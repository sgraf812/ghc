{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fprof-auto #-}
--
-- Copyright (c) 2014 Joachim Breitner
--

module CallArity.Analysis where

#include "HsVersions.h"

import CallArity.Types
import CallArity.FrameworkBuilder

import BasicTypes
import Class
import Coercion ( Coercion, coVarsOfCo )
import CoreSyn
import CoreUtils ( exprIsTrivial )
import DataCon
import DynFlags      ( DynFlags, gopt, GeneralFlag(Opt_DmdTxDictSel) )
import FamInstEnv
import Id
import Maybes ( expectJust, fromMaybe, isJust )
import MkCore
import Outputable
import TyCon ( isDataProductTyCon_maybe, tyConSingleDataCon_maybe )
import UniqFM
import UnVarGraph
import Usage
import Util
import Var ( isId, isTyVar )
import VarEnv
import VarSet
import WwLib ( findTypeShape )

import Control.Arrow ( first, second )
import Control.Monad ( forM )
import qualified Data.Set as Set
import Data.Tree


{-
%************************************************************************
%*                                                                      *
              Call Arity Analyis
%*                                                                      *
%************************************************************************

Note [Notes are out of date]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

While the general concept of the Co-Call Analysis still holds, much has
changed at isn't yet on par with the implementation.

Note [Call Arity: The goal]
~~~~~~~~~~~~~~~~~~~~~~~~~~~

The goal of this analysis is to find out if we can eta-expand a local function,
based on how it is being called. The motivating example is this code,
which comes up when we implement foldl using foldr, and do list fusion:

    let go = \x -> let d = case ... of
                              False -> go (x+1)
                              True  -> id
                   in \z -> d (x + z)
    in go 1 0

If we do not eta-expand `go` to have arity 2, we are going to allocate a lot of
partial function applications, which would be bad.

The function `go` has a type of arity two, but only one lambda is manifest.
Furthermore, an analysis that only looks at the RHS of go cannot be sufficient
to eta-expand go: If `go` is ever called with one argument (and the result used
multiple times), we would be doing the work in `...` multiple times.

So `callArityAnalProgram` looks at the whole let expression to figure out if
all calls are nice, i.e. have a high enough arity. It then stores the result in
the `calledArity` field of the `IdInfo` of `go`, which the next simplifier
phase will eta-expand.

The specification of the `calledArity` field is:

    No work will be lost if you eta-expand me to the arity in `calledArity`.

What we want to know for a variable
-----------------------------------

For every let-bound variable we'd like to know:
  1. A lower bound on the arity of all calls to the variable, and
  2. whether the variable is being called at most once or possible multiple
     times.

It is always ok to lower the arity, or pretend that there are multiple calls.
In particular, "Minimum arity 0 and possible called multiple times" is always
correct.


What we want to know from an expression
---------------------------------------

In order to obtain that information for variables, we analyize expression and
obtain bits of information:

 I.  The arity analysis:
     For every variable, whether it is absent, or called,
     and if called, which what arity.

 II. The Co-Called analysis:
     For every two variables, whether there is a possibility that bothUsageType are being
     called.
     We obtain as a special case: For every variables, whether there is a
     possibility that it is being called twice.

For efficiency reasons, we gather this information only for a set of
*interesting variables*, to avoid spending time on, e.g., variables from pattern matches.

The two analysis are not completely independent, as a higher arity can improve
the information about what variables are being called once or multiple times.

Note [Analysis I: The arity analyis]
------------------------------------

The arity analysis is quite straight forward: The information about an
expression is an
    VarEnv Arity
where absent variables are bound to Nothing and otherwise to a lower bound to
their arity.

When we analyize an expression, we analyize it with a given context arity.
Lambdas decrease and applications increase the incoming arity. Analysizing a
variable will put that arity in the environment. In lets or cases all the
results from the various subexpressions are lubed, which takes the point-wise
minimum (considering Nothing an infinity).


Note [Analysis II: The Co-Called analysis]
------------------------------------------

The second part is more sophisticated. For reasons explained below, it is not
sufficient to simply know how often an expression evalutes a variable. Instead
we need to know which variables are possibly called together.

The data structure here is an undirected graph of variables, which is provided
by the abstract
    UnVarGraph

It is safe to return a larger graph, i.e. one with more edges. The worst case
(i.e. the least useful and always correct result) is the complete graph on all
free variables, which means that anything can be called together with anything
(including itself).

Notation for the following:
C(e)  is the co-called result for e.
G₁∪G₂ is the union of two graphs
fv    is the set of free variables (conveniently the domain of the arity analysis result)
S₁×S₂ is the complete bipartite graph { {a,b} | a ∈ S₁, b ∈ S₂ }
S²    is the complete graph on the set of variables S, S² = S×S
C'(e) is a variant for bound expression:
      If e is called at most once, or it is and stays a thunk (after the analysis),
      it is simply C(e). Otherwise, the expression can be called multiple times
      and we return (fv e)²

The interesting cases of the analysis:
 * Var v:
   No other variables are being called.
   Return {} (the empty graph)
 * Lambda v e, under arity 0:
   This means that e can be evaluated many times and we cannot get
   any useful co-call information.
   Return (fv e)²
 * Case alternatives alt₁,alt₂,...:
   Only one can be execuded, so
   Return (alt₁ ∪ alt₂ ∪...)
 * App e₁ e₂ (and analogously Case scrut alts), with non-trivial e₂:
   We get the results from bothUsageType sides, with the argument evaluated at most once.
   Additionally, anything called by e₁ can possibly be called with anything
   from e₂.
   Return: C(e₁) ∪ C(e₂) ∪ (fv e₁) × (fv e₂)
 * App e₁ x:
   As this is already in A-normal form, CorePrep will not separately lambda
   bind (and hence share) x. So we conservatively assume multiple calls to x here
   Return: C(e₁) ∪ (fv e₁) × {x} ∪ {(x,x)}
 * Let v = rhs in body:
   In addition to the results from the subexpressions, add all co-calls from
   everything that the body calls together with v to everthing that is called
   by v.
   Return: C'(rhs) ∪ C(body) ∪ (fv rhs) × {v'| {v,v'} ∈ C(body)}
 * Letrec v₁ = rhs₁ ... vₙ = rhsₙ in body
   Tricky.
   We assume that it is really mutually recursive, i.e. that every variable
   calls one of the others, and that this is strongly connected (otherwise we
   return an over-approximation, so that's ok), see note [Recursion and fixpointing].

   Let V = {v₁,...vₙ}.
   Assume that the vs have been analysed with an incoming demand and
   cardinality consistent with the final result (this is the fixed-pointing).
   Again we can use the results from all subexpressions.
   In addition, for every variable vᵢ, we need to find out what it is called
   with (call this set Sᵢ). There are two cases:
    * If vᵢ is a function, we need to go through all right-hand-sides and bodies,
      and collect every variable that is called together with any variable from V:
      Sᵢ = {v' | j ∈ {1,...,n},      {v',vⱼ} ∈ C'(rhs₁) ∪ ... ∪ C'(rhsₙ) ∪ C(body) }
    * If vᵢ is a thunk, then its rhs is evaluated only once, so we need to
      exclude it from this set:
      Sᵢ = {v' | j ∈ {1,...,n}, j≠i, {v',vⱼ} ∈ C'(rhs₁) ∪ ... ∪ C'(rhsₙ) ∪ C(body) }
   Finally, combine all this:
   Return: C(body) ∪
           C'(rhs₁) ∪ ... ∪ C'(rhsₙ) ∪
           (fv rhs₁) × S₁) ∪ ... ∪ (fv rhsₙ) × Sₙ)

Using the result: Eta-Expansion
-------------------------------

We use the result of these two analyses to decide whether we can eta-expand the
rhs of a let-bound variable.

If the variable is already a function (exprIsCheap), and all calls to the
variables have a higher arity than the current manifest arity (i.e. the number
of lambdas), expand.

If the variable is a thunk we must be careful: Eta-Expansion will prevent
sharing of work, so this is only safe if there is at most one call to the
function. Therefore, we check whether {v,v} ∈ G.

    Example:

        let n = case .. of .. -- A thunk!
        in n 0 + n 1

    vs.

        let n = case .. of ..
        in case .. of T -> n 0
                      F -> n 1

    We are only allowed to eta-expand `n` if it is going to be called at most
    once in the body of the outer let. So we need to know, for each variable
    individually, that it is going to be called at most once.


Why the co-call graph?
----------------------

Why is it not sufficient to simply remember which variables are called once and
which are called multiple times? It would be in the previous example, but consider

        let n = case .. of ..
        in case .. of
            True -> let go = \y -> case .. of
                                     True -> go (y + n 1)
                                     False > n
                    in go 1
            False -> n

vs.

        let n = case .. of ..
        in case .. of
            True -> let go = \y -> case .. of
                                     True -> go (y+1)
                                     False > n
                    in go 1
            False -> n

In bothUsageType cases, the body and the rhs of the inner let call n at most once.
But only in the second case that holds for the whole expression! The
crucial difference is that in the first case, the rhs of `go` can call
*both* `go` and `n`, and hence can call `n` multiple times as it recurses,
while in the second case find out that `go` and `n` are not called together.


Why co-call information for functions?
--------------------------------------

Although for eta-expansion we need the information only for thunks, we still
need to know whether functions are being called once or multiple times, and
together with what other functions.

    Example:

        let n = case .. of ..
            f x = n (x+1)
        in f 1 + f 2

    vs.

        let n = case .. of ..
            f x = n (x+1)
        in case .. of T -> f 0
                      F -> f 1

    Here, the body of f calls n exactly once, but f itself is being called
    multiple times, so eta-expansion is not allowed.


Note [Analysis type signature]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The work-hourse of the analysis is the function `callArityAnal`, with the
following type:

    type UsageType = (UnVarGraph, VarEnv Arity)
    callArityAnal ::
        Arity ->  -- The arity this expression is called with
        VarSet -> -- The set of interesting variables
        CoreExpr ->  -- The expression to analyse
        (UsageType, CoreExpr)

and the following specification:

  ((coCalls, callArityEnv), expr') = callArityEnv arity interestingIds expr

                            <=>

  Assume the expression `expr` is being passed `arity` arguments. Then it holds that
    * The domain of `callArityEnv` is a subset of `interestingIds`.
    * Any variable from `interestingIds` that is not mentioned in the `callArityEnv`
      is absent, i.e. not called at all.
    * Every call from `expr` to a variable bound to n in `callArityEnv` has at
      least n value arguments.
    * For two interesting variables `v1` and `v2`, they are not adjacent in `coCalls`,
      then in no execution of `expr` bothUsageType are being called.
  Furthermore, expr' is expr with the callArity field of the `IdInfo` updated.


Note [Which variables are interesting]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The analysis would quickly become prohibitive expensive if we would analyse all
variables; for most variables we simply do not care about how often they are
called, i.e. variables bound in a pattern match. So interesting are variables that are
 * top-level or let bound
 * and possibly functions (typeArity > 0)

Note [Taking boring variables into account]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If we decide that the variable bound in `let x = e1 in e2` is not interesting,
the analysis of `e2` will not report anything about `x`. To ensure that
`registerBindingGroup` does still do the right thing we have to take that into account
everytime we look up up `x` in the analysis result of `e2`.
  * Instead of calling lookupUsage, we return (0, True), indicating
    that this variable might be called many times with no arguments.
  * Instead of checking `calledWith x`, we assume that everything can be called
    with it.
  * In the recursive case, when calclulating the `cross_calls`, if there is
    any boring variable in the recursive group, we ignore all co-call-results
    and directly go to a very conservative assumption.

The last point has the nice side effect that the relatively expensive
integration of co-call results in a recursive groups is often skipped. This
helped to avoid the compile time blowup in some real-world code with large
recursive groups (#10293).

Note [Recursion and fixpointing]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For a mutually recursive let, we begin by
 1. analysing the body, using the same incoming arity as for the whole expression.
 2. Then we iterate, memoizing for each of the bound variables the last
    analysis call, i.e. incoming arity, whether it is called once, and the UsageType.
 3. We combine the analysis result from the body and the memoized results for
    the arguments (if already present).
 4. For each variable, we find out the incoming arity and whether it is called
    once, based on the the current analysis result. If this differs from the
    memoized results, we re-analyse the rhs and update the memoized table.
 5. If nothing had to be reanalyzed, we are done.
    Otherwise, repeat from step 3.


Note [Thunks in recursive groups]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We never eta-expand a thunk in a recursive group, on the grounds that if it is
part of a recursive group, then it will be called multipe times.

This is not necessarily true, e.g.  it would be safe to eta-expand t2 (but not
t1) in the following code:

  let go x = t1
      t1 = if ... then t2 else ...
      t2 = if ... then go 1 else ...
  in go 0

Detecting this would require finding out what variables are only ever called
from thunks. While this is certainly possible, we yet have to see this to be
relevant in the wild.


Note [Analysing top-level binds]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We can eta-expand top-level-binds if they are not exported, as we see all calls
to them. The plan is as follows: Treat the top-level binds as nested lets around
a body representing “all external calls”, which returns a pessimistic
UsageType (the co-call graph is the complete graph, all arityies 0).

Note [What is a thunk]
~~~~~~~~~~~~~~~~~~~~~~

Originally, everything that is not in WHNF (`exprIsWHNF`) is considered a
thunk, not eta-expanded, to avoid losing any sharing. This is also how the
published papers on Call Arity describe it.

In practice, there are thunks that do a just little work, such as
pattern-matching on a variable, and the benefits of eta-expansion likely
oughtweigh the cost of doing that repeatedly. Therefore, this implementation of
Call Arity considers everything that is not cheap (`exprIsCheap`) as a thunk.
-}

data AnalEnv
  = AE
  { ae_dflags :: DynFlags
  -- ^ Configuration flags. Of particular interest to this analysis:
  --
  --     - `Opt_DmdTxDictSel`: Control analysis of dictionary selectors.
  --
  , ae_sigs :: VarEnv (SingleUse -> TransferFunction UsageType)
  -- ^ 'TransferFunction's of visible local let-bound identifiers. It is crucial
  -- that only the 'UsageSig' component is used, as the usage on free vars might
  -- be unstable and thus too optimistic.
  , ae_fam_envs :: FamInstEnvs
  -- ^ Needed for 'findTypeShape' to resolve type/data families.
  , ae_need_sig_annotation :: VarSet
  -- ^ `Id`s which need to be annotated with a signature, e.g. because
  -- they are visible beyond this module. These are probably top-level
  -- ids only, including exports and mentions in RULEs.
  , ae_predicted_nodes :: Tree Int
  -- ^ A prediction of how many `FrameworkNode`s need to be allocated for
  -- the expression to be analyzed. We need these for allocating
  -- `FrameworkNode`s in a particular order that guarantees fast
  -- stabilization.
  }

initialAnalEnv :: DynFlags -> FamInstEnvs -> VarSet -> Tree Int -> AnalEnv
initialAnalEnv dflags fam_envs need_sigs predicted_nodes
  = AE
  { ae_dflags = dflags
  , ae_sigs = emptyVarEnv
  , ae_fam_envs = fam_envs
  , ae_need_sig_annotation = need_sigs
  , ae_predicted_nodes = predicted_nodes
  }

descend :: Int -> AnalEnv -> AnalEnv
descend n env 
  = env { ae_predicted_nodes = subForest (ae_predicted_nodes env) !! n }

predictSizeOfLetBody :: AnalEnv -> Int
-- The body is always the first child
predictSizeOfLetBody = rootLabel . ae_predicted_nodes . descend 0 

extendAnalEnv 
  :: AnalEnv 
  -> Id 
  -> (SingleUse -> TransferFunction UsageType) 
  -> AnalEnv
extendAnalEnv env id node 
  = env { ae_sigs = extendVarEnv (ae_sigs env) id node }

-- | See Note [Analysing top-level-binds]
-- `programToExpr` returns a pair of externally visible top-level `Id`s
-- (including at least exports and mentions in RULEs) and a nested
-- `let` expression to be analysed by `callArityRHS`.
--
-- Represents the fact that a `CoreProgram` is like a sequence of
-- nested lets, where the external visible ids are returned in the inner-most let
-- as a tuple. As a result, all exported identifiers are handled as called
-- with each other, with `topUsage`.
programToExpr 
  :: CoreProgram 
  -> (VarSet, CoreExpr)
programToExpr = first (\it -> pprTrace "programToExpr" (ppr (sizeVarSet it)) it) . impl []
  where
    impl exposed []
      = (mkVarSet exposed, mkBigCoreVarTup exposed)
    impl exposed (bind:prog)
      = second (Let bind) (impl (exposed_ids bind ++ exposed) prog)
    -- We are too conservative here, but we need *at least*  
    -- 
    --   * exported `Id`s (`isExportedId`)
    --   * `Id`s mentioned in RULEs of this module
    --
    -- I'm not sure it's enough to just look into RULEs associated
    -- with any of the binders, so we just blindly assume all top-level
    -- `Id`s as exported (as does the demand analyzer).
    exposed_ids bind = bindersOf bind

-- | The left inverse to `programToExpr`: `exprToProgram . snd . programToExpr = id \@CoreProgram`
exprToProgram :: CoreExpr -> CoreProgram
exprToProgram (Let bind e) = bind : exprToProgram e
exprToProgram _ = []

-- Main entry point
callArityAnalProgram 
  :: DynFlags 
  -> FamInstEnvs 
  -> CoreProgram 
  -> IO CoreProgram
callArityAnalProgram dflags fam_envs
  = return 
  . (\it -> pprTrace "callArity:end" (ppr (length it)) it) 
  . exprToProgram 
  . uncurry (callArityRHS dflags fam_envs) 
  . programToExpr 
  . (\it -> pprTrace "callArity:begin" (ppr (length it)) it)
  -- . (\prog -> pprTrace "CallArity:Program" (ppr prog) prog)

callArityRHS :: DynFlags -> FamInstEnvs -> VarSet -> CoreExpr -> CoreExpr
callArityRHS dflags fam_envs need_sigs e
  = ASSERT2( isEmptyUnVarSet (domType ut), text "Free vars in UsageType:" $$ ppr ut ) e'
  where
    env = initialAnalEnv dflags fam_envs need_sigs (predictAllocatedNodes e)
    (ut, e') = buildAndRun (callArityExpr env e) topSingleUse

-- | The main analysis function. See Note [Analysis type signature]
callArityExpr
  :: AnalEnv
  -> CoreExpr
  -> FrameworkBuilder (SingleUse -> TransferFunction AnalResult)

callArityExprTrivial
  :: UsageType
  -> CoreExpr
  -> FrameworkBuilder (SingleUse -> TransferFunction AnalResult)
callArityExprTrivial ut e
  = return (const (return (ut, e)))

callArityExprMap
  :: AnalEnv
  -> (CoreExpr -> a)
  -> CoreExpr
  -> FrameworkBuilder (SingleUse -> TransferFunction (UsageType, a)) -- @a@ instead of @CoreExpr@
callArityExprMap env f e
  = transfer' <$> callArityExpr env e
  where
    transfer' transfer use = do
      (ut, e') <- transfer use
      return (ut, f e')

callArityExpr _ e@(Lit _)
  = callArityExprTrivial emptyUsageType e 
callArityExpr _ e@(Type _)
  = callArityExprTrivial emptyUsageType e

callArityExpr _ e@(Coercion co)
  = callArityExprTrivial (coercionUsageType co) e

callArityExpr env (Tick t e)
  = callArityExprMap env (Tick t) e

callArityExpr env (Cast e co)
  = transfer' <$> callArityExpr env e
  where
    transfer' transfer use = do
      (ut, e') <- transfer use
      -- like callArityExprMap, but we also have to combine with the UsageType
      -- of the coercion.
      return (ut `bothUsageType` coercionUsageType co, Cast e' co)

callArityExpr env e@(Var id) = return transfer
  where
    transfer use
      | Just transfer_callee <- lookupVarEnv (ae_sigs env) id
      -- A local let-binding, e.g. a binding from this module.
      = do
        ut_callee <- transfer_callee use
        -- It is crucial that we only use ut_args here, as every other field
        -- might be unstable and thus too optimistic.
        --pprTrace "callArityExpr:LocalId" (ppr id <+> ppr use <+> ppr (ut_args ut_callee)) (return ())
        return ((unitUsageType id use) { ut_args = ut_args ut_callee }, e)

      | isLocalId id
      -- A LocalId not present in @nodes@, e.g. a lambda or case-bound variable.
      -- We are only second-order, so we don't model signatures for parameters!
      -- Their usage is interesting to note nonetheless for annotating lambda
      -- binders and scrutinees.
      = --pprTrace "callArityExpr:OtherId" (ppr id <+> ppr use) $
        return (unitUsageType id use, e)

      -- The other cases handle global ids
      | Just dc <- ASSERT( isGlobalId id ) (isDataConWorkId_maybe id)
      -- Some data constructor, on which we can try to unleash product use
      -- as a `UsageSig`.
      = --pprTrace "callArityExpr:DataCon" (ppr id <+> ppr use <+> ppr (dataConUsageSig dc use)) $
        return (emptyUsageType { ut_args = dataConUsageSig dc use }, e)

      | gopt Opt_DmdTxDictSel (ae_dflags env)
      , Just clazz <- isClassOpId_maybe id
      -- A dictionary component selector
      = --pprTrace "callArityExpr:DictSel" (ppr id <+> ppr use <+> ppr (dictSelUsageSig id clazz use)) $
        return (emptyUsageType { ut_args = dictSelUsageSig id clazz use }, e)

      | otherwise
      -- A global id from another module which has a usage signature.
      -- We don't need to track the id itself, though.
      = --pprTrace "callArityExpr:GlobalId" (ppr id <+> ppr (idArity id) <+> ppr use <+> ppr (globalIdUsageSig id use) <+> ppr (idStrictness id) <+> ppr (idDetails id)) $
        return (emptyUsageType { ut_args = globalIdUsageSig id use }, e)

callArityExpr env (Lam id body)
  | isTyVar id
  = callArityExprMap env (Lam id) body
  | otherwise
  = do
    transfer_body <- callArityExpr env body
    return $ \use ->
      case fromMaybe topUsage (peelCallUse use) of -- Get at the relative @Usage@ of the body
        Absent -> do
          let id' = id `setIdCallArity` Absent
          return (emptyUsageType, Lam id' body)
        u@(Used multi body_use) -> do
          (ut_body, body') <- transfer_body body_use
          let (ut_body', usage_id) = findBndrUsage NonRecursive (ae_fam_envs env) ut_body id
          let id' = applyWhen (multi == Once) (flip setIdOneShotInfo OneShotLam)
                  . flip setIdCallArity usage_id
                  $ id
          -- Free vars are manified, closed vars are not. The usage of the current
          -- argument `id` is *not* manified.
          let ut = modifyArgs (consUsageSig usage_id)
                 . multiplyUsages multi
                 $ ut_body'
          --pprTrace "callArityExpr:Lam" (vcat [text "id:" <+> ppr id, text "relative body usage:" <+> ppr u, text "id usage:" <+> ppr usage_id, text "usage sig:" <+> ppr (ut_args ut)]) (return ())
          return (ut, Lam id' body')

callArityExpr env (App f (Type t)) 
  = callArityExprMap (descend 0 env) (flip App (Type t)) f
callArityExpr env (App f a) = do
  transfer_f <- callArityExpr (descend 0 env) f
  transfer_a <- callArityExpr (descend 1 env) a
  return $ \result_use -> do
    (ut_f, f') <- transfer_f (mkCallUse Once result_use)
    --pprTrace "App:f'" (ppr f') $ return ()
    -- peel off one argument from the type
    let (arg_usage, ut_f') = peelArgUsage ut_f
    case considerThunkSharing a arg_usage of
      Absent -> return (ut_f', App f' a)
      Used m arg_use -> do
          -- `m` will be `Once` most of the time (see `considerThunkSharing`),
          -- so that all work before the lambda is uncovered will be shared 
          -- (call-by-need!). This is the same argument as for let-bound 
          -- right hand sides.
          -- We could also use the multiplicity in the same way we do for
          -- let-bindings: An argument only used once does not need to be
          -- memoized.
          (ut_a, a') <- first (multiplyUsages m) <$> transfer_a arg_use
          --pprTrace "App:a'" (text "arg_use:" <+> ppr arg_use <+> ppr (ut_a, a')) $ return ()
          return (ut_f' `bothUsageType` ut_a, App f' a')

callArityExpr env (Case scrut case_bndr ty alts) = do
  transfer_scrut <- callArityExpr (descend 0 env) scrut
  -- We zip the index of the child in the ae_predicted_nodes tree
  transfer_alts <- forM (zip [1..] alts) $ \(n, alt) -> 
    analyseCaseAlternative (descend n env) case_bndr alt
  return $ \use -> do
    (ut_alts, alts', scrut_uses) <- unzip3 <$> mapM ($ use) transfer_alts
    let ut_alt = lubUsageTypes ut_alts
    let case_bndr' = setIdCallArity case_bndr (lookupUsage NonRecursive ut_alt case_bndr)
    let ut_alt' = delUsageType case_bndr ut_alt
    let scrut_use = propagateProductUse alts' scrut_uses
    (ut_scrut, scrut') <- transfer_scrut scrut_use
    let ut = ut_alt' `bothUsageType` ut_scrut
    --pprTrace "Case" (vcat [text "ut_scrut:" <+> ppr ut_scrut, text "ut_alts:" <+> ppr ut_alts, text "ut:" <+> ppr ut]) (return ())
    return (ut, Case scrut' case_bndr' ty alts')

callArityExpr env (Let bind e) 
  = registerTransferFunction register >>= deref_node
  where
    deref_node node = return $ \use -> do
      (ut, let') <- dependOnWithDefault (botUsageType, Let bind e) (node, use)
      --pprTrace "Let" (ppr (ut, let')) $ return ()
      return (delUsageTypes (bindersOf bind) ut, let')
    register node = do
      let initial_binds = flattenBinds [bind]
      let ids = map fst initial_binds
      -- We retain nodes we need for the body, so that they have lower
      -- priority than the bindings.
      retained <- retainNodes (predictSizeOfLetBody env)
      (env', rhs_env) <- registerBindingGroup env initial_binds
      freeRetainedNodes retained
      let lookup_node id =
            expectJust ": the RHS of id wasn't registered" (lookupVarEnv rhs_env id)
      let transferred_bind b@(id, rhs) = (id, (rhs, lookup_node id))
      -- Ideally we'd want the body to have a lower priority than the RHSs,
      -- but we need to access env' with the new sigs in the body, so we
      -- can't register it earlier.
      transfer_body <- callArityExpr (descend 0 env') e
      let rec_flag = recFlagOf bind
      let transfer :: SingleUse -> TransferFunction AnalResult
          transfer = monotonize node $ \use -> do
            --use <- pprTrace "Rec:begin" (ppr ids) $ return use
            (ut_body, e') <- transfer_body use
            (ut_usage, old_binds) <- case rec_flag of
              NonRecursive -> 
                -- We don't need to dependOn ourselves here, because only the let body can't
                -- call id.
                return (ut_body, initial_binds)
              Recursive -> do
                -- This is the actual fixed-point iteration: we depend on usage
                -- results from the previous iteration, defaulting to just the body.
                (ut_usage, Let (Rec old_binds) _) <- dependOnWithDefault (ut_body, Let bind e) (node, use)
                return (ut_usage, old_binds)
            let transferred_binds = map transferred_bind old_binds
            (ut, binds') <- unleashLet env rec_flag transferred_binds ut_usage ut_body
            --ut <- pprTrace "Rec:end" (ppr ids) $ return ut
            case rec_flag of
              NonRecursive 
                | [(id', rhs')] <- binds'
                -> return (ut, Let (NonRec id' rhs') e')
              _ -> return (ut, Let (Rec binds') e')
      return (node, (transfer, changeDetectorAnalResult node))

coercionUsageType :: Coercion -> UsageType
coercionUsageType co = multiplyUsages Many ut
  where
    ut = emptyUsageType { ut_uses = mapVarEnv (const topSingleUse) (coVarsOfCo co) }

-- | Consider the expression
--
-- @
--     case (,) (f x) (g y) of
--       (,) a _ -> a
-- @
--
-- The pair has product use @U(w*U,A)@, but how do we propagate that information?
--
-- By the time we hit the actual product constructor identifier in the application,
-- we'll have an incoming use of @C^1(C^1(w*U(U,A)))@. What we need is a
-- compatible `UsageSig`, which is @w*U -> A -> .@ in this case.
--
-- `dataConUsageSig` does exactly this: First peel off one-shot calls according
-- to the constructors `idArity`, then peel off the product use to get at the
-- usage on its components.
dataConUsageSig :: DataCon -> SingleUse -> UsageSig
dataConUsageSig dc use = fromMaybe topUsageSig sig_maybe
  where
    arity = dataConRepArity dc
    peelSingleShotCalls 0 use = Just use
    peelSingleShotCalls n call
      | Just Absent <- peelCallUse call
      = Just botSingleUse -- (,) x `seq` ...: Nothing unleashed in this case
      | Just (Used Once use) <- peelCallUse call
      = peelSingleShotCalls (n - 1) use
      | otherwise
      = Nothing
    sig_maybe = do
      product_use <- peelSingleShotCalls arity use
      -- We need to consider strict constructors, where a head use will also
      -- use its components (e.g. I#)
      component_usages <- peelProductUse arity (addDataConStrictness dc product_use)
      return (usageSigFromUsages component_usages)

dictSelUsageSig :: Id -> Class -> SingleUse -> UsageSig
dictSelUsageSig id clazz use
  | Used _ dict_single_call_use <- fst . unconsUsageSig . idArgUsage $ id
  , Just dc <- tyConSingleDataCon_maybe (classTyCon clazz)
  , let dict_length = idArity (dataConWorkId dc)
  , Just comps <- peelProductUse dict_length dict_single_call_use
  = case peelCallUse use of -- The outer call is the selector. The inner use is on the actual method!
      Nothing -> topUsageSig -- weird
      Just Absent -> botUsageSig
      Just (Used Once method_use) -> specializeDictSig comps method_use
      Just (Used Many method_use) -> manifyUsageSig (specializeDictSig comps method_use)
  | otherwise
  = topUsageSig

specializeDictSig :: [Usage] -> SingleUse -> UsageSig
specializeDictSig comps method_use = consUsageSig dict_usage topUsageSig
  where
    dict_usage = Used Once (mkProductUse (map replace_usage comps))
    replace_usage old
      | old == Absent = old
      | otherwise = Used Once method_use -- This is the selector for the method we used!

globalIdUsageSig :: Id -> SingleUse -> UsageSig
globalIdUsageSig id use
  | use <= no_call -- @f x `seq` ...@ for a GlobalId `f` with arity > 1
  = botUsageSig
  | use <= single_call
  = arg_usage
  | otherwise
  = --pprTrace "many" (ppr arg_usage <+> ppr (idStrictness id) <+> ppr (manifyUsageSig arg_usage)) $ 
    manifyUsageSig arg_usage
  where
    (<=) = leqSingleUse
    arity = idArity id
    mk_one_shot = mkCallUse Once
    no_call = iterate mk_one_shot botSingleUse !! max 0 (arity - 1)
    single_call = iterate mk_one_shot topSingleUse !! arity
    arg_usage = idArgUsage id

-- | Evaluation of a non-trivial RHS of a let-binding or argument 
-- is shared (call-by-need!). GHC however doesn't allocate a new thunk
-- if it finds the expression to bind to be trivial (`exprIsTrivial`).
-- This makes sure we share usage only if this is not the case.
considerThunkSharing :: CoreExpr -> Usage -> Usage
considerThunkSharing e
  | exprIsTrivial e = id
  | otherwise = oneifyUsage

analyseCaseAlternative
  :: AnalEnv
  -> Id
  -> Alt CoreBndr
  -> FrameworkBuilder (SingleUse -> TransferFunction (UsageType, Alt CoreBndr, SingleUse))
analyseCaseAlternative env case_bndr (dc, alt_bndrs, e)
  = transfer <$> callArityExpr env e
  where
    transfer transfer_alt use = do
      let fam_envs = ae_fam_envs env
      (ut_alt, e') <- transfer_alt use
      let (ut_alt', alt_bndr_usages) = findBndrsUsages NonRecursive fam_envs ut_alt alt_bndrs
      let (_, case_bndr_usage) = findBndrUsage NonRecursive fam_envs ut_alt case_bndr
      -- We have to combine usages of alts_bndrs with that of case_bndr.
      -- Usage info flows from case_bndr to alt_bndrs, but not the other way
      -- around! This means that we later on annotate case_bndr solely based
      -- on how its @Id@ was used, not on how the components were used.
      let alt_bndr_usages' = addCaseBndrUsage case_bndr_usage alt_bndr_usages
      let alt_bndrs' = setBndrsUsageInfo alt_bndrs alt_bndr_usages
      let product_use = mkProductUse alt_bndr_usages'
      -- product_use doesn't yet take into account strictness annotations of the
      -- constructor. That's to be done when we finally match on dc.
      return (ut_alt', (dc, alt_bndrs', e'), product_use)

findBndrUsage :: RecFlag -> FamInstEnvs -> UsageType -> Id -> (UsageType, Usage)
findBndrUsage rec_flag fam_envs ut id
  = (delUsageType id ut, usage')
  where
    usage = lookupUsage rec_flag ut id
    -- See Note [Trimming a demand to a type] in Demand.hs
    shape = findTypeShape fam_envs (idType id)
    usage' = trimUsage shape usage

findBndrsUsages :: RecFlag -> FamInstEnvs -> UsageType -> [Var] -> (UsageType, [Usage])
findBndrsUsages rec_flag fam_envs ut = foldr step (ut, [])
  where
    step b (ut, usages)
      | isId b
      , (ut', usage) <- findBndrUsage rec_flag fam_envs ut b
      = (ut', usage:usages)
      | otherwise
      = (ut, usages)

addCaseBndrUsage :: Usage -> [Usage] -> [Usage]
addCaseBndrUsage Absent alt_bndr_usages = alt_bndr_usages
addCaseBndrUsage (Used _ use) alt_bndr_usages
  | Just case_comp_usages <- peelProductUse (length alt_bndr_usages) use
  = zipWith bothUsage case_comp_usages alt_bndr_usages
  | otherwise
  = topUsage <$ alt_bndr_usages

setBndrsUsageInfo :: [Var] -> [Usage] -> [Var]
setBndrsUsageInfo [] [] = []
setBndrsUsageInfo (b:bndrs) (usage:usages)
  | isId b
  = --pprTrace "setBndrInfo" (ppr b <+> ppr usage) 
    (setIdCallArity b usage) : setBndrsUsageInfo bndrs usages
setBndrsUsageInfo (b:bndrs) usages
  = b : setBndrsUsageInfo bndrs usages
setBndrsUsageInfo _ usages
  = pprPanic "No Ids, but a Usage left" (ppr usages)

propagateProductUse
  :: [Alt CoreBndr]
  -> [SingleUse]
  -> SingleUse
propagateProductUse alts scrut_uses
  -- Only one alternative with a product constructor
  | [(DataAlt dc, _, _)] <- alts
  , [scrut_use] <- scrut_uses
  , let tycon = dataConTyCon dc
  -- Don't include newtypes, as they aren't really constructors introducing
  -- indirections.
  , isJust (isDataProductTyCon_maybe tycon)
  -- This is a good place to make sure we don't construct an infinitely deep
  -- use, which can happen when analysing e.g. lazy streams.
  -- Also see Note [Demand on scrutinee of a product case] in DmdAnal.hs.
  = addDataConStrictness dc (boundDepth 6 scrut_use)

  | otherwise
  -- We *could* lub the uses from the different branches, but there's not much
  -- to be won there, except for maybe head strictness.
  = topSingleUse

addDataConStrictness :: DataCon -> SingleUse -> SingleUse
-- See Note [Add demands for strict constructors] in DmdAnal.hs
addDataConStrictness dc
  = maybe topSingleUse (mkProductUse . add_component_strictness) 
  . peelProductUse arity
  where
    add_component_strictness :: [Usage] -> [Usage]
    add_component_strictness = zipWith add strs

    strs = dataConRepStrictness dc
    arity = length strs

    add _ Absent = Absent -- See the note; We want to eliminate these in WW.
    add str usage@(Used _ _)
      | isMarkedStrict str = usage `bothUsage` u'1HU -- head usage imposed by `seq`
      | otherwise = usage

recFlagOf :: CoreBind -> RecFlag
recFlagOf Rec{} = Recursive
recFlagOf NonRec{} = NonRecursive

registerBindingGroup
  :: AnalEnv
  -> [(Id, CoreExpr)]
  -> FrameworkBuilder (AnalEnv, VarEnv (SingleUse -> TransferFunction AnalResult))
registerBindingGroup env = go env emptyVarEnv . zip [1..] -- `zip` for `descend`ing
  where
    go env nodes [] = return (env, nodes)
    go env nodes ((n, (id, rhs)):binds) =
      registerTransferFunction $ \node ->
        registerTransferFunction $ \args_node -> do
          let deref_node node def_e use = dependOnWithDefault (botUsageType, def_e) (node, use)
          let expr_forced_error = error "Expression component may not be used"
          (env', nodes') <- go
            (extendAnalEnv env id (fmap fst . deref_node args_node expr_forced_error))
            (extendVarEnv nodes id (deref_node node rhs))
            binds
          transfer <- callArityExpr (descend n env') rhs
          let transfer' = monotonize node $ \use -> do
                --use <- pprTrace "RHS:begin" (ppr id <+> text "::" <+> ppr use) $ return use
                ret@(ut, rhs') <- transfer use 
                --ret <- pprTrace "RHS:end" (vcat [ppr id <+> text "::" <+> ppr use, ppr (ut_args ut_rhs)]) $ return ret
                return ret
          let transfer_args use = do
                --use <- pprTrace "args:begin" (ppr id <+> text "::" <+> ppr use) $ return use
                (ut, _) <- dependOnWithDefault (botUsageType, undefined) (node, use)
                --ut <- pprTrace "args:end" (vcat [ppr id <+> text "::" <+> ppr use, ppr (ut_args ut)]) $ return ut
                return (ut, expr_forced_error)
          let ret = (env', nodes') -- What we return from 'registerBindingGroup'
          let full = (transfer', changeDetectorAnalResult node) -- What we register for @node@
          let args = (transfer_args, changeDetectorUsageType) -- What we register for @arg_node@
          return ((ret, full), args) -- registerTransferFunction  will peel `snd`s away for registration

changeDetectorUsageType :: ChangeDetector
changeDetectorUsageType changed_refs (old, _) (new, _) =
  -- It's crucial that we don't have to check the annotated expressions.
  ASSERT2( old_sig `leqUsageSig` new_sig, text "CallArity.changeDetector: usage sig not monotone")
  pprTrace "usage sig" empty (old_sig /= new_sig) ||
  ASSERT2( sizeUFM old_uses <= sizeUFM new_uses, text "CallArity.changeDetector: uses not monotone")
  pprTrace "uses count" (ppr (sizeUFM old_uses) <+> ppr (sizeUFM new_uses)) (sizeUFM old_uses /= sizeUFM new_uses) ||
  pprTrace "uses" empty (old_uses /= new_uses) ||
  ASSERT2( edgeCount old_cocalled <= edgeCount new_cocalled, text "CallArity.changeDetector: edgeCount not monotone")
  pprTrace "edgeCount" (ppr (edgeCount old_cocalled) <+> ppr (edgeCount new_cocalled)) (edgeCount old_cocalled /= edgeCount new_cocalled)
  where
    old_sig = ut_args old
    new_sig = ut_args new
    old_uses = ut_uses old
    new_uses = ut_uses new
    old_cocalled = ut_cocalled old
    new_cocalled = ut_cocalled new
    leqUsageSig a b = lubUsageSig a b == b

changeDetectorAnalResult :: FrameworkNode -> ChangeDetector
changeDetectorAnalResult self_node changed_refs (old, e) (new, e') =
  pprTrace "changeDetector" (ppr $ Set.map fst changed_refs) $
  not (Set.map fst changed_refs `Set.isSubsetOf` Set.singleton self_node) || 
  changeDetectorUsageType changed_refs (old, e) (new, e')

unleashLet
  :: AnalEnv 
  -> RecFlag
  -> [(Id, (CoreExpr, SingleUse -> TransferFunction AnalResult))]
  -> UsageType
  -> UsageType
  -> TransferFunction (UsageType, [(Id, CoreExpr)])
unleashLet env rec_flag transferred_binds ut_usage ut_body = do
  let fam_envs = ae_fam_envs env
  let need_sigs = ae_need_sig_annotation env
  let (ids, transferred_rhss) = unzip transferred_binds
  (ut_rhss, rhss') <- fmap unzip $ forM transferred_binds $ \(id, (rhs, transfer)) ->
    unleashUsage rhs transfer (lookupUsage rec_flag ut_usage id)
  let ut_final = callArityLetEnv (zip ids ut_rhss) ut_body

  --pprTrace "unleashLet" (ppr ids $$ text "ut_body" <+> ppr ut_body $$ text "ut_final" <+> ppr ut_final) $ return ()
  -- Now use that information to annotate binders.
  let (_, usages) = findBndrsUsages rec_flag fam_envs ut_final ids
  let ids' = setBndrsUsageInfo ids usages
  ids'' <- forM (zip ids' transferred_rhss) $ \(id, (_, transfer)) ->
    annotateIdArgUsage need_sigs id transfer

  -- This intentionally still contains the @Id@s of the binding group, because
  -- the recursive rule looks at their usages to determine stability.
  return (ut_final, zip ids'' rhss')

annotateIdArgUsage
  :: VarSet
  -> Id
  -> (SingleUse -> TransferFunction AnalResult)
  -> TransferFunction Id
annotateIdArgUsage need_sigs id transfer_rhs
  | not (id `elemVarSet` need_sigs) = return id
  | otherwise = do
    -- We can't eta-expand beyond idArity anyway (exported!), so our best
    -- bet is a single call with idArity.
    -- Note that in the case where idArity id == 0, there is no interesting
    -- @UsageSig@ to be had.
    -- In that case we *could* try to analyze with arity 1, just for the
    -- signature.
    let single_call = iterate (mkCallUse Once) topSingleUse !! idArity id
    usage_sig <- ut_args . fst <$> transfer_rhs single_call
    return (id `setIdArgUsage` usage_sig)

unleashUsage
  :: CoreExpr
  -> (SingleUse -> TransferFunction AnalResult)
  -> (Usage -> TransferFunction AnalResult)
unleashUsage rhs transfer_rhs usage
  | Absent <- usage
  = return (emptyUsageType, rhs)
  | Used m use <- considerThunkSharing rhs usage
  -- As with arguments, `m` should be `Once` most of the time 
  -- (e.g. if `rhs` is non-trivial, see `considerThunkSharing`).
  -- Thus, the work required to get the RHS of let-bindings 
  -- to WHNF is shared among all use sites.
  -- We still annotate the binder with the multiplicity later on, 
  -- as @Once@ means we don't have to memoize the result anyway.
  = first (multiplyUsages m) <$> transfer_rhs use

-- Combining the results from body and rhs of a let binding
-- See Note [Analysis II: The Co-Called analysis]
callArityLetEnv
  :: [(Id, UsageType)]
  -> UsageType
  -> UsageType
callArityLetEnv rhss ut_body
    = --pprTrace "callArityLetEnv" (vcat [ppr (map fst rhss), ppr (map snd rhss), ppr ut_body, ppr ut_new, ppr (map (lookupUsage Recursive ut_new . fst) rhss)]) $
      ut_new
  where
    (ids, ut_rhss) = unzip rhss

    body_and_rhss good_id
      = (ut_body :)            -- always include the usage type of the body
      . map (unusedArgs . snd) -- we are only interested in the usage types
      . filter (good_id . fst) -- check if the id associated with the usage type is a good_id
      $ rhss

    -- This is already the complete type, but with references from the current
    -- binding group not resolved.
    -- For the non-recursive case, at least ut_body may refer to some bound var
    -- which we have to handle, for the recursive case even any of ut_rhss may.
    -- This is why we have to union in appropriate cross_calls, which basically
    -- perform substitution of Id to UsageType.
    ut_all = body_and_rhss (\id_rhs -> True)

    cross_calls (id, ut_rhs) = botUsageType { ut_uses = uses, ut_cocalled = graph }
      where
        -- ut_others excludes the defining rhs itself, because that is already
        -- accounted for based on the recorded Usage, which is always manified
        -- for recursive binders.
        -- This ensures we don't duplicate shared work, while also manifying anything
        -- under a lambda for recursive groups. In the case of a non-recursive
        -- binding, there is no mention of the id in the rhs anyway.
        ut_others = lubUsageTypes (body_and_rhss (\id_rhs -> id /= id_rhs))
        -- Since Co-Call graphs are not transitive, but recursion is, we have to
        -- conservatively assume that id was called with every neighbor in
        -- ut_others of any of the ids of the binding group.
        called_with_id = unionUnVarSets $ map (calledWith ut_others) ids
        called_by_id = domType ut_rhs
        -- As long as called_with_id does not contain every node in ut_others,
        -- the whole Co-Call hassle played out: We can be more precise than
        -- just smashing everything together with `bothUsageType` (which would
        -- correspond exactly to the scenario called_with_id = domType ut_others).
        graph = completeBipartiteGraph called_by_id called_with_id
        uses = bothUseEnv (ut_uses ut_rhs) (restrict (ut_uses ut_others) called_with_id)
        restrict = restrictVarEnv_UnVarSet

    ut_new
        -- Calculating cross_calls is expensive. Simply be conservative
        -- if the mutually recursive group becomes too large.
        -- Combining all rhs and the body with `bothUsageType` corresponds to
        -- cocalls in the complete graph.
        | length ut_rhss > 25 = bothUsageTypes ut_all
        | otherwise           = lubUsageTypes (ut_all ++ map cross_calls rhss)
