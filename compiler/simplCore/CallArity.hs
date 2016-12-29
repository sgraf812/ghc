{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--
-- Copyright (c) 2014 Joachim Breitner
--

module CallArity
    ( callArityAnalProgram
    , callArityRHS -- for testing
    ) where

import DynFlags      (DynFlags)
import VarEnv

import Data.Monoid
import Data.List     (delete)
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.Map.Strict   (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set

import BasicTypes
import CoreArity     (typeArity)
import CoreSyn
import CoreUtils     (exprIsHNF, exprIsTrivial)
import MkCore
import Id
import Outputable hiding ((<>))
import Demand
import UnVarGraph
import Worklist
import Util
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.State.Strict

import Control.Arrow ((***), first)


{-
%************************************************************************
%*                                                                      *
              Call Arity Analyis
%*                                                                      *
%************************************************************************

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
     For every two variables, whether there is a possibility that both are being
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
   We get the results from both sides, with the argument evaluated at most once.
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

If the variable is already a function (exprIsHNF), and all calls to the
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

In both cases, the body and the rhs of the inner let call n at most once.
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

    type CallArityType = (UnVarGraph, VarEnv Arity)
    callArityAnal ::
        Arity ->  -- The arity this expression is called with
        VarSet -> -- The set of interesting variables
        CoreExpr ->  -- The expression to analyse
        (CallArityType, CoreExpr)

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
      then in no execution of `expr` both are being called.
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
`callArityBind` does still do the right thing we have to take that into account
everytime we look up up `x` in the analysis result of `e2`.
  * Instead of calling lookupCallArityType, we return (0, True), indicating
    that this variable might be called many times with no variables.
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
    analysis call, i.e. incoming arity, whether it is called once, and the CallArityType.
 3. We combine the analysis result from the body and the memoized results for
    the arguments (if already present).
 4. For each variable, we find out the incoming arity and whether it is called
    once, based on the the current analysis result. If this differs from the
    memoized results, we re-analyse the rhs and update the memoized table.
 5. If nothing had to be reanalized, we are done.
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
CallArityType (the co-call graph is the complete graph, all arityies 0).

Note [Trimming arity]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the Call Arity papers, we are working on an untyped lambda calculus with no
other id annotations, where eta-expansion is always possible. But this is not
the case for Core!
 1. We need to ensure the invariant
      callArity e <= typeArity (exprType e)
    for the same reasons that exprArity needs this invariant (see Note
    [exprArity invariant] in CoreArity).

    If we are not doing that, a too-high arity annotation will be stored with
    the id, confusing the simplifier later on.

 2. Eta-expanding a right hand side might invalidate existing annotations. In
    particular, if an id has a strictness annotation of <...><...>b, then
    passing two arguments to it will definitely bottom out, so the simplifier
    will throw away additional parameters. This conflicts with Call Arity! So
    we ensure that we never eta-expand such a value beyond the number of
    arguments mentioned in the strictness signature.
    See #10176 for a real-world-example.

-}


-- See Note [Analysing top-level-binds]
-- Represents the fact that a CoreProgram is like a sequence of
-- nested lets, where the exports are returned in the inner-most let
-- as a tuple. As a result, all exported identifiers are handled as called
-- with each other, with arity 0.
moduleToExpr :: CoreProgram -> CoreExpr
moduleToExpr = impl []
  where
    impl exported [] = mkBigCoreTup (map Var exported)
    impl exported (bind:prog) = Let bind (impl (filter isExportedId (bindersOf bind) ++ exported) prog)

exprToModule :: CoreExpr -> CoreProgram
exprToModule (Let bind e) = bind : exprToModule e
exprToModule _ = []

-- Main entry point
callArityAnalProgram :: DynFlags -> CoreProgram -> CoreProgram
callArityAnalProgram _dflags = exprToModule . callArityRHS . moduleToExpr

callArityRHS :: CoreExpr -> CoreExpr
callArityRHS e = lookup_expr (runFramework fw (Set.singleton (node, 0)))
  where
    (node, fw) = buildFramework $
      registerTransferFunction $ \node -> do
        transfer <- callArityExpr emptyVarEnv e
        -- We only get away with using alwaysChangeDetector because this won't
        -- introduce a cycle.
        return (node, (transfer, alwaysChangeDetector))

    lookup_expr :: Map (FrameworkNode, Arity) AnalResult -> CoreExpr
    lookup_expr result_map = case Map.lookup (node, 0) result_map of
      Nothing -> pprPanic "callArityRHS" empty
      Just (AR _ annotations) -> annotate annotations e

newtype Annotations
  = Annotations (VarEnv Arity)
  deriving (Eq, Outputable)

mkAnnotation :: Id -> Arity -> Annotations
mkAnnotation id arity = Annotations (unitVarEnv id arity)

lookupAnnotatedArity :: Annotations -> Id -> Arity
lookupAnnotatedArity (Annotations ann) id = fromMaybe (idCallArity id) (lookupVarEnv ann id)

instance Monoid Annotations where
  mempty = Annotations mempty
  mappend (Annotations a) (Annotations b)
    = Annotations (plusVarEnv_C panicOnConflict a b)
    where
      panicOnConflict n m
        | n == m    = n
        | otherwise = pprPanic "CallArity.Annotations.mappend conflict"
                               (vcat [ppr n <+> text "vs" <+> ppr m, ppr a, ppr b])

-- | How an expression uses its interesting variables
-- and the arity annotations for local bindings
data AnalResult = AR !CallArityType !Annotations

instance Outputable AnalResult where
  ppr (AR cat ann) = vcat [text "type:" <+> ppr cat, text "annotations:" <+> ppr ann]

unzipAnalResult :: [AnalResult] -> ([CallArityType], Annotations)
unzipAnalResult ar = (map cat ar, foldMap ann ar)
  where
    cat (AR cat _) = cat
    ann (AR _ ann) = ann

newtype FrameworkNode
  = FrameworkNode Int
  deriving (Show, Eq, Ord, Outputable)

type TransferFunction' a = TransferFunction (FrameworkNode, Arity) AnalResult a
type ChangeDetector' = ChangeDetector (FrameworkNode, Arity) AnalResult
type DataFlowFramework' = DataFlowFramework (FrameworkNode, Arity) AnalResult

newtype FrameworkBuilder a
  = FB { unFB :: State (IntMap (Arity -> TransferFunction' AnalResult, ChangeDetector')) a }
  deriving (Functor, Applicative, Monad)

data LetAnalKind
  = LetDown
  | LetUp
  deriving (Show, Eq, Ord)

isLetUp :: LetAnalKind -> Bool
isLetUp LetUp = True
isLetUp LetDown = False

buildFramework :: FrameworkBuilder a -> (a, DataFlowFramework')
buildFramework (FB state) = (res, DFF dff)
  where
    (res, env) = runState state IntMap.empty
    dff (FrameworkNode node, arity) = case IntMap.lookup node env of
      Nothing -> pprPanic "CallArity.buildFramework" (ppr node)
      Just (transfer, detectChange) -> (transfer arity, detectChange)

registerTransferFunction
  :: (FrameworkNode -> FrameworkBuilder (a, (Arity -> TransferFunction' AnalResult, ChangeDetector')))
  -> FrameworkBuilder a
registerTransferFunction f = FB $ do
  node <- gets IntMap.size
  (result, _) <- mfix $ \ ~(_, entry) -> do
    -- Using mfix so that we can spare an unnecessary Int counter in the state
    modify' (IntMap.insert node entry)
    unFB (f (FrameworkNode node))
  return result

dependOn' :: FrameworkNode -> Arity -> TransferFunction' AnalResult
dependOn' node arity = fromMaybe emptyAnalResult <$> dependOn (node, arity)

-- | The main analysis function. See Note [Analysis type signature]
callArityExpr
  :: VarEnv LetAnalKind
  -> CoreExpr
  -> FrameworkBuilder (Arity -> TransferFunction' AnalResult)

callArityExprTrivial
  :: FrameworkBuilder (Arity -> TransferFunction' AnalResult)
callArityExprTrivial = return (\_ -> return emptyAnalResult)

-- The trivial base cases
callArityExpr _ (Lit _) = callArityExprTrivial
callArityExpr _ (Type _) = callArityExprTrivial
callArityExpr _ (Coercion _) = callArityExprTrivial

-- The transparent cases
callArityExpr let_anal_kinds (Tick _ e) = callArityExpr let_anal_kinds e
callArityExpr let_anal_kinds (Cast e _) = callArityExpr let_anal_kinds e

-- The interesting cases: Variables, Lambdas, Lets, Applications, Cases
callArityExpr let_anal_kinds (Var v) = return transfer
  where
    transfer = case lookupVarEnv let_anal_kinds v of
      Nothing | not (isInteresting v) -> \_ -> return emptyAnalResult -- v is boring
      Nothing -> \arity -> return (AR (unitArityType v arity) mempty) -- TODO: use an exported sig here
      Just LetUp -> \arity -> return (AR (unitArityType v arity) mempty) -- the demand is unleashed later
      Just LetDown -> \arity ->
        -- unleash cat directly
        dependOn' undefined arity

-- Non-value lambdas are ignored
callArityExpr let_anal_kinds (Lam v e)
    | not (isId v)
    = callArityExpr let_anal_kinds e

callArityExpr let_anal_kinds (Lam v e) = transfer' <$> callArityExpr let_anal_kinds e
  where
    -- We have a lambda that may be called multiple times, so its free variables
    -- can all be co-called.
    -- Also regardless of the variable not being interesting,
    -- we have to add the var as an argument.
    transfer' transfer 0 = do
      AR cat ann <- transfer 0
      return (AR (addArgToType v (calledMultipleTimes cat)) ann)
    -- We have a lambda that we are calling. decrease arity.
    transfer' transfer arity = do
      AR cat ann <- transfer (arity - 1)
      return (AR (addArgToType v cat) ann)

callArityExpr let_anal_kinds (App f (Type _)) = callArityExpr let_anal_kinds f

-- Application. Increase arity for the called expression, nothing to know about
-- the second
callArityExpr let_anal_kinds (App f a) = do
  transfer_f <- callArityExpr let_anal_kinds f
  transfer_a <- callArityExpr let_anal_kinds a
  return $ \arity -> do
    AR ca_f ann_f <- transfer_f (arity + 1)
    -- peel off one argument from the type
    let (arg_arity, called_once, ca_f') = peelCallArityType a ca_f
    -- TODO: Actually use called with information instead of just called_once
    --       Maybe this is enough for higher-order signature information?
    AR ca_a ann_a <- transfer_a arg_arity
    let ca_a' | called_once    = ca_a
              | arg_arity == 0 = ca_a
              | otherwise      = calledMultipleTimes ca_a
    return (AR (ca_f' `both` ca_a') (pprTrace "ann_f" empty ann_f <> pprTrace "ann_a" empty ann_a))

-- Case expression.
callArityExpr let_anal_kinds (Case scrut bndr ty alts) = do
  transfer_scrut <- callArityExpr let_anal_kinds scrut
    -- TODO: Do we have to do something special with bndr?
  transfer_alts <- mapM (\(dc, bndrs, e) -> callArityExpr let_anal_kinds e) alts
  return $ \arity -> do
    AR cat_scrut ann_scrut <- transfer_scrut 0
    (cat_alts, ann_alts) <- unzipAnalResult <$> mapM ($ arity) transfer_alts
    let cat = cat_scrut `both` lubTypes cat_alts
    -- pprTrace "callArityExpr:Case"
    --          (vcat [ppr scrut, ppr cat])
    return (AR cat (pprTrace "ann_scrut" empty ann_scrut <> ann_alts))

callArityExpr let_anal_kinds (Let bind e) = do
  let add_let_kind (id, rhs) env
        | isInteresting id = extendVarEnv env id (determineLetAnalKind rhs)
        | otherwise = env
  let binds = flattenBinds [bind]
  let let_anal_kinds' = foldr add_let_kind let_anal_kinds binds

  -- The order in which we call callArityExpr here is important: This makes sure
  -- we first stabilize bindings before analyzing the body.
  transferred_binds <- forM binds $ \(id, rhs) -> do
    transfer_rhs <- callArityExpr let_anal_kinds' rhs
    return (id, rhs, transfer_rhs)
  transfer_body <- callArityExpr let_anal_kinds' e

  case bind of
    NonRec _ _ ->
      -- We don't need to dependOn ourselves here, because only the let body can
      -- call id.
      return $ \arity -> do
        ar_body <- transfer_body arity
        AR cat ann <- unleashLet False transferred_binds ar_body ar_body
        return (AR (typeDelList (bindersOf bind) cat) ann)
    Rec _ -> do
      -- This is a little more complicated, as we'll introduce a new FrameworkNode
      -- which we'll depend on ourselves.
      node <- registerTransferFunction $ \node -> do
        let transfer arity = do
              ar_body <- transfer_body arity
              -- This is the actual fixed-point iteration: we depend on usage
              -- results from the previous iteration, defaulting to just the body.
              ar_usage <- fromMaybe ar_body <$> dependOn (node, arity)
              unleashLet True transferred_binds ar_usage ar_body

        let changeDetector changedRefs (AR old _) (AR new _) =
              -- since we only care for arity and called once information of the
              -- previous iteration, we cann efficiently test for changes.
              map fst (Set.toList changedRefs) /= [node]
              || any (\id -> lookupCallArityType old id /= lookupCallArityType new id) (map fst binds)

        return (node, (transfer, changeDetector))

      -- Now for the actual TransferFunction of this expr...
      return $ \arity -> do
        AR cat ann <- dependOn' node arity
        return (AR (typeDelList (bindersOf bind) cat) ann)

unleashLet :: Bool -> [(Id, CoreExpr, Arity -> TransferFunction' AnalResult)] -> AnalResult -> AnalResult -> TransferFunction' AnalResult
unleashLet is_recursive transferred_binds (AR cat_usage ann_usage) (AR cat_body ann_body) = do
  (cat_rhss, ann_rhss) <- unzipAnalResult <$> mapM (unleashCall is_recursive cat_usage) transferred_binds
  let ids = map (\(id, _, _) -> id) transferred_binds
  let cat_final = callArityLetEnv ann_usage (zip ids cat_rhss) cat_body
  return (AR cat_final (pprTraceIt "ann_body" ann_body <> pprTraceIt "ann_rhss" ann_rhss))

unleashCall :: Bool -> CallArityType -> (Id, CoreExpr, Arity -> TransferFunction' AnalResult) -> TransferFunction' AnalResult
unleashCall is_recursive cat_usage (id, rhs, transfer_rhs)
  | isInteresting id && not (id `elemUnVarSet` domType cat_usage)
  = return emptyAnalResult -- No call to `id` (yet)
  | otherwise
  = do
    let boring = not (isInteresting id)
        -- If v is boring, we will not find it in cat_usage, but always assume (0, False)
        (arity, called_once)
            | boring    = (0, False) -- See Note [Taking boring variables into account]
            | otherwise = --pprTrace "CallArity.unleashCalls" (ppr id <+> ppr (lookupCallArityType cat_usage id)) $
                          lookupCallArityType cat_usage id

        -- See Note [Thunks in recursive groups]
        safe_arity
            | isThunk rhs && (is_recursive || not called_once) = 0 -- A thunk was called multiple times! Do not eta-expand
            | otherwise = arity -- in the other cases it's safe to expand

        -- See Note [Trimming arity]
        trimmed_arity = trimArity id safe_arity

    -- TODO: Find out if (where) we need the trimmed_arity here or not
    -- We probably want to analyze with arity und annotate trimmed_arity.
    -- Although CA analyzes with trimmed_arity, so we do that for now
    AR cat_rhs ann_rhs <- transfer_rhs trimmed_arity
    let cat_rhs' | called_once || safe_arity == 0 = cat_rhs
                 | otherwise = calledMultipleTimes cat_rhs
    return (AR cat_rhs' ((pprTrace "annotating" (ppr id <+> ppr trimmed_arity) mkAnnotation id trimmed_arity) <> ann_rhs))

determineLetAnalKind :: CoreExpr -> LetAnalKind
determineLetAnalKind rhs
  | isThunk rhs || True = LetUp
  | otherwise = LetDown

isThunk :: CoreExpr -> Bool
isThunk = not . exprIsHNF

-- TODO: add the set of neighbors
peelCallArityType :: CoreExpr -> CallArityType -> (Arity, Bool, CallArityType)
peelCallArityType a ca_type = case cat_args ca_type of
  arg:_ | isInteresting arg ->
    -- TODO: not (exprIsTrivial a)?
    -- TODO: called_once when arity = 0?
    let (arity, called_once) = lookupCallArityType ca_type arg
        ca_type' = typeDel arg ca_type
    in  (arity, called_once, ca_type')
  _:_ -> (0, False, ca_type) -- See Note [Taking boring variables into account]
  [] -> (0, not (exprIsTrivial a), ca_type)
    -- the called function had no signature or has not
    -- been analysed with high enough incoming arity
    -- (e.g. when loading the signature from an imported id).
    -- ca_f is rather useless for analysing a, so
    -- be consersative assume incoming arity 0.
    --
    -- Also, if the argument is trivial (e.g. a variable), then it will _not_ be
    -- let-bound in the Core to STG transformation (CorePrep actually),
    -- so no sharing will happen here, and we have to assume many calls.

-- Which bindings should we look at?
-- See Note [Which variables are interesting]
isInteresting :: Var -> Bool
isInteresting v = not $ null (typeArity (idType v))

-- Combining the results from body and rhs of a let binding
-- See Note [Analysis II: The Co-Called analysis]
callArityLetEnv
  :: Annotations
  -> [(Var, CallArityType)]
  -> CallArityType
  -> CallArityType
callArityLetEnv ann_old cat_rhss cat_body
    = -- (if length ae_rhss > 300 then pprTrace "callArityLetEnv" (vcat [ppr ae_rhss, ppr ae_body, ppr ae_new]) else id) $
      cat_new
  where
    vars = map fst cat_rhss

    -- This is already the complete type, but with references from the current
    -- binding group not resolved.
    -- For the non-recursive case, at least cat_body may refer to some bound var
    -- which we have to handle, for the recursive case even any of cat_rhss may.
    -- This is why we have to union in appropriate cross_calls, which basically
    -- perform substitution of Id to CallArityType.
    cat_combined = lubTypes (map snd cat_rhss) `lubType` cat_body

    cross_calls
        -- Calculating cross_calls is expensive. Simply be conservative
        -- if the mutually recursive group becomes too large.
        | length cat_rhss > 25 = completeGraph (domType cat_combined)
        | otherwise            = unionUnVarGraphs $ map cross_call cat_rhss
    cross_call (v, cat_rhs) = completeBipartiteGraph called_by_v called_with_v
      where
        is_thunk = lookupAnnotatedArity ann_old v == 0
        -- We only add self cross calls if we really can recurse into ourselves.
        -- This is not the case for thunks (and non-recursive bindings, but
        -- then there won't be any mention of v in the rhs).
        -- A thunk is not evaluated more than once, so the only
        -- relevant calls are from other bindings or the body.
        -- What rhs are relevant as happening before (or after) calling v?
        --    If v doesn't recurse into itself, everything from all the _other_ variables
        --    If v is self-recursive, everything can happen.
        cat_before_v
            | is_thunk  = lubTypes (map snd $ filter ((/= v) . fst) cat_rhss) `lubType` cat_body
            | otherwise = cat_combined
        -- What do we want to know from these?
        -- Which calls can happen next to any recursive call.
        called_with_v = unionUnVarSets $ map (calledWith cat_before_v) vars
        called_by_v = domType cat_rhs

    cat_new = modifyCoCalls (cross_calls `unionUnVarGraph`) cat_combined

-- See Note [Trimming arity]
trimArity :: Id -> Arity -> Arity
trimArity v a = minimum [a, max_arity_by_type, max_arity_by_strsig]
  where
    max_arity_by_type = length (typeArity (idType v))
    max_arity_by_strsig
        | isBotRes result_info = length demands
        | otherwise = a

    (demands, result_info) = splitStrictSig (idStrictness v)

annotate :: Annotations -> CoreExpr -> CoreExpr
annotate ann e = case e of
  Lit _ -> e
  Type _ -> e
  Coercion _ -> e
  Var _ -> e
  Tick t e -> Tick t (annotate ann e)
  Cast e co -> Cast (annotate ann e) co
  Lam v e -> Lam v (annotate ann e) -- TODO: Also annotate v? Seems important for LetDown
  App f a -> App (annotate ann f) (annotate ann a)
  Let (NonRec id rhs) e -> Let (NonRec (annotateId ann id) (annotate ann rhs)) (annotate ann e)
  Let (Rec pairs) e -> Let (Rec (map (annotateId ann *** annotate ann) pairs)) (annotate ann e)
  Case scrut bndr ty alts -> Case (annotate ann scrut) bndr ty (map annotate_alt alts)
    where
      annotate_alt (dc, bndrs, e) = (dc, bndrs, annotate ann e)

annotateId :: Annotations -> Id -> Id
annotateId ann id = id `setIdCallArity` lookupAnnotatedArity ann id

---------------------------------------
-- Functions related to CallArityType --
---------------------------------------

-- Result type for the two analyses.
-- See Note [Analysis I: The arity analyis]
-- and Note [Analysis II: The Co-Called analysis]
data CallArityType
  = CAT
  { cat_cocalled :: UnVarGraph
  , cat_arities :: VarEnv Arity
  , cat_args :: [Var]
  }

instance Outputable CallArityType where
  ppr (CAT cocalled arities args) =
    text "args:" <+> ppr args
    <+> text "co-calls:" <+> ppr cocalled
    <+> text "arities:" <+> ppr arities

emptyArityType :: CallArityType
emptyArityType = CAT emptyUnVarGraph emptyVarEnv []

emptyAnalResult :: AnalResult
emptyAnalResult = AR emptyArityType mempty

unitArityType :: Var -> Arity -> CallArityType
unitArityType v arity = CAT emptyUnVarGraph (unitVarEnv v arity) []

typeDelList :: [Var] -> CallArityType -> CallArityType
typeDelList vs ae = foldr typeDel ae vs

-- TODO: args handling
-- TODO: What about transitive co-call relationships over v?
typeDel :: Var -> CallArityType -> CallArityType
typeDel v (CAT g ae args) = CAT (g `delNode` v) (ae `delVarEnv` v) (delete v args)

domType :: CallArityType -> UnVarSet
domType ca_type = varEnvDom (cat_arities ca_type)

addArgToType :: Id -> CallArityType -> CallArityType
addArgToType id ca_type = ca_type { cat_args = id : cat_args ca_type }

-- In the result, find out the minimum arity and whether the variable is called
-- at most once.
lookupCallArityType :: CallArityType -> Var -> (Arity, Bool)
lookupCallArityType (CAT g ae _) v
    = case lookupVarEnv ae v of
        Just a -> (a, not (v `elemUnVarSet` neighbors g v))
        Nothing -> (0, False)

calledWith :: CallArityType -> Var -> UnVarSet
calledWith ca_type v
  | isInteresting v
  = neighbors (cat_cocalled ca_type) v
  | otherwise
  = domType ca_type

modifyCoCalls :: (UnVarGraph -> UnVarGraph) -> CallArityType -> CallArityType
modifyCoCalls modifier ca_type
  = ca_type { cat_cocalled = modifier (cat_cocalled ca_type) }

addCrossCoCalls :: UnVarSet -> UnVarSet -> CallArityType -> CallArityType
addCrossCoCalls set1 set2
  = modifyCoCalls (completeBipartiteGraph set1 set2 `unionUnVarGraph`)

-- Replaces the co-call graph by a complete graph (i.e. no information)
calledMultipleTimes :: CallArityType -> CallArityType
calledMultipleTimes res = modifyCoCalls (const (completeGraph (domType res))) res

-- Used for application and cases
both :: CallArityType -> CallArityType -> CallArityType
both r1 r2 = addCrossCoCalls (domType r1) (domType r2) (r1 `lubType` r2)

-- Used when combining results from alternative cases; take the minimum
lubType :: CallArityType -> CallArityType -> CallArityType
lubType (CAT g1 ae1 args) (CAT g2 ae2 _) -- both args should really be the same
  = CAT (g1 `unionUnVarGraph` g2) (ae1 `lubArityEnv` ae2) args

lubArityEnv :: VarEnv Arity -> VarEnv Arity -> VarEnv Arity
lubArityEnv = plusVarEnv_C min

lubTypes :: [CallArityType] -> CallArityType
lubTypes = foldl lubType emptyArityType
