{-
Author: George Karachalias <george.karachalias@cs.kuleuven.be>

The term equality oracle. The main export of the module is function `tmOracle'.
-}

{-# LANGUAGE CPP, MultiWayIf, GeneralisedNewtypeDeriving, PatternSynonyms #-}

module TmOracle (

        -- the term oracle
        tmOracle, TmState, initialTmState, solveComplexEq, extendSubst, canDiverge,

        -- misc.
        toComplex, exprDeepLookup, pmLitType, flattenFactEnv
    ) where

#include "HsVersions.h"

import GhcPrelude

import Id
import Name
import Type
import HsLit
import TcHsSyn
import MonadUtils
import Util
import Outputable

import FV
import VarEnv
import CoreSubst
import CoreFVs
import CoreSyn
import CoreMap

{-
%************************************************************************
%*                                                                      *
                      The term equality oracle
%*                                                                      *
%************************************************************************
-}

-- | Invariant: We map to the key with which we index the 'CoreMap' in order for
-- 'foldTM' to provide us with the key. Yuck.
type CoreSet = CoreMap CoreExpr

coreSetFreeIdsList :: CoreSet -> [Id]
coreSetFreeIdsList cs =
  fvVarList $ filterFV isLocalId $ foldTM (unionFV . exprFVs) cs emptyFV

-- | Simple term equality
data SimpleEq = Smpl !Id !CoreExpr

-- | Complex term equality
data ComplexEq = Cplx !CoreExpr !CoreExpr

-- | Lift a 'SimpleEq' to a 'ComplexEq'
toComplex :: SimpleEq -> ComplexEq
toComplex (Smpl x e) = Cplx (Var x) e

-- | This is actually just an 'CoreSubst.IdSubstEnv', but we inlined the synonym
-- for symmetry with 'RefutEnv'.
type FactEnv  = IdEnv CoreExpr
-- | Records refutable expressions for each identifier. We write \(x ~ E \in
-- \Gamma \) when @E@ is in the 'CoreSet' of @x@ according to the 'RefutEnv'
-- \(\Gamma\).
type RefutEnv = IdEnv LiteralMap

--
-- * Indexing stuff
--

type Index = IdEnv IdSet

addFreeIds :: Id -> [Id] -> Index -> Index
addFreeIds x ids idx = foldr (\y idx -> modifyVarEnv idx (`extendVarSet` x) y) idx ids

indexCoreExpr :: Id -> CoreExpr -> Index -> Index
indexCoreExpr x e idx = addFreeIds (exprFreeIdsList e) idx

indexCoreSet :: Id -> CoreSet -> Index -> Index
indexCoreSet x cs idx = addFreeIds (coreSetFreeIdsList cs) idx

type RepEnv = UniqFM CoreSet

-- | The environment of the oracle.
data TmOracleEnv = TOE
  { toe_facts     :: !FactEnv
  -- ^ A triangular substitution we extend when we brought a 'ComplexEq' from
  -- 'ts_standby' into 'SimpleEq' form. This is an 'CoreSubst.IdSubstEnv', but
  -- we inlined the synonym for symmetry with 'toe_refuts'.
  -- TODO: This might not be enough for handling function applications. For
  -- example, it's simultaneously possible for @x@ to be the result of @f 42@
  -- and of @g 5@ (@f 41@, even). (Is it, though? Yes, imagine if/then/else).
  -- For now we assume that we only record facts equating to *matchable*
  -- expressions. This means we can't really record much at all apart from
  -- literals and con apps... Maybe switch to 'IdEnv CoreSet' later? But what's
  -- the point? We should probably have these contraints in the worklist...
  , toe_refuts    :: !RefutEnv
  -- ^ When \(x ~ E \in \Gamma\), then we can refute satisfiability as soon as
  -- we can prove that \(x ~ E\). This tracks negative equalities occuring in
  -- case splits. E.g., after the clause guarded by @Nothing <- x@, we know that
  -- @x@ can't be @Nothing@, so we have \(x ~ Nothing \in \Gamma\).
  -- TODO: Is this really Reader-like state? I.e. don't we want to take some
  -- refutations we learned with us when we leave scope?
  , toe_us        :: !UniqSupply
  , toe_reps      :: !RepEnv
  , toe_in_scope  :: !InScopeSet
  -- ^ The variables currently in scope. Should agree with 'toe_facts' and
  -- 'toe_refuts', i.e. when a new variable shadows we have to remove it from
  -- the substitutions. TODO: We should not really discard old entries, as they
  -- might be useful when we leave the scope again (in which case we also have
  -- to prune any equations involving out-of-scope binders)
  -- TODO: Removing from the substitution doesn't work, unless we are willing
  -- to index all data structures for free ids. Also it's unnecessary, as the
  -- information is perfectly valid, it just so happens that the name is taken.
  -- Instead, we should thread around an RnEnv and substitute shadowing occs
  -- accordingly.
  }

-- | The solver_state of the term oracle.
-- TODO: Check that if after we have 'toe_refuts', 'SimpleEq' only (see Note
-- [Representation of Term Equalities]) becomes viable again.
-- Is 2. in that note even accurate? Why can't we have 'ComplexEq' in triangular
-- form by introducing new variables as necessary? It's surely OK to just go
-- through 'toe_facts' when needed?
data TmState = TS
  { ts_standby :: ![ComplexEq]
  -- ^ Complex constraints that cannot progress unless we get more information.
  , ts_env     :: !TmOracleEnv
  -- ^ The current environment of the term oracle.
  }

-- | Initial solver_state of the oracle.
initialTmState :: InScopeSet -> TmState
initialTmState in_scope = TS [] (TOE emptyVarEnv emptyVarEnv emptyVarEnv emptyVarEnv in_scope)

-- | Prepends a 'ComplexEq' to 'ts_standby'.
deferComplexEq :: ComplexEq -> TmState -> TmState
deferComplexEq eq st = st { ts_standby = eq : ts_standby st }

-- | Check whether a constraint (x ~ BOT) can succeed,
-- given the resulting solver_state of the term oracle.
canDiverge :: Var -> TmState -> Bool
canDiverge x TS{ ts_standby = standby, ts_env = env }
  -- If the variable seems not evaluated, there is a possibility for
  -- constraint x ~ BOT to be satisfiable.
  | Var y <- varDeepLookup (toe_facts env) x -- seems not forced
  -- If it is involved (directly or indirectly) in any equality in the
  -- worklist, we can assume that it is already indirectly evaluated,
  -- as a side-effect of equality checking. If not, then we can assume
  -- that the constraint is satisfiable.
  = not $ any (isForcedByEq x) standby || any (isForcedByEq y) standby
  -- Variable x is already in WHNF so the constraint is non-satisfiable
  | otherwise = False
  where
    isForcedByEq :: Name -> ComplexEq -> Bool
    isForcedByEq y (Cplx e1 e2) = varIn y e1 || varIn y e2

-- | Check whether a variable is in the free variables of an expression
varIn :: Var -> CoreExpr -> Bool
varIn x e = x `elemVarSet` exprFreeIds e

-- | Determine if the given variable is rigid and if so, return its solution.
isRigid_maybe :: FactEnv -> Var -> Maybe CoreExpr
isRigid_maybe = lookupVarEnv

-- | Attempt to solve a complex equality.
-- Nothing => definitely unsatisfiable
-- Just tms => I have added the complex equality and added
--             it to the tmstate; the result may or may not be
--             satisfiable
solveComplexEq :: TmState -> ComplexEq -> Maybe TmState
solveComplexEq solver_state (Cplx e1 e2)
  | let in_scope = toe_in_scope (ts_env solver_state)
  , Just (con1, _tys, args1) <- exprIsConApp_maybe in_scope e1
  , Just (con2, _tys, args2) <- exprIsConApp_maybe in_scope e2
  = if con1 == con2
      then foldlM solveComplexEq solver_state (zipWith Cplx ts1 ts2)
      else unsat
solveComplexEq solver_state eq@(Cplx e1 e2) = case (e1, e2) of
  (Lit l1, Lit l2)
    | l1 == l2  -> solved
    | otherwise -> unsat

  (Var x, Var y)
    | x == y    -> solved
  (Var x, _)
    | Just e1' <- isRigid_maybe (toe_facts (ts_env solver_state)) x
    -> solveComplexEq e1' e2
    | otherwise
    -> extendSubstAndSolve x e2 solver_state
  (_, Var _)    -> symmetric

  _
    | cheapEqExpr' (const True) e1 e2 -> solved
    | otherwise                       -> defer
  where
    solved    = Just solver_state
    defer     = Just (deferComplexEq eq solver_state)
    unsat     = Nothing
    symmetric = solveComplexEq solver_state (Cplx e2 e1)

-- Compute the fixpoint of the given function by repeatedly applying it to an
-- initial set until the series stabilises.
fixVarSet :: (Var -> VarSet) -> VarSet -> VarSet
fixVarSet f s = fst $ head $ dropWhile (uncurry (/=)) $ zip series (tail series)
  where
    series = iterate (mapUnionVarSet f . nonDetEltsUfm) s

-- | Extend the substitution and solve the (possibly updated) constraints.
extendSubstAndSolve :: Var -> CoreExpr -> TmState -> Maybe TmState
extendSubstAndSolve x e state
  = foldlM solveComplexEq new_incr_state (map simplifyComplexEq changed)
  where
    -- Apply the substitution to the worklist and partition them to the ones
    -- that had some progress and the rest. Then, recurse over the ones that
    -- had some progress. Careful about performance:
    -- See Note [Representation of Term Equalities] in deSugar/Check.hs
    (changed, unchanged) = partitionWith (substComplexEq x e) (ts_standby state)
    env                  = ts_env ts
    new_env              = env { toe_facts = extendVarEnv (toe_facts env) x e }
    new_incr_state       = state { ts_standby = unchanged, ts_env = new_env }

    idx_facts            = toe_idx_facts env
    transitive_changes   = fixVarSet (lookupIndex idx_facts) (unitVarSet x)
    might_refute         = lookupIndex (toe_idx_refuts)
    new_idx_facts        = indexCoreExpr x e (toe_idx_facts env)
    new_idx_refuts       = indexCoreExpr x e (toe_idx_refuts env)

-- | When we know that a variable is fresh, we do not actually have to
-- check whether anything changes, we know that nothing does. Hence,
-- `extendSubst` simply extends the substitution, unlike what
-- `extendSubstAndSolve` does.
extendSubst :: Id -> CoreExpr -> TmState -> TmState
extendSubst x e state = state { ts_env = new_env }
  where
    env = ts_env state
    new_env = env { toe_facts = extendVarEnv (toe_facts env) x simpl_e }
    simpl_e = fst $ simplifyPmExpr $ exprDeepLookup env e

-- | Apply an (un-flattened) substitution to a simple equality.
applySubstComplexEq :: FactEnv -> ComplexEq -> ComplexEq
applySubstComplexEq env (Cplx e1 e2) = Cplx (exprDeepLookup env e1) (exprDeepLookup env e2)

-- | Apply an (un-flattened) substitution to a variable.
varDeepLookup :: PmVarEnv -> Var -> CoreExpr
varDeepLookup env x
  | Just e <- lookupNameEnv env x = exprDeepLookup env e -- go deeper
  | otherwise                  = Var x          -- terminal
{-# INLINE varDeepLookup #-}

-- | Apply an (un-flattened) substitution to an expression.
exprDeepLookup :: PmVarEnv -> CoreExpr -> CoreExpr
exprDeepLookup env (PmExprCon c es) = PmExprCon c (map (exprDeepLookup env) es)
exprDeepLookup env (Var x)    = varDeepLookup env x
exprDeepLookup env (PmExprEq e1 e2) = PmExprEq (exprDeepLookup env e1)
                                               (exprDeepLookup env e2)
exprDeepLookup _   other_expr       = other_expr -- PmExprLit, PmExprOther

-- | External interface to the term oracle.
tmOracle :: TmState -> [ComplexEq] -> Maybe TmState
tmOracle tm_state eqs = foldlM solveOneEq tm_state eqs

{- Note [Deep equalities]
~~~~~~~~~~~~~~~~~~~~~~~~~
Solving nested equalities is the most difficult part. The general strategy
is the following:

  * Equalities of the form (True ~ (e1 ~ e2)) are transformed to just
    (e1 ~ e2) and then treated recursively.

  * Equalities of the form (False ~ (e1 ~ e2)) cannot be analyzed unless
    we know more about the inner equality (e1 ~ e2). That's exactly what
    `simplifyEqExpr' tries to do: It takes e1 and e2 and either returns
    truePmExpr, falsePmExpr or (e1' ~ e2') in case it is uncertain. Note
    that it is not e but rather e', since it may perform some
    simplifications deeper.
-}
