{-
Author: George Karachalias <george.karachalias@cs.kuleuven.be>

The term equality oracle. The main export of the module is function `tmOracle'.
-}

{-# LANGUAGE CPP, MultiWayIf #-}

module TmOracle (

        -- re-exported from PmExpr
        PmExpr(..), PmLit(..), SimpleEq, ComplexEq, PmVarEnv, falsePmExpr,
        eqPmLit, filterComplex, isNotPmExprOther, runPmPprM, lhsExprToPmExpr,
        hsExprToPmExpr, pprPmExprWithParens,

        -- the term oracle
        tmOracle, TmState, initialTmState, solveOneEq, extendSubst, canDiverge,

        -- misc.
        toComplex, exprDeepLookup, pmLitType, flattenPmVarEnv
    ) where

#include "HsVersions.h"

import GhcPrelude

import PmExpr

import Id
import Name
import Type
import HsLit
import TcHsSyn
import MonadUtils
import Util
import Outputable

import VarEnv
import CoreSubst
import CoreSyn

{-
%************************************************************************
%*                                                                      *
                      The term equality oracle
%*                                                                      *
%************************************************************************
-}

-- | Simple term equality
data SimpleEq = Smpl !Id !CoreExpr

-- | Complex term equality
data ComplexEq = Cplx !CoreExpr !CoreExpr

-- | Lift a 'SimpleEq' to a 'ComplexEq'
toComplex :: SimpleEq -> ComplexEq
toComplex (Smpl x e) = Cplx (Var x) e

type PmVarEnv = IdSubstEnv

-- | The environment of the oracle.
data TmOracleEnv = TOE
  { toe_unhandled :: !Bool
  -- ^ Are there any constraints we cannot handle?
  , toe_subst     :: !PmVarEnv
  -- ^ A substitution we extend with every step and return as a result
  }

-- | The solver_state of the term oracle.
data TmState = TS
  { ts_standby :: ![ComplexEq]
  -- ^ Complex constraints that cannot progress unless we get more information.
  , ts_env     :: !TmOracleEnv
  -- ^ The current environment of the term oracle.
  }

-- | Initial solver_state of the oracle.
initialTmState :: TmState
initialTmState = TS [] (TOE False emptyVarEnv)

-- | Set the 'toe_unhandled' flag in the 'TmState's 'ts_env'.
markUnhandled :: TmState -> TmState
markUnhandled st = st { ts_env = ts_env st { toe_unhandled = True } }

-- | Prepends a 'ComplexEq' to 'ts_standby'.
deferComplexEq :: ComplexEq -> TmState -> TmState
deferComplexEq eq st = st { ts_standby = eq : ts_standby st }

-- | Check whether a constraint (x ~ BOT) can succeed,
-- given the resulting solver_state of the term oracle.
canDiverge :: Var -> TmState -> Bool
canDiverge x TS{ ts_standby = standby, ts_env = env }
  -- If the variable seems not evaluated, there is a possibility for
  -- constraint x ~ BOT to be satisfiable.
  | Var y <- varDeepLookup (toe_subst env) x -- seems not forced
  -- If it is involved (directly or indirectly) in any equality in the
  -- worklist, we can assume that it is already indirectly evaluated,
  -- as a side-effect of equality checking. If not, then we can assume
  -- that the constraint is satisfiable.
  = not $ any (isForcedByEq x) standby || any (isForcedByEq y) standby
  -- Variable x is already in WHNF so the constraint is non-satisfiable
  | otherwise = False
  where
    isForcedByEq :: Name -> ComplexEq -> Bool
    isForcedByEq y (e1, e2) = varIn y e1 || varIn y e2

-- | Check whether a variable is in the free variables of an expression
varIn :: Var -> CoreExpr -> Bool
varIn x e = x `elemVarSet` exprFreeIds e

-- | Flatten the DAG (Could be improved in terms of performance.).
flattenPmVarEnv :: PmVarEnv -> PmVarEnv
flattenPmVarEnv env = mapVarEnv (exprDeepLookup env) env

-- | Solve a complex equality (top-level).
solveOneEq :: TmState -> ComplexEq -> Maybe TmState
solveOneEq solver_state complex
  = solveComplexEq solver_state                -- do the actual *merging* with existing solver_state
  $ simplifyComplexEq                          -- simplify as much as you can
  $ applySubstComplexEq (ts_env state) complex -- replace everything we already know

-- | Solve a complex equality.
-- Nothing => definitely unsatisfiable
-- Just tms => I have added the complex equality and added
--             it to the tmstate; the result may or may not be
--             satisfiable
solveComplexEq :: TmState -> ComplexEq -> Maybe TmState
solveComplexEq solver_state eq@(Cplx e1 e2) = case (e1, e2) of
  -- We cannot do a thing about these cases
  (PmExprOther _,_)            -> Just (markUnhandled solver_state)
  (_,PmExprOther _)            -> Just (markUnhandled solver_state)

  (PmExprLit l1, PmExprLit l2) -> case eqPmLit l1 l2 of
    -- See Note [Undecidable Equality for Overloaded Literals]
    True  -> Just solver_state
    False -> Nothing

  (PmExprCon c1 ts1, PmExprCon c2 ts2)
    | c1 == c2  -> foldlM solveComplexEq solver_state (zip ts1 ts2)
    | otherwise -> Nothing
  (PmExprCon _ [], PmExprEq t1 t2)
    | isTruePmExpr e1  -> solveComplexEq solver_state (t1, t2)
    | isFalsePmExpr e1 -> Just (deferComplexEq eq solver_state)
  (PmExprEq t1 t2, PmExprCon _ [])
    | isTruePmExpr e2   -> solveComplexEq solver_state (t1, t2)
    | isFalsePmExpr e2  -> Just (deferComplexEq eq solver_state)

  (PmExprVar x, PmExprVar y)
    | x == y    -> Just solver_state
    | otherwise -> extendSubstAndSolve x e2 solver_state

  (PmExprVar x, _) -> extendSubstAndSolve x e2 solver_state
  (_, PmExprVar x) -> extendSubstAndSolve x e1 solver_state

  (PmExprEq _ _, PmExprEq _ _) -> Just (deferComplexEq eq solver_state)

  _ -> WARN( True, text "solveComplexEq: Catch all" <+> ppr eq )
       Just (markUnhandled solver_state) -- I HATE CATCH-ALLS

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
    new_env              = env { toe_subst = extendVarEnv (toe_subst env) x e }
    new_incr_state       = state { ts_standby = unchanged, ts_env = new_env }

-- | When we know that a variable is fresh, we do not actually have to
-- check whether anything changes, we know that nothing does. Hence,
-- `extendSubst` simply extends the substitution, unlike what
-- `extendSubstAndSolve` does.
extendSubst :: Id -> PmExpr -> TmState -> TmState
extendSubst x e state
  | isNotPmExprOther simpl_e
  = state { ts_env = env { toe_subst = extendVarEnv (toe_subst env) x simpl_e))
  | otherwise = markUnhandled state
  where
    env = ts_env state
    simpl_e = fst $ simplifyPmExpr $ exprDeepLookup env e

-- | Simplify a complex equality.
simplifyComplexEq :: ComplexEq -> ComplexEq
simplifyComplexEq (Cplx e1 e2) = Cplx (fst $ simplifyPmExpr e1) (fst $ simplifyPmExpr e2)

-- | Simplify an expression. The boolean indicates if there has been any
-- simplification or if the operation was a no-op.
simplifyPmExpr :: PmExpr -> (PmExpr, Bool)
-- See Note [Deep equalities]
simplifyPmExpr e = case e of
  PmExprCon c ts -> case mapAndUnzip simplifyPmExpr ts of
                      (ts', bs) -> (PmExprCon c ts', or bs)
  PmExprEq t1 t2 -> simplifyEqExpr t1 t2
  _other_expr    -> (e, False) -- the others are terminals

-- | Simplify an equality expression. The equality is given in parts.
simplifyEqExpr :: PmExpr -> PmExpr -> (PmExpr, Bool)
-- See Note [Deep equalities]
simplifyEqExpr e1 e2 = case (e1, e2) of
  -- Varables
  (PmExprVar x, PmExprVar y)
    | x == y -> (truePmExpr, True)

  -- Literals
  (PmExprLit l1, PmExprLit l2) -> case eqPmLit l1 l2 of
    -- See Note [Undecidable Equality for Overloaded Literals]
    True  -> (truePmExpr,  True)
    False -> (falsePmExpr, True)

  -- Can potentially be simplified
  (PmExprEq {}, _) -> case (simplifyPmExpr e1, simplifyPmExpr e2) of
    ((e1', True ), (e2', _    )) -> simplifyEqExpr e1' e2'
    ((e1', _    ), (e2', True )) -> simplifyEqExpr e1' e2'
    ((e1', False), (e2', False)) -> (PmExprEq e1' e2', False) -- cannot progress
  (_, PmExprEq {}) -> case (simplifyPmExpr e1, simplifyPmExpr e2) of
    ((e1', True ), (e2', _    )) -> simplifyEqExpr e1' e2'
    ((e1', _    ), (e2', True )) -> simplifyEqExpr e1' e2'
    ((e1', False), (e2', False)) -> (PmExprEq e1' e2', False) -- cannot progress

  -- Constructors
  (PmExprCon c1 ts1, PmExprCon c2 ts2)
    | c1 == c2 ->
        let (ts1', bs1) = mapAndUnzip simplifyPmExpr ts1
            (ts2', bs2) = mapAndUnzip simplifyPmExpr ts2
            (tss, _bss) = zipWithAndUnzip simplifyEqExpr ts1' ts2'
            worst_case  = PmExprEq (PmExprCon c1 ts1') (PmExprCon c2 ts2')
        in  if | not (or bs1 || or bs2) -> (worst_case, False) -- no progress
               | all isTruePmExpr  tss  -> (truePmExpr, True)
               | any isFalsePmExpr tss  -> (falsePmExpr, True)
               | otherwise              -> (worst_case, False)
    | otherwise -> (falsePmExpr, True)

  -- We cannot do anything about the rest..
  _other_equality -> (original, False)

  where
    original = PmExprEq e1 e2 -- reconstruct equality

-- | Apply an (un-flattened) substitution to a simple equality.
applySubstComplexEq :: PmVarEnv -> ComplexEq -> ComplexEq
applySubstComplexEq env (e1,e2) = (exprDeepLookup env e1, exprDeepLookup env e2)

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

-- | Type of a PmLit
pmLitType :: PmLit -> Type -- should be in PmExpr but gives cyclic imports :(
pmLitType (PmSLit   lit) = hsLitType   lit
pmLitType (PmOLit _ lit) = overLitType lit

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
