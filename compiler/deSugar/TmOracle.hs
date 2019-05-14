{-
Author: George Karachalias <george.karachalias@cs.kuleuven.be>

The term equality oracle. The main export of the module is function `tmOracle'.
-}

{-# LANGUAGE CPP, MultiWayIf, GeneralisedNewtypeDeriving, PatternSynonyms #-}

module TmOracle (

    -- the term oracle
    tmOracle, TmState, initialTmState, solveComplexEq, canDiverge,

    -- misc.
    SimpleEq (..), ComplexEq (..), toComplex
  ) where

#include "HsVersions.h"

import GhcPrelude

import Id
import MonadUtils
import Outputable
import Control.Applicative ((<|>))

import UniqSupply
import VarEnv
import CoreOpt (exprIsConApp_maybe)
import CoreUtils (exprIsCheap, cheapEqExpr')
import CoreSyn
import CoreMap
import CoreSet
import Equivalence (Equivalence, Rep)
import qualified Equivalence

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

type Class = (Maybe CoreExpr, CoreSet)

data Equalities = E
  { e_eq   :: !(Equivalence Class)
  , e_reps :: !(CoreMap Rep)
  }

emptyEqualities :: UniqSupply -> Equalities
emptyEqualities us = E (Equivalence.empty us) emptyTM

-- | Not quite the same as 'exprIsHNF'... Only literals and saturated
-- constructor applications, modulo ticks and coercions, are considered values
exprIsValue :: InScopeEnv -> CoreExpr -> Bool
exprIsValue ise e
  | Just _ <- exprIsConApp_maybe ise e
  = True
exprIsValue ise (Tick _ e)     = exprIsValue ise e
exprIsValue ise (Cast e _)     = exprIsValue ise e
exprIsValue ise (App e Type{}) = exprIsValue ise e
exprIsValue _ (Lit _)        = True
exprIsValue _ _              = False

exprIsValue_maybe :: InScopeEnv -> CoreExpr -> Maybe CoreExpr
exprIsValue_maybe ise e
  | exprIsValue ise e = Just e
  | otherwise                  = Nothing

unitClass :: InScopeEnv -> CoreExpr -> Class
unitClass ise e = (exprIsValue_maybe ise e, mkCoreSet [e])

-- | Merges two classes under the premise that their solutions aren't
-- contradictory.
mergeClasses :: Class -> Class -> Class
mergeClasses (soll, setl) (solr, setr) = (soll <|> solr, unionCoreSet setl setr)

-- | Adds a 'ComplexEq' to our knowledge base by merging equivalence classes,
-- creating them if needed. Also takes care of merging solutions by just
-- favoring left-biased. So make sure not to add contradictory rigid-rigid
-- equations here, the knowledge will be lost thereafter!
addEquality :: InScopeEnv -> ComplexEq -> Equalities -> Equalities
addEquality ise (Cplx l r) es@E{ e_eq = eq, e_reps = reps } =
  case (lookupCoreMap reps l, lookupCoreMap reps r) of
    (Just rl, Just rr) -> es { e_eq = Equivalence.equate mergeClasses rl rr eq }
    (Just rl, Nothing) -> add_to_equiv r rl
    (Nothing, Just rr) -> add_to_equiv l rr
    (Nothing, Nothing) ->
      let cls          = mergeClasses (unitClass ise l) (unitClass ise r)
          (rep, eq')   = Equivalence.newClass cls eq
          reps'        = extendCoreMap (extendCoreMap reps r rep) l rep
      in es { e_eq = eq', e_reps = reps' }
  where
    add_to_equiv e r =
      let reps'        = extendCoreMap reps e r
          eq'          = Equivalence.modify (mergeClasses (unitClass ise e)) r eq
      in es { e_reps = reps', e_eq = eq' }

-- | Check if we have knowledge that the given term is surely terminating.
-- For that to be true, it's sufficient to check its equivalence class has any
-- term that is in WHNF or cheap to get there.
exprSurelyTerminates :: CoreExpr -> TmState -> Bool
exprSurelyTerminates e TS{ ts_eqs = E{ e_reps = reps, e_eq = eq } } =
  case lookupCoreMap reps e of
    Nothing -> False
    Just rep ->
      let equal_exprs = coreSetElems $ snd $ fst $ Equivalence.lookup rep eq
          -- variables are cheap, but in our scenario we don't know whether
          -- evaluating them terminates
          terminating (Var _) = False
          terminating e = exprIsCheap e
      in any terminating equal_exprs

-- | Records refutable literals for each identifier. We write \(x ~ E \in
-- \Gamma \) when @E@ is in the 'CoreSet' of @x@ according to the 'RefutEnv'
-- \(\Gamma\).
type RefutEnv = IdEnv (LiteralMap ())

-- | The solver state of the term oracle.
data TmState = TS
  { ts_eqs     :: !Equalities
  , ts_refuts    :: !RefutEnv
  -- ^ When \(x ~ E \in \Gamma\), then we can refute satisfiability as soon as
  -- we can prove that \(x ~ E\). This tracks negative equalities occuring in
  -- case splits. E.g., after the clause guarded by @Nothing <- x@, we know that
  -- @x@ can't be @Nothing@, so we have \(x ~ Nothing \in \Gamma\).
  }

-- | Initial solver_state of the oracle.
initialTmState :: UniqSupply -> TmState
initialTmState us = TS (emptyEqualities us) emptyVarEnv

-- | Adds a 'ComplexEq' to our knowledge base.
deferComplexEq :: InScopeEnv -> ComplexEq -> TmState -> TmState
deferComplexEq ise eq st = st { ts_eqs = addEquality ise eq (ts_eqs st) }

-- | Check whether a constraint (x ~ BOT) can succeed,
-- given the resulting solver_state of the term oracle.
canDiverge :: Var -> TmState -> Bool
canDiverge x st
  | exprSurelyTerminates (Var x) st
{-
TODO: Does this make sense? I think not... f x ~ g y doesn't make it evaluated,
and f x ~ f 42 does neither.
  -- If it is involved (directly or indirectly) in any equality in the
  -- worklist, we can assume that it is already indirectly evaluated,
  -- as a side-effect of equality checking. If not, then we can assume
  -- that the constraint is satisfiable.
  = not $ any (isForcedByEq x) standby || any (isForcedByEq y) standby
  where
    isForcedByEq :: Name -> ComplexEq -> Bool
    isForcedByEq y (Cplx e1 e2) = varIn y e1 || varIn y e2
-}
  = False
  | otherwise
  = True

-- | Determine if the given expression is known to be equivalent to a value
-- and if so, return its solution.
hasValue_maybe :: Equalities -> CoreExpr -> Maybe CoreExpr
hasValue_maybe E{ e_eq = eq, e_reps = reps } x =
  fst . fst . flip Equivalence.lookup eq =<< lookupCoreMap reps x

-- | Attempt to solve a complex equality.
-- Nothing => definitely unsatisfiable
-- Just tms => I have added the complex equality and added
--             it to the tmstate; the result may or may not be
--             satisfiable
solveComplexEq :: InScopeEnv -> TmState -> ComplexEq -> Maybe TmState
solveComplexEq ise solver_state eq@(Cplx e1 e2) =
  if
    | (Lit l1, Lit l2) <- (e1, e2)
    , l1 /= l2
    -> unsat
    | cheapEqExpr' (const True) e1 e2
    -> solved
    -- TODO: Extend this to non-empty floats?
    | Just (_, [], con1, _, ts1) <- exprIsConApp_maybe ise e1
    , Just (_, [], con2, _, ts2) <- exprIsConApp_maybe ise e2
    -> if con1 == con2
          then foldlM (solveComplexEq ise) solver_state (zipWith Cplx ts1 ts2)
          else unsat
    | Just e1' <- hasValue_maybe (ts_eqs solver_state) e1
    -> solveComplexEq ise solver_state (Cplx e1' e2)
    | Just e2' <- hasValue_maybe (ts_eqs solver_state) e2
    -> solveComplexEq ise solver_state (Cplx e1 e2')
    | otherwise
    -> defer -- TODO: Does this satisfy the requirements of addEquality? Probably, both sides won't be
  where
    solved    = Just solver_state
    defer     = Just (deferComplexEq ise eq solver_state)
    unsat     = Nothing

-- | External interface to the term oracle.
tmOracle :: InScopeEnv -> TmState -> [ComplexEq] -> Maybe TmState
tmOracle ise tm_state eqs = foldlM (solveComplexEq ise) tm_state eqs