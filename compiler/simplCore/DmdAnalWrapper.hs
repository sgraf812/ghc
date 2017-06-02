{-# LANGUAGE CPP #-}

module DmdAnalWrapper (combinedDmdAnalProgram) where

#include "HsVersions.h"

import CallArity
import CoreSyn
import DmdAnal
import DynFlags
import FamInstEnv
import Id
import Outputable
import Usage
import Util
import Var

combinedDmdAnalProgram :: DynFlags -> FamInstEnvs -> [CoreRule] -> CoreProgram -> IO CoreProgram
combinedDmdAnalProgram dflags fams orphan_rules prog = do
  -- Call Arity first, suggesting the fact that there's no information flow
  -- from DA to CA. There isn't from CA to DA either, of course.
  prog' <- callArityAnalProgram dflags fams orphan_rules prog
  prog'' <- dmdAnalProgram dflags fams prog'
  --pprTrace "Program" (ppr prog'') $ pure ()
  return (mapBndrsProgram mergeInfo prog'')

mergeInfo :: Bool -> Var -> Var
mergeInfo is_lam_bndr id
  | isTyVar id
  = id
  | otherwise 
  -- Since LetDown analyzes the RHS stripped-off of lambdas only once with U 
  -- instead of the whole expression, we get more conservative results in our
  -- new analysis, where there might be multiplied uses on lambda binders if
  -- it has more than one lambda. In that case we have to relax the assert.
  = ASSERT2( (is_lam_bndr || isExportedId id || ca_usage `leqUsage` old_usage), text "Usage should never be less precise:" <+> ppr id <+> text "old:" <+> ppr old_usage <+> text "ca:" <+> ppr ca_usage <+> text "new:" <+> ppr new_demand )
    ASSERT2( (not (isExportedId id) || ca_usg_sig `leqUsageSig` old_usg_sig), text "UsageSig should never be less precise:" <+> ppr id <+> text "old:" <+> ppr old_usg_sig <+> text "ca:" <+> ppr ca_usg_sig <+> text "new:" <+> ppr new_str_sig )
    --pprTrace "mergeInfo" (ppr id <+> text "Demand:" <+> ppr old_demand <+> ppr ca_usage <+> ppr new_demand <+> text "Strictness" <+> ppr old_str_sig <+> ppr ca_usg_sig <+> ppr new_str_sig) $
    id'
  where
    -- We merge idDemandInfo with idCallArity and idStrictness with idArgUsage.
    -- Since Demand.hs doesn't seem to enforce the equivalences from the paper,
    -- we first convert everything to the representation of Usage.hs.
    old_demand = idDemandInfo id
    old_str_sig = idStrictness id
    ca_usage = idCallArity id
    ca_usg_sig = idArgUsage id

    old_usage = usageFromDemand old_demand
    old_usg_sig = usageSigFromStrictSig old_str_sig

    new_demand 
      | ca_usage `leqUsage` old_usage = overwriteDemandWithUsage ca_usage old_demand
      | otherwise = old_demand
    new_str_sig 
      | ca_usg_sig `leqUsageSig` old_usg_sig = overwriteStrictSigWithUsageSig ca_usg_sig old_str_sig
      | otherwise = old_str_sig

    leqUsage l r = l `lubUsage` r == r
    leqUsageSig l r = l `lubUsageSig` r == r
    id'
      | isExportedId id = id `setIdStrictness` new_str_sig -- Only the sig matters
      | otherwise = id `setIdDemandInfo` new_demand -- Only use sites matter


mapBndrsProgram :: (Bool -> Var -> Var) -> CoreProgram -> CoreProgram
mapBndrsProgram f = map (mapBndrsBind f)

mapBndrsBind :: (Bool -> Var -> Var) -> CoreBind -> CoreBind
mapBndrsBind f (NonRec id e) = NonRec (f False id) (mapBndrsExprIfNotAbsent id f e)
mapBndrsBind f (Rec bndrs) = Rec (map (\(id, e) -> (f False id, mapBndrsExprIfNotAbsent id f e)) bndrs)

mapBndrsExprIfNotAbsent :: Var -> (Bool -> Var -> Var) -> CoreExpr -> CoreExpr
mapBndrsExprIfNotAbsent id f e
  | Absent <- idCallArity id = e -- we won't have analysed e in this case.
  | otherwise = mapBndrsExpr f e

mapBndrsExpr :: (Bool -> Var -> Var) -> CoreExpr -> CoreExpr
mapBndrsExpr f e = case e of
  App func arg -> App (mapBndrsExpr f func) (mapBndrsExpr f arg)
  Lam id e -> Lam (f True id) (mapBndrsExpr f e)
  Let bind body -> Let (mapBndrsBind f bind) (mapBndrsExpr f body)
  Case scrut id ty alts -> Case (mapBndrsExpr f scrut) (f False id) ty (map (mapBndrsAlt f) alts)
  Cast e co -> Cast (mapBndrsExpr f e) co
  Tick t e -> Tick t (mapBndrsExpr f e)
  Var _ -> e -- use sites carry no important annotations
  _ -> e

mapBndrsAlt :: (Bool -> Var -> Var) -> Alt CoreBndr -> Alt CoreBndr
mapBndrsAlt f (con, bndrs, e) = (con, map (f False) bndrs, mapBndrsExpr f e)
