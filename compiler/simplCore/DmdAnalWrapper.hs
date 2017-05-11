{-# LANGUAGE CPP #-}

module DmdAnalWrapper (combinedDmdAnalProgram) where

#include "HsVersions.h"

import CallArity
import CoreSyn
import Demand
import DmdAnal
import DynFlags
import FamInstEnv
import Id
import Outputable
import Util
import Usage
import Var

combinedDmdAnalProgram :: DynFlags -> FamInstEnvs -> CoreProgram -> IO CoreProgram
combinedDmdAnalProgram dflags fams prog = do
  -- Call Arity first, suggesting the fact that there's no information flow
  -- from DA to CA. There isn't from CA to DA either, of course.
  prog' <- callArityAnalProgram dflags fams prog
  prog'' <- dmdAnalProgram dflags fams prog'
  --pprTrace "Program" (ppr prog'') $ pure ()
  return (mapBndrsProgram mergeInfo prog'')

mergeInfo :: Var -> Var
mergeInfo id
  | isTyVar id
  = id
  | otherwise
  = ASSERT2( isExportedId id || ca_usage `leqUsage` old_usage, text "Usage should never be less precise:" <+> ppr id <+> text "old:" <+> ppr old_usage <+> text "ca:" <+> ppr ca_usage <+> text "new:" <+> ppr new_demand )
    ASSERT2( not (isExportedId id) || ca_usg_sig `leqUsageSig` old_usg_sig, text "UsageSig should never be less precise:" <+> ppr id <+> text "old:" <+> ppr old_usg_sig <+> text "ca:" <+> ppr ca_usg_sig <+> text "new:" <+> ppr new_str_sig )
    --(if idCallArity id == Absent then pprTrace "Absent" (ppr id) else \x -> x) $
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

    new_demand = overwriteDemandWithUsage ca_usage old_demand
    new_str_sig = overwriteStrictSigWithUsageSig ca_usg_sig old_str_sig

    leqUsage l r = l `lubUsage` r == r
    leqUsageSig l r = l `lubUsageSig` r == r
    id'
      | isExportedId id = id `setIdStrictness` new_str_sig -- Only the sig matters
      | otherwise = id `setIdDemandInfo` new_demand -- Only use sites matter


mapBndrsProgram :: HasCallStack => (Var -> Var) -> CoreProgram -> CoreProgram
mapBndrsProgram f = map (mapBndrsBind f)

mapBndrsBind :: HasCallStack => (Var -> Var) -> CoreBind -> CoreBind
mapBndrsBind f (NonRec id e) = NonRec (f id) (mapBndrsExprIfNotAbsent id f e)
mapBndrsBind f (Rec bndrs) = Rec (map (\(id, e) -> (f id, mapBndrsExprIfNotAbsent id f e)) bndrs)

mapBndrsExprIfNotAbsent :: HasCallStack => Var -> (Var -> Var) -> CoreExpr -> CoreExpr
mapBndrsExprIfNotAbsent id f e
  | Absent <- idCallArity id = e -- we won't have analysed e in this case.
  | otherwise = mapBndrsExpr f e

mapBndrsExpr :: HasCallStack => (Var -> Var) -> CoreExpr -> CoreExpr
mapBndrsExpr f e = case e of
  App func arg -> App (mapBndrsExpr f func) (mapBndrsExpr f arg)
  Lam id e -> Lam (f id) (mapBndrsExpr f e)
  Let bind body -> Let (mapBndrsBind f bind) (mapBndrsExpr f body)
  Case scrut id ty alts -> Case (mapBndrsExpr f scrut) (f id) ty (map (mapBndrsAlt f) alts)
  Cast e co -> Cast (mapBndrsExpr f e) co
  Tick t e -> Tick t (mapBndrsExpr f e)
  Var _ -> e -- use sites carry no important annotations
  _ -> e

mapBndrsAlt :: HasCallStack => (Var -> Var) -> Alt CoreBndr -> Alt CoreBndr
mapBndrsAlt f (con, bndrs, e) = (con, map f bndrs, mapBndrsExpr f e)
