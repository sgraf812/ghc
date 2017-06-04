{-# LANGUAGE CPP #-}

module DmdAnalWrapper (combinedDmdAnalProgram) where

#include "HsVersions.h"

import BasicTypes
import CallArity
import CoreArity
import CoreSyn
import Demand
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

type InfoMerger = TopLevelFlag -> Bool -> Var -> Var

mergeInfo :: InfoMerger
mergeInfo top_lvl is_lam_bndr id
  | isTyVar id
  = id
  | otherwise 
  -- Since LetDown analyzes the RHS stripped-off of lambdas only once with U 
  -- instead of the whole expression, we get more conservative results in our
  -- new analysis, where there might be multiplied uses on lambda binders if
  -- it has more than one lambda. In that case we have to relax the assert.
  = ASSERT2( (is_lam_bndr || not has_usage || ca_usage `leqUsage` old_usage), text "Usage should never be less precise:" <+> ppr id <+> text "old:" <+> ppr old_usage <+> text "ca:" <+> ppr ca_usage <+> text "new:" <+> ppr new_demand )
    ASSERT2( (not has_usg_sig || ca_usg_sig `leqUsageSig` old_usg_sig), text "UsageSig should never be less precise:" <+> ppr id <+> text "old:" <+> ppr old_usg_sig <+> text "ca:" <+> ppr ca_usg_sig <+> text "new:" <+> ppr new_str_sig )
    --pprTrace "mergeInfo" (ppr id <+> text "Demand:" <+> ppr old_demand <+> ppr ca_usage <+> ppr new_demand <+> text "Strictness" <+> ppr old_str_sig <+> ppr ca_usg_sig <+> ppr new_str_sig) $
    id'
  where
    max_arity = length (typeArity (idType id))
    -- We merge idDemandInfo with idCallArity and idStrictness with idArgUsage.
    -- Since Demand.hs doesn't seem to enforce the equivalences from the paper,
    -- we first convert everything to the representation of Usage.hs.
    old_demand = idDemandInfo id
    old_str_sig = idStrictness id
    (old_arg_dmds, _) = splitStrictSig old_str_sig
    ca_usage = idCallArity id
    ca_usg_sig = idArgUsage id

    old_usage = usageFromDemand old_demand
    -- trimming the sig so that we don't care for arguments which aren't there
    -- as dictated by the types (e.g. when a sig bottoms out after 2 arguments 
    -- and the id's type only has two arrows).
    old_usg_sig = trimUsageSig max_arity (usageSigFromStrictSig old_str_sig) 

    new_demand 
      | ca_usage `leqUsage` old_usage = overwriteDemandWithUsage ca_usage old_demand
      | otherwise = old_demand
    new_str_sig 
      | ca_usg_sig `leqUsageSig` old_usg_sig 
      , idArity id <= length old_arg_dmds
      -- This is only safe if DmdAnal used the same arity as CallArity.
      -- Otherwise we get into nasty situations where arity /= #top-level binders,
      -- like with IO's RealWorld tokens. In that situation we have
      -- a more precise usage signature, but at the cost of a higher arity.
      -- Which is OK, since arity analysis determined that there didn't
      -- happen anything before.
      = overwriteStrictSigWithUsageSig ca_usg_sig old_str_sig
      | otherwise = old_str_sig

    leqUsage l r = l `lubUsage` r == r
    leqUsageSig l r = l `lubUsageSig` r == r
    has_usage = idCallArity id /= topUsage || old_usage /= topUsage
    has_usg_sig = isTopLevel top_lvl
    id' = id 
      `setIdDemandInfo` new_demand
      `setIdStrictness` new_str_sig


mapBndrsProgram :: InfoMerger -> CoreProgram -> CoreProgram
mapBndrsProgram f = map (mapBndrsBind TopLevel f)

mapBndrsBind :: TopLevelFlag -> InfoMerger -> CoreBind -> CoreBind
mapBndrsBind top_lvl f (NonRec id e) = NonRec (f top_lvl False id) (mapBndrsExpr f e)
mapBndrsBind top_lvl f (Rec bndrs) = Rec (map (\(id, e) -> (f top_lvl False id, mapBndrsExpr f e)) bndrs)

mapBndrsExpr :: InfoMerger -> CoreExpr -> CoreExpr
mapBndrsExpr f e = case e of
  App func arg -> App (mapBndrsExpr f func) (mapBndrsExpr f arg)
  Lam id e -> Lam (f NotTopLevel True id) (mapBndrsExpr f e)
  Let bind body -> Let (mapBndrsBind NotTopLevel f bind) (mapBndrsExpr f body)
  Case scrut id ty alts -> Case (mapBndrsExpr f scrut) (f NotTopLevel False id) ty (map (mapBndrsAlt f) alts)
  Cast e co -> Cast (mapBndrsExpr f e) co
  Tick t e -> Tick t (mapBndrsExpr f e)
  Var _ -> e -- use sites carry no important annotations
  _ -> e

mapBndrsAlt :: InfoMerger -> Alt CoreBndr -> Alt CoreBndr
mapBndrsAlt f (con, bndrs, e) = (con, map (f NotTopLevel False) bndrs, mapBndrsExpr f e)
