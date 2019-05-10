{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module CoreSet (
    CoreSet,
    emptyCoreSet, elemCoreSet, mkCoreSet, extendCoreSet,
    extendCoreSetList, unionCoreSet, coreSetElems
  ) where

import GhcPrelude

import Data.List (foldl')
import Data.Maybe (isJust)
import CoreMap
import CoreSyn

{-
coreSetFreeIdsList :: CoreSet -> [Id]
coreSetFreeIdsList cs =
  fvVarList $ filterFV isLocalId $ foldTM (unionFV . exprFVs) cs emptyFV
-}

-- | Invariant: We map to the key with which we index the 'CoreMap' in order for
-- 'foldTM' to provide us with the key. Yuck.
newtype CoreSet = CoreSet (CoreMap CoreExpr)

emptyCoreSet :: CoreSet
emptyCoreSet = CoreSet emptyCoreMap

elemCoreSet :: CoreSet -> CoreExpr -> Bool
elemCoreSet (CoreSet m) e = isJust (lookupCoreMap m e)

extendCoreSet :: CoreSet -> CoreExpr -> CoreSet
extendCoreSet (CoreSet m) e = CoreSet (extendCoreMap m e e)

extendCoreSetList :: CoreSet -> [CoreExpr] -> CoreSet
extendCoreSetList = foldl' extendCoreSet

unionCoreSet :: CoreSet -> CoreSet -> CoreSet
unionCoreSet (CoreSet a) (CoreSet b) = CoreSet (unionWithTM const a b)

mkCoreSet :: [CoreExpr] -> CoreSet
mkCoreSet = extendCoreSetList emptyCoreSet

coreSetElems :: CoreSet -> [CoreExpr]
coreSetElems (CoreSet m) = foldCoreMap (:) [] m