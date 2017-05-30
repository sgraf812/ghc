{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

module CallArity.FrameworkBuilder
  ( FrameworkNode
  , TransferFunction
  , ChangeDetector
  , Worklist.alwaysChangeDetector
  , DataFlowFramework
  , FrameworkBuilder
  , RequestedPriority (..)
  , registerTransferFunction
  , registerAnnotationFunction
  , dependOnWithDefault
  , buildAndRun
  ) where

#include "HsVersions.h"

import CallArity.Types
import Outputable
import Usage
import qualified Worklist

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.Map.Strict   (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe
import Control.Monad.Fix
import Control.Monad.Trans.State.Strict

newtype FrameworkNode
  = FrameworkNode Int
  deriving (Show, Eq, Ord, Outputable)

type TransferFunction a = Worklist.TransferFunction (FrameworkNode, SingleUse) (Either UsageType CoreExpr) a
type ChangeDetector = Worklist.ChangeDetector (FrameworkNode, SingleUse) (Either UsageType CoreExpr)
type DataFlowFramework = Worklist.DataFlowFramework (FrameworkNode, SingleUse) (Either UsageType CoreExpr)
-- | Maps @FrameworkNode@ to incoming usage dependent @TransferFunction@s
type NodeTransferEnv = IntMap (SingleUse -> TransferFunction (Either UsageType CoreExpr))

newtype FrameworkBuilder a
  = FB { unFB :: State NodeTransferEnv a }
  deriving (Functor, Applicative, Monad)

changeDetector :: ChangeDetector
changeDetector _ (Left old) (Left new) =
  ASSERT2( old_sig `leqUsageSig` new_sig, text "CallArity.changeDetector: usage sig not monotone")
  pprTrace "usage sig" empty (old_sig /= new_sig) ||
  ASSERT2( sizeUFM old_uses <= sizeUFM new_uses, text "CallArity.changeDetector: uses not monotone")
  pprTrace "uses count" empty (sizeUFM old_uses /= sizeUFM new_uses) ||
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
changeDetector _ (Right _) (Right _) = True
changeDetector _ _ _ = pprPanic "FrameworkNode should not switch between Left and Right (type error)" empty

buildFramework :: FrameworkBuilder a -> (a, DataFlowFramework)
buildFramework (FB state) = (res, Worklist.DFF dff)
  where
    (res, env) = runState state IntMap.empty -- NodeTransferEnv
    dff (FrameworkNode node, use) = case IntMap.lookup node env of
      Nothing -> pprPanic "CallArity.FrameworkBuilder.buildFramework" (ppr node)
      Just transfer -> (transfer use, changeDetector)

registerTransferFunction 
  :: UsageType 
  -> (FrameworkBuilder (SingleUse -> TransferFunction UsageType, a))
  -> FrameworkBuilder (SingleUse -> TransferFunction UsageType, a)
registerTransferFunction def f = allocateNode $ \node -> do
  (transfer, result) <- f node
  let monotonized_transfer use = do
        Left old_ut <- fromMaybe (Left def) <$> Worklist.unsafePeekValue (node, use)
        ut_new <- transfer use
        return (Left (lubUsageType ut_new ut_old))
  let reference_node use = dependOnWithDefault def (node, use)
  return (monotonized_transfer, (reference_node, result))

registerAnnotationFunction
  :: FrameworkBuilder (SingleUse -> TransferFunction CoreExpr)
  -> FrameworkBuilder FrameworkNode
registerAnnotationFunction fb = registerTransferFunction $ \node -> do
  annotate <- fb
  return (fmap Right . annotate, node)

allocateNode
  :: (FrameworkNode -> FrameworkBuilder (SingleUse -> TransferFunction (Either UsageType CoreExpr), a)
  -> FrameworkBuilder a
allocateNode f = FB $ do
  nodes <- get
  let node = IntMap.size nodes
  (_, result) <- mfix $ \ ~(entry, _) -> do
    -- Using mfix so that we can spare an unnecessary Int counter in the state.
    -- Also because @f@ needs to see its own node in order to define its
    -- transfer function in case of letrec.
    modify' (IntMap.insert node entry)
    unFB (f (FrameworkNode node))
  return result

-- | This should never be called with a node that doesn't return a `UsageType`
-- (e.g. the single top-level node for the annotated `CoreExpr`).
dependOnWithDefault :: UsageType -> (FrameworkNode, SingleUse) -> TransferFunction UsageType
dependOnWithDefault def which = do
  --which <- pprTrace "dependOnWithDefault:before" (ppr which) (return which)
  Left res <- fromMaybe (Left def) <$> Worklist.dependOn which
  --res <- pprTrace "dependOnWithDefault:after " (ppr which) (return res)
  return res

buildAndRun :: FrameworkBuilder (SingleUse -> TransferFunction AnalResult) -> SingleUse -> AnalResult
buildAndRun buildTransfer use = lookup_result (Worklist.runFramework fw (Set.singleton (node, use)))
  where
    (node, fw) = buildFramework $
      registerTransferFunction (LowerThan (FrameworkNode 0)) $ \node -> do
        transfer <- buildTransfer
        return (node, (transfer, Worklist.alwaysChangeDetector))

    lookup_result :: Map (FrameworkNode, SingleUse) AnalResult -> AnalResult
    lookup_result result_map = case Map.lookup (node, use) result_map of
      Nothing -> pprPanic "CallArity.FrameworkBuilder.buildAndRun" empty
      Just res -> res
