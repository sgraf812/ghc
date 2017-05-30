{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CallArity.FrameworkBuilder
  ( FrameworkNode
  , TransferFunction
  , ChangeDetector
  , Worklist.alwaysChangeDetector
  , DataFlowFramework
  , FrameworkBuilder
  , registerTransferFunction
  , monotonize
  , dependOnWithDefault
  , buildAndRun
  ) where

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

type TransferFunction a = Worklist.TransferFunction (FrameworkNode, SingleUse) AnalResult a
type ChangeDetector = Worklist.ChangeDetector (FrameworkNode, SingleUse) AnalResult
type DataFlowFramework = Worklist.DataFlowFramework (FrameworkNode, SingleUse) AnalResult
-- | Maps @FrameworkNode@ to incoming usage dependent @TransferFunction@s
type NodeTransferEnv = IntMap (SingleUse -> TransferFunction AnalResult, ChangeDetector)

newtype FrameworkBuilder a
  = FB { unFB :: State NodeTransferEnv a }
  deriving (Functor, Applicative, Monad)

buildFramework :: FrameworkBuilder a -> (a, DataFlowFramework)
buildFramework (FB state) = (res, Worklist.DFF dff)
  where
    (res, env) = runState state IntMap.empty -- NodeTransferEnv
    dff (FrameworkNode node, use) = case IntMap.lookup node env of
      Nothing -> pprPanic "CallArity.FrameworkBuilder.buildFramework" (ppr node)
      Just (transfer, detectChange) -> (transfer use, detectChange)

registerTransferFunction
  :: (FrameworkNode -> FrameworkBuilder (a, (SingleUse -> TransferFunction AnalResult, ChangeDetector)))
  -> FrameworkBuilder a
registerTransferFunction f = FB $ do
  nodes <- get
  let node = IntMap.size nodes
  (result, _) <- mfix $ \ ~(_, entry) -> do
    -- Using mfix so that we can spare an unnecessary Int counter in the state.
    -- Also because @f@ needs to see its own node in order to define its
    -- transfer function in case of letrec.
    modify' (IntMap.insert node entry)
    unFB (f (FrameworkNode node))
  return result

monotonize
  :: FrameworkNode
  -> (SingleUse -> TransferFunction AnalResult)
  -> SingleUse -> TransferFunction AnalResult
monotonize node transfer use = do
  (ut_new, e') <- transfer use 
  (ut_old, _) <- fromMaybe (botUsageType, undefined) <$> Worklist.unsafePeekValue (node, use)
  return (lubUsageType ut_new ut_old, e')

dependOnWithDefault :: AnalResult -> (FrameworkNode, SingleUse) -> TransferFunction AnalResult
dependOnWithDefault def which = do
  --which <- pprTrace "dependOnWithDefault:before" (ppr which) (return which)
  res <- fromMaybe def <$> Worklist.dependOn which
  --res <- pprTrace "dependOnWithDefault:after " (ppr which) (return res)
  return res

buildAndRun :: FrameworkBuilder (SingleUse -> TransferFunction AnalResult) -> SingleUse -> AnalResult
buildAndRun buildTransfer use = lookup_result (Worklist.runFramework fw (Set.singleton (node, use)))
  where
    (node, fw) = buildFramework $ registerTransferFunction $ \node -> do
      transfer <- buildTransfer
      return (node, (transfer, Worklist.alwaysChangeDetector))

    lookup_result :: Map (FrameworkNode, SingleUse) AnalResult -> AnalResult
    lookup_result result_map = case Map.lookup (node, use) result_map of
      Nothing -> pprPanic "CallArity.FrameworkBuilder.buildAndRun" empty
      Just res -> res
