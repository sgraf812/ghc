{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CallArity.FrameworkBuilder
  ( FrameworkNode
  , TransferFunction
  , ChangeDetector
  , Worklist.alwaysChangeDetector
  , DataFlowFramework
  , FrameworkBuilder
  , RequestedPriority (..)
  , registerTransferFunction
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

data RequestedPriority
  = LowerThan !FrameworkNode
  | HighestAvailable

registerTransferFunction
  :: RequestedPriority
  -> (FrameworkNode -> FrameworkBuilder (a, (SingleUse -> TransferFunction AnalResult, ChangeDetector)))
  -> FrameworkBuilder a
registerTransferFunction prio f = FB $ do
  nodes <- get
  let node = case prio of
        HighestAvailable -> 2 * IntMap.size nodes
        LowerThan (FrameworkNode node)
          | not (IntMap.member (node - 1) nodes) -> node - 1
          | otherwise -> pprPanic
            "CallArity.FrameworkBuilder.registerTransferFunction"
            (text "There was already a node registered with priority" <+> ppr (node - 1))
  (result, _) <- mfix $ \ ~(_, entry) -> do
    -- Using mfix so that we can spare an unnecessary Int counter in the state.
    -- Also because @f@ needs to see its own node in order to define its
    -- transfer function in case of letrec.
    modify' (IntMap.insert node entry)
    unFB (f (FrameworkNode node))
  return result

dependOnWithDefault :: AnalResult -> (FrameworkNode, SingleUse) -> TransferFunction AnalResult
dependOnWithDefault def which = do
  --which <- pprTrace "dependOnWithDefault:before" (ppr which) (return which)
  res <- fromMaybe def <$> Worklist.dependOn which
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
