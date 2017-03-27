{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CallArity.FrameworkBuilder
  ( FrameworkNode
  , TransferFunction
  , ChangeDetector
  , Worklist.alwaysChangeDetector
  , DataFlowFramework
  , buildFramework
  , Worklist.runFramework
  , RequestedPriority (..)
  , registerTransferFunction
  , dependOnWithDefault
  ) where

import CallArity.Types
import qualified Worklist

import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.Map.Strict   (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import VarEnv
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans.State.Strict

newtype FrameworkNode
  = FrameworkNode Int
  deriving (Show, Eq, Ord, Outputable)

type TransferFunction a = Worklist.TransferFunction (FrameworkNode, Arity) AnalResult a
type ChangeDetector = Worklist.ChangeDetector (FrameworkNode, Arity) AnalResult
type DataFlowFramework = Worklist.DataFlowFramework (FrameworkNode, Arity) AnalResult
-- | Maps @FrameworkNode@ to incoming usage dependent @TransferFunction'@s
type NodeTransferEnv = IntMap (Arity -> TransferFunction AnalResult, ChangeDetector)

newtype FrameworkBuilder a
  = FB { unFB :: State NodeTransferEnv a }
  deriving (Functor, Applicative, Monad)

buildFramework :: FrameworkBuilder a -> (a, DataFlowFramework)
buildFramework (FB state) = (res, DFF dff)
  where
    (res, env) = runState state IntMap.empty -- NodeTransferEnv
    dff (FrameworkNode node, arity) = case IntMap.lookup node env of
      Nothing -> pprPanic "CallArity.buildFramework" (ppr node)
      Just (transfer, detectChange) -> (transfer arity, detectChange)

data RequestedPriority
  = LowerThan FrameworkNode
  | HighestAvailable

registerTransferFunction
  :: RequestedPriority
  -> (FrameworkNode -> FrameworkBuilder (a, (Arity -> TransferFunction' AnalResult, ChangeDetector')))
  -> FrameworkBuilder a
registerTransferFunction prio f = FB $ do
  nodes <- get
  let node = case prio of
        HighestAvailable -> 2 * IntMap.size nodes
        LowerThan (FrameworkNode node)
          | not (IntMap.member (node - 1) nodes) -> node - 1
          | otherwise -> pprPanic "registerTransferFunction" (text "There was already a node registered with priority" <+> ppr (node - 1))
  (result, _) <- mfix $ \~(_, entry) -> do
    -- Using mfix so that we can spare an unnecessary Int counter in the state.
    -- Also because @f@ needs to see its own node in order to define its
    -- transfer function in case of letrec.
    modify' (IntMap.insert node entry)
    unFB (f (FrameworkNode node))
  return result

dependOnWithDefault :: AnalResult -> (FrameworkNode, Arity) -> TransferFunction AnalResult
dependOnWithDefault def which = do
  --pprTrace "dependOnWithDefault:before" (text "node:" <+> ppr node <+> text "arity:" <+> ppr arity) $ return ()
  res <- fromMaybe def <$> Worklist.dependOn which
  --pprTrace "dependOnWithDefault:after" (vcat [text "node:" <+> ppr node, text "arity:" <+> ppr arity, text "res:" <+> ppr res]) $ return ()
  return res
