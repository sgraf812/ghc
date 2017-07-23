{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Worklist where

import Control.Monad (forM_, when, (<=<))
import Control.Monad.Trans.State.Strict
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Outputable

newtype TransferFunction node lattice a
  = TFM (State (WorklistState node lattice) a)
  deriving (Functor, Applicative, Monad)

type ChangeDetector node lattice
  = Set node -> lattice -> lattice -> Bool

newtype DataFlowFramework node lattice
  = DFF { getTransfer :: node -> (TransferFunction node lattice lattice, ChangeDetector node lattice) }

eqChangeDetector :: Eq lattice => ChangeDetector node lattice
eqChangeDetector _ = (/=)

alwaysChangeDetector :: ChangeDetector node lattice
alwaysChangeDetector _ _ _ = True

frameworkWithEqChangeDetector
  :: Eq lattice
  => (node -> TransferFunction node lattice lattice)
  -> DataFlowFramework node lattice
frameworkWithEqChangeDetector transfer = DFF transfer'
  where
    transfer' node = (transfer node, eqChangeDetector)

data NodeInfo node lattice
  = NodeInfo
  { value :: !(Maybe lattice) -- ^ the value at this node. can be Nothing only when a loop was detected
  , references :: !(Set node) -- ^  nodes this value depends on
  , referrers :: !(Set node) -- ^ nodes depending on this value
  } deriving (Show, Eq)

emptyNodeInfo :: NodeInfo node lattice
emptyNodeInfo = NodeInfo Nothing Set.empty Set.empty

type Graph node lattice = Map node (NodeInfo node lattice)

data WorklistState node lattice
  = WorklistState
  { framework :: !(DataFlowFramework node lattice)
  , graph :: !(Graph node lattice)
  , unstable :: !(Map node (Set node)) -- unstable nodes and their changed references
  , callStack :: !(Set node)
  , referencedNodes :: !(Set node)
  }

zoomGraph :: State (Graph node lattice) a -> State (WorklistState node lattice) a
zoomGraph modifyGraph = state $ \st ->
  let (res, g) = runState modifyGraph (graph st)
  in  (res, st { graph = g })

zoomUnstable :: State (Map node (Set node)) a -> State (WorklistState node lattice) a
zoomUnstable modifyUnstable = state $ \st ->
  let (res, u) = runState modifyUnstable (unstable st)
  in  (res, st { unstable = u })

zoomReferencedNodes :: State (Set node) a -> State (WorklistState node lattice) a
zoomReferencedNodes modifier = state $ \st ->
  let (res, rn) = runState modifier (referencedNodes st)
  in  (res, st { referencedNodes = rn })

initialWorklistState
  :: Map node (Set node)
  -> DataFlowFramework node lattice
  -> WorklistState node lattice
initialWorklistState unstable fw =
  WorklistState fw Map.empty unstable Set.empty Set.empty

dependOn :: Ord node => node -> TransferFunction node lattice (Maybe lattice)
dependOn node = TFM $ do
  loopDetected <- Set.member node <$> gets callStack
  isNotYetStable <- Map.member node <$> gets unstable
  maybeNodeInfo <- Map.lookup node <$> gets graph
  zoomReferencedNodes (modify' (Set.insert node)) -- save that we depend on this value
  case maybeNodeInfo of
    Nothing | loopDetected -> do
      -- Somewhere in an outer call stack we already compute this one.
      -- We don't recurse again and just return Nothing.
      -- The outer call will then recognize the instability and enqueue
      -- itself as unstable after its first approximation is computed.
      return Nothing
      --return (trace "Nothing, loop detected" Nothing)
    Nothing -> do
      Just <$> recompute node
      --Just <$> recompute (trace "Nothing, no loop" node)
    -- We aren't doing this because of monotonicity issues
    --Just _ | isNotYetStable && not loopDetected -> do
      --Just <$> recompute node
      --Just <$> recompute (trace "Just, not stable" node)
    Just info -> do
      return (value info)
      --return (trace "Just, stable" (value info))

unsafePeekValue :: Ord node => node -> TransferFunction node lattice (Maybe lattice)
unsafePeekValue node = TFM $ (value <=< Map.lookup node) <$> gets graph

data Diff a
  = Diff
  { added :: !(Set a)
  , removed :: !(Set a)
  }

computeDiff :: Ord a => Set a -> Set a -> Diff a
computeDiff from to = Diff (to `Set.difference` from) (from `Set.difference` to)

updateGraphNode
  :: Ord node
  => node
  -> lattice
  -> Set node
  -> State (WorklistState node lattice) (NodeInfo node lattice)
updateGraphNode node val refs = zoomGraph $ do
  -- if we are lucky (e.g. no refs changed), we get away with one map access
  -- first update `node`s NodeInfo
  let newInfo = emptyNodeInfo { value = Just val, references = refs }
  let merger _ new old = new { referrers = referrers old }
  oldInfo <- fromMaybe emptyNodeInfo <$> state (Map.insertLookupWithKey merger node newInfo)

  -- Now compute the diff of changed references
  let diff = computeDiff (references oldInfo) refs

  -- finally register/unregister at all references as referrer.
  let updater f dep = modify' (Map.alter (Just . f . fromMaybe emptyNodeInfo) dep)
  let addReferrer ni = ni { referrers = Set.insert node (referrers ni) }
  let removeReferrer ni = ni { referrers = Set.delete node (referrers ni) }
  forM_ (added diff) (updater addReferrer)
  forM_ (removed diff) (updater removeReferrer)

  return oldInfo

recompute
  :: Ord node
  => node
  -> State (WorklistState node lattice) lattice
recompute node = do
  oldState <- get
  put $ oldState
    { referencedNodes = Set.empty
    , callStack = Set.insert node (callStack oldState)
    }
  let (TFM transfer, detectChange) = getTransfer (framework oldState) node
  newVal <- transfer
  refs <- gets referencedNodes
  --pprTrace "recompute:refs" (ppr (length refs)) $ return ()
  oldInfo <- updateGraphNode node newVal refs
  --pprTrace "recompute:referrers" (ppr (length (referrers oldInfo))) $ return ()
  let add_new_refs = Set.union (Set.difference refs (references oldInfo)) -- new refs are changes, too!
  changedRefs <- add_new_refs . fromMaybe Set.empty <$> deleteLookupUnstable node
  case value oldInfo of
    Just oldVal | not (detectChange changedRefs oldVal newVal) -> return ()
    _ -> do
      forM_ (referrers oldInfo) (\ref -> enqueueUnstable ref (Set.singleton node))
      -- If the node depends itself the first time (e.g. when it gets its first value),
      -- that will not be reflected in `oldInfo`. So we enqueue it manually
      -- if that is the case.
      when (Set.member node refs) (enqueueUnstable node (Set.singleton node))
  modify' $ \st -> st
    { referencedNodes = referencedNodes oldState
    , callStack = callStack oldState
    }
  return newVal

enqueueUnstable :: Ord node => node -> Set node -> State (WorklistState node lattice) ()
enqueueUnstable reference referrers_ = zoomUnstable $ modify' $
  Map.alter (Just . maybe referrers_ (Set.union referrers_)) reference

deleteLookupUnstable :: Ord node => node -> State (WorklistState node lattice) (Maybe (Set node))
deleteLookupUnstable node = zoomUnstable $ state $ 
  Map.updateLookupWithKey (\_ _ -> Nothing) node

highestPriorityUnstableNode :: Ord node => State (WorklistState node lattice) (Maybe node)
highestPriorityUnstableNode = fmap (fst . fst) . Map.maxViewWithKey <$> gets unstable

whileJust_ :: Monad m => m (Maybe a) -> (a -> m b) -> m ()
whileJust_ pred action = go
  where
    go = pred >>= \m -> case m of
      Nothing -> return ()
      Just a -> action a >> go

work :: Ord node => State (WorklistState node lattice) ()
work = whileJust_ highestPriorityUnstableNode recompute

runFramework
  :: Ord node
  => DataFlowFramework node lattice
  -> Set node
  -> Map node lattice
runFramework framework_ interestingNodes = run framework_
  where
    unstable = Map.fromSet (const Set.empty) interestingNodes
    run = Map.mapMaybe value . graph . execState work . initialWorklistState unstable
