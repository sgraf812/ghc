{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Worklist where

import Control.Arrow (first)
import Control.Monad (forM_)
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
  , loopBreakers :: !(Set node)
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

zoomLoopBreakers :: State (Set node) a -> State (WorklistState node lattice) a
zoomLoopBreakers modifier = state $ \st ->
  let (res, lb) = runState modifier (loopBreakers st)
  in  (res, st { loopBreakers = lb })

initialWorklistState
  :: Map node (Set node)
  -> DataFlowFramework node lattice
  -> WorklistState node lattice
initialWorklistState unstable fw =
  WorklistState fw Map.empty unstable Set.empty Set.empty Set.empty

dependOn :: Ord node => node -> TransferFunction node lattice (Maybe lattice)
dependOn node = TFM $ do
  loopDetected <- Set.member node <$> gets callStack
  isNotYetStable <- Map.member node <$> gets unstable
  maybeNodeInfo <- Map.lookup node <$> gets graph
  zoomReferencedNodes (modify' (Set.insert node)) -- save that we depend on this value
  case maybeNodeInfo of
    Nothing | loopDetected -> do
      -- We have to revisit these later
      zoomLoopBreakers (modify' (Set.insert node))
      --return (trace "Nothing, loop detected" Nothing)
      return Nothing
    Nothing -> do
      --fmap (\(val, _, _) -> Just val) (recompute (trace "Nothing, no loop" node))
      fmap (\(val, _, _) -> Just val) (recompute node)
--    Just _ | isNotYetStable && not loopDetected -> do
--      fmap (\(val, _, _) -> Just val) (recompute (trace "Just, not stable" node))
    Just info -> do
      return (value info)

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
  -> State (WorklistState node lattice) (lattice, NodeInfo node lattice, ChangeDetector node lattice)
recompute node = do
  oldState <- get
  put $ oldState
    { referencedNodes = Set.empty
    , callStack = Set.insert node (callStack oldState)
    }
  let (TFM transfer, changeDetector) = getTransfer (framework oldState) node
  val <- transfer
  refs <- gets referencedNodes
  --pprTrace "recompute:refs" (ppr (length refs)) $ return ()
  oldInfo <- updateGraphNode node val refs
  modify' $ \st -> st
    { referencedNodes = referencedNodes oldState
    , callStack = callStack oldState
    }
  return (val, oldInfo, changeDetector)

enqueueUnstable :: Ord node => node -> Set node -> State (WorklistState node lattice) ()
enqueueUnstable reference referrers_ = zoomUnstable $ modify' $
  Map.alter (Just . maybe referrers_ (Set.union referrers_)) reference

dequeueUnstable :: Ord node => State (WorklistState node lattice) (Maybe (node, Set node))
dequeueUnstable = zoomUnstable $ state $ \m ->
  maybe (Nothing, m) (first Just) (Map.maxViewWithKey m)

lookupReferrers :: Ord node => node -> Graph node lattice -> Set node
lookupReferrers node = maybe Set.empty referrers . Map.lookup node

work :: Ord node => State (WorklistState node lattice) ()
work = do
  m <- dequeueUnstable
  case m of
    Nothing -> return ()
    Just (node, changedRefs) -> do
      modify' $ \st -> st { loopBreakers = Set.empty, callStack = Set.empty, referencedNodes = Set.empty }
      (newVal, oldInfo, detectChange) <- recompute node
      -- We have to enqueue all referrers to loop breakers, e.g. nodes which we
      -- returned `Nothing` from `dependOn` to break cyclic dependencies.
      -- Their referrers probably aren't carrying safe values, so we have to
      -- revisit them. This looks expensive, but loopBreakers should be pretty
      -- rare later on.
      g <- gets graph
      lbs <- gets loopBreakers
      forM_ lbs (\lb -> enqueueUnstable lb (lookupReferrers lb g))
      case value oldInfo of
        Just oldVal | not (detectChange changedRefs oldVal newVal) -> return ()
        _ -> forM_ (referrers oldInfo) (\ref -> enqueueUnstable ref (Set.singleton node))
      work

runFramework
  :: Ord node
  => DataFlowFramework node lattice
  -> Set node
  -> Map node lattice
runFramework framework_ interestingNodes = run framework_
  where
    unstable = Map.fromSet (const Set.empty) interestingNodes
    run = Map.mapMaybe value . graph . execState work . initialWorklistState unstable
