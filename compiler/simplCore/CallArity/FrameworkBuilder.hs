{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CallArity.FrameworkBuilder
  ( predictAllocatedNodes
  , FrameworkNode
  , TransferFunction
  , ChangeDetector
  , Worklist.alwaysChangeDetector
  , DataFlowFramework
  , FrameworkBuilder
  , RetainedChunk
  , retainNodes
  , freeRetainedNodes
  , registerTransferFunction
  , monotonize
  , dependOnWithDefault
  , buildAndRun
  ) where

import CallArity.Types
import CoreSyn
import Outputable
import Usage
import qualified Worklist

import Control.Monad.Fix
import Control.Monad.Trans.State.Strict
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap.Lazy as IntMap
import Data.Map.Strict   (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Tree

predictAllocatedNodes :: Expr b -> Tree Int
predictAllocatedNodes = expr
  where
    expr (App f a) = mk_parent . map expr $ [f, a]
    expr (Lam _ e) = expr e
    expr (Let bs body) = map_lbl (+1) . mk_parent $ expr body:bind bs
    expr (Case scrut _ _ alts) = mk_parent (expr scrut:alt alts)
    expr (Cast e _) = expr e
    expr (Tick _ e) = expr e
    expr _ = empty_node
    bind = map (map_lbl (+2) . expr) . rhssOfBind
    alt = map expr . rhssOfAlts
    map_lbl f (Node l cs) = Node (f l) cs -- Can't fmap, as that also increments children
    add_child c (Node p cs) = Node (rootLabel c + p) (c:cs)
    empty_node = Node 0 []
    mk_parent = foldr add_child empty_node

newtype FrameworkNode
  = FrameworkNode Int
  deriving (Show, Eq, Ord, Outputable)

type TransferFunction a = Worklist.TransferFunction (FrameworkNode, SingleUse) AnalResult a
type ChangeDetector = Worklist.ChangeDetector (FrameworkNode, SingleUse) AnalResult
type DataFlowFramework = Worklist.DataFlowFramework (FrameworkNode, SingleUse) AnalResult
-- | Maps @FrameworkNode@ to incoming usage dependent @TransferFunction@s
type NodeTransferEnv = IntMap (SingleUse -> TransferFunction AnalResult, ChangeDetector)

data BuilderState
  = BS 
  { bs_env :: !NodeTransferEnv
  -- ^ Maps allocated `FrameworkNode`s to `TransferFunction`s.
  , bs_free :: IntMap Int
  -- ^ Begin of next free node and size of the free chunk.
  }

modifyFree :: (IntMap Int -> IntMap Int) -> BuilderState -> BuilderState
modifyFree f bs = bs { bs_free = f (bs_free bs) }

modifyEnv :: (NodeTransferEnv -> NodeTransferEnv) -> BuilderState -> BuilderState
modifyEnv f bs = bs { bs_env = f (bs_env bs) }

data RetainedChunk 
  = RC 
  { rc_start :: !Int 
  , rc_end :: !Int
  }

initialBuilderState :: BuilderState
initialBuilderState = BS IntMap.empty (IntMap.singleton 0 maxBound)

newtype FrameworkBuilder a
  = FB { unFB :: State BuilderState a }
  deriving (Functor, Applicative, Monad)

buildFramework :: FrameworkBuilder a -> (a, DataFlowFramework)
buildFramework (FB state) = (res, Worklist.DFF dff)
  where
    (res, bs) = runState state initialBuilderState
    dff (FrameworkNode node, use) = case IntMap.lookup node (bs_env bs) of
      Nothing -> pprPanic "CallArity.FrameworkBuilder.buildFramework" (ppr node)
      Just (transfer, detectChange) -> (transfer use, detectChange)

viewAt :: Int -> IntMap a -> Maybe (a, IntMap a)
viewAt n m = case IntMap.updateLookupWithKey (\_ _ -> Nothing) n m of
  (Just v, m') -> Just (v, m')
  _ -> Nothing

mergeAt :: Int -> IntMap Int -> IntMap Int
mergeAt split free
  | Just (start, split') <- IntMap.lookupLT split free
  , split == split'
  , Just (end, free') <- viewAt split free
  = IntMap.insert start end free'
  | otherwise
  = free

freeChunk :: RetainedChunk -> IntMap Int -> IntMap Int
freeChunk (RC start end)
  | start == end
  = id
freeChunk (RC start end)
  = mergeAt start . mergeAt end . IntMap.insert start end

requestChunk :: Int -> IntMap Int -> (RetainedChunk, IntMap Int)
requestChunk req_size free
  | Just ((start, end), free') <- IntMap.minViewWithKey free
  , split <- start + req_size
  , split <= end
  = (RC start split, freeChunk (RC split end) free')
  | Just ((start, end), _) <- IntMap.minViewWithKey free
  = pprPanic "requestChunk: requested chunk size too big" (ppr req_size <+> ppr (end - start))
  | otherwise
  = pprPanic "requestChunk: no chunks available (?)" empty

retainNodes :: Int -> FrameworkBuilder RetainedChunk
retainNodes req_size = FB (state impl)
  where
    impl bs
      | (rc, free') <- requestChunk req_size (bs_free bs)
      = (rc, bs { bs_free = free' })

freeRetainedNodes :: RetainedChunk -> FrameworkBuilder ()
freeRetainedNodes rc = FB (modify' (modifyFree (freeChunk rc))) 

popNextFreeNode :: State BuilderState Int
popNextFreeNode = rc_start <$> unFB (retainNodes 1)

registerTransferFunction
  :: (FrameworkNode -> FrameworkBuilder (a, (SingleUse -> TransferFunction AnalResult, ChangeDetector)))
  -> FrameworkBuilder a
registerTransferFunction f = FB $ do
  node <- popNextFreeNode
  (result, _) <- mfix $ \ ~(_, entry) -> do
    -- Using mfix so that we can spare an unnecessary Int counter in the state.
    -- Also because @f@ needs to see its own node in order to define its
    -- transfer function in case of letrec.
    modify' (modifyEnv (IntMap.insertWith (pprPanic "Overwriting TransferFunction" (ppr node)) node entry))
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
