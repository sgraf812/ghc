{-# LANGUAGE BangPatterns #-}
{-

Copyright (c) 2014 Joachim Breitner

A data structure for undirected graphs of variables
(or in plain terms: Sets of unordered pairs of numbers)


This is very specifically tailored for the use in CallArity. In particular it
stores the graph as a union of complete and complete bipartite graph, which
would be very expensive to store as sets of edges or as adjanceny lists.

It does not normalize the graphs. This means that g `unionUnVarGraph` g is
equal to g, but twice as expensive and large.

-}
module UnVarGraph
    ( UnVarSet
    , emptyUnVarSet, sizeUnVarSet, mkUnVarSet, varEnvDom, restrictVarEnv_UnVarSet
    , unionUnVarSet, unionUnVarSets, delUnVarSet
    , elemUnVarSet, isEmptyUnVarSet
    , UnVarGraph, edgeCount
    , emptyUnVarGraph
    , unionUnVarGraph, unionUnVarGraphs
    , completeGraph, completeBipartiteGraph
    , isCompleteGraph_maybe
    , neighbors
    , delNode
    ) where

import Id
import VarEnv
import UniqFM
import Outputable
import Unique
import Maybes

import Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict ( IntMap )
import qualified Data.IntMap.Strict as IntMap

-- We need a type for sets of variables (UnVarSet).
-- We do not use VarSet, because for that we need to have the actual variable
-- at hand, and we do not have that when we turn the domain of a VarEnv into a UnVarSet.
-- Therefore, use a IntSet directly (which is likely also a bit more efficient).

-- Set of uniques, i.e. for adjancet nodes
newtype UnVarSet 
  = UnVarSet IntSet
  deriving Eq

k :: Var -> Int
k v = getKey (getUnique v)

emptyUnVarSet :: UnVarSet
emptyUnVarSet = UnVarSet IntSet.empty

sizeUnVarSet :: UnVarSet -> Int
sizeUnVarSet (UnVarSet s) = IntSet.size s

elemUnVarSet :: Var -> UnVarSet -> Bool
elemUnVarSet v (UnVarSet s) = k v `IntSet.member` s

isEmptyUnVarSet :: UnVarSet -> Bool
isEmptyUnVarSet (UnVarSet s) = IntSet.null s

differenceUnVarSet :: UnVarSet -> UnVarSet -> UnVarSet
differenceUnVarSet (UnVarSet s1) (UnVarSet s2) = UnVarSet $ IntSet.difference s1 s2

intersectionUnVarSet :: UnVarSet -> UnVarSet -> UnVarSet
intersectionUnVarSet (UnVarSet s1) (UnVarSet s2) = UnVarSet $ IntSet.intersection s1 s2

delUnVarSet :: UnVarSet -> Var -> UnVarSet
delUnVarSet (UnVarSet s) v = UnVarSet $ k v `IntSet.delete` s

mkUnVarSet :: [Var] -> UnVarSet
mkUnVarSet vs = UnVarSet $ IntSet.fromList $ map k vs

varEnvDom :: VarEnv a -> UnVarSet
varEnvDom ae = UnVarSet $ ufmToSet_Directly ae

restrictVarEnv_UnVarSet :: VarEnv a -> UnVarSet -> VarEnv a
restrictVarEnv_UnVarSet env (UnVarSet s) = filterVarEnv_Directly keep env
  where
    keep u _ = getKey u `IntSet.member` s

unionUnVarSet :: UnVarSet -> UnVarSet -> UnVarSet
unionUnVarSet (UnVarSet set1) (UnVarSet set2) = UnVarSet (set1 `IntSet.union` set2)

unionUnVarSets :: [UnVarSet] -> UnVarSet
unionUnVarSets = foldr unionUnVarSet emptyUnVarSet

instance Outputable UnVarSet where
  ppr (UnVarSet s) = braces $
    hcat $ punctuate comma [ ppr (getUnique i) | i <- IntSet.toList s]

data OverlayResolution
  = Additive
  | Subtractive
  deriving (Eq, Ord, Show)

complementOverlayResolution :: OverlayResolution -> OverlayResolution
complementOverlayResolution Additive = Subtractive
complementOverlayResolution Subtractive = Additive

data UnVarGraph 
  = UnVarGraph
  { edge_interpretation :: !OverlayResolution
  , edges :: !(IntMap UnVarSet)
  , edge_count_estimate :: !(Int, Int)
  , edge_count :: Int -- Intentionally lazy!
  }

edgeCount :: UnVarGraph -> Int
edgeCount = edge_count

mkUnVarGraph :: OverlayResolution -> IntMap UnVarSet -> (Int, Int) -> UnVarGraph
mkUnVarGraph ei edges ec_estimate 
  = UnVarGraph
  { edge_interpretation = ei
  , edges = edges
  , edge_count_estimate = ec_estimate
  , edge_count = foldr ((+) . sizeUnVarSet) 0 edges
  }

balance :: UnVarGraph -> UnVarGraph
balance g@(UnVarGraph ei edges (_, ub) ec)
  | ub_ratio < 0.6 = g
  | precise_ratio < 0.6 = precise_g
  | otherwise = complementUnVarGraph precise_g
  where
    nodes = IntMap.size edges
    max_edges = nodes * nodes
    ub_ratio :: Double
    ub_ratio = fromIntegral ub / fromIntegral max_edges
    precise_ratio :: Double
    precise_ratio = fromIntegral ec / fromIntegral max_edges
    precise_g = UnVarGraph ei edges (ec, ec) ec

complementUnVarGraph :: UnVarGraph -> UnVarGraph
complementUnVarGraph (UnVarGraph res edges (lb, ub) _) 
  = mkUnVarGraph (complementOverlayResolution res) (complementEdges edges) ec_est
  where
    nodes = IntMap.size edges
    max_edges = nodes*nodes
    ec_est = (max_edges - ub, max_edges - lb)

complementEdges :: IntMap UnVarSet -> IntMap UnVarSet
complementEdges edges = edges'
  where
    dom = UnVarSet (IntMap.keysSet edges)
    edges' = fmap complement_neighbors edges
    complement_neighbors neighbors
      -- Very common cases are an empty neighbor set and the full neighbor set,
      -- in which case we want to be pretty cheap.
      | isEmptyUnVarSet neighbors = dom
      | sizeUnVarSet neighbors == sizeUnVarSet dom = emptyUnVarSet
      | otherwise = differenceUnVarSet dom neighbors

emptyUnVarGraph :: UnVarGraph
emptyUnVarGraph = mkUnVarGraph Subtractive IntMap.empty (0, 0)

unionUnVarGraph :: UnVarGraph -> UnVarGraph -> UnVarGraph
unionUnVarGraph u1@(UnVarGraph Subtractive _ _ _) u2
  = unionUnVarGraph (complementUnVarGraph u1) u2
unionUnVarGraph u1 u2@(UnVarGraph Subtractive _ _ _)
  = unionUnVarGraph u1 (complementUnVarGraph u2)
unionUnVarGraph (UnVarGraph Additive e1 (l1, u1) _) (UnVarGraph Additive e2 (l2, u2) _)
  = balance $ mkUnVarGraph Additive e (max l1 l2, u1 + u2) 
  where
    e = IntMap.unionWith unionUnVarSet e1 e2
    
unionUnVarGraphs :: [UnVarGraph] -> UnVarGraph
unionUnVarGraphs = foldr unionUnVarGraph emptyUnVarGraph

-- completeBipartiteGraph A B = { {a,b} | a ∈ A, b ∈ B }
completeBipartiteGraph :: UnVarSet -> UnVarSet -> UnVarGraph
completeBipartiteGraph u1@(UnVarSet s1) u2@(UnVarSet s2) 
  = balance (UnVarGraph Additive edges (ec, ec) ec)
  where
    dom@(UnVarSet s) = unionUnVarSet u1 u2
    (UnVarSet s3) = intersectionUnVarSet u1 u2 -- common elements
    a = sizeUnVarSet u1
    b = sizeUnVarSet u2
    ec = 2*a*b
    edges = IntMap.fromSet neighbors_of s
    neighbors_of k
      | k `IntSet.member` s3 = dom
      | k `IntSet.member` s1 = u2
      | k `IntSet.member` s2 = u1
        
completeGraph :: UnVarSet -> UnVarGraph
completeGraph (UnVarSet s) 
  = mkUnVarGraph Subtractive (IntMap.fromSet (const emptyUnVarSet) s) (0, 0)

isCompleteGraph_maybe :: UnVarGraph -> Maybe UnVarSet
isCompleteGraph_maybe (UnVarGraph Subtractive e (0, 0) _) 
  = Just (UnVarSet (IntMap.keysSet e))
isCompleteGraph_maybe _ = Nothing

neighbors :: UnVarGraph -> Var -> UnVarSet
neighbors (UnVarGraph ie edges _ _) v 
  = fromMaybe emptyUnVarSet (interpret_edge <$> IntMap.lookup (k v) edges)
  where 
    dom = UnVarSet $ IntMap.keysSet edges
    interpret_edge 
      | ie == Additive = id
      | otherwise = differenceUnVarSet dom

delNode :: UnVarGraph -> Var -> UnVarGraph
delNode (UnVarGraph ei g (lb, ub) _) v 
  = mkUnVarGraph ei g2 (lb', ub') -- No rebalance here, since the graph gets smaller anyway
  where 
    -- Note that we need to delete all mentioned edges, regardless of `ei`.
    (neighbors_maybe, g1) = IntMap.updateLookupWithKey (\_ _ -> Nothing) (k v) g
    UnVarSet neighbors = fromMaybe emptyUnVarSet neighbors_maybe
    g2 = foldr (IntMap.adjust deleter) g1 (IntSet.toList neighbors)
    dom = UnVarSet $ IntMap.keysSet g
    new_dom = delUnVarSet dom v
    deleter s
      -- Again, optimize for the common cases
      | sizeUnVarSet s <= 1 = emptyUnVarSet -- This assumes that v is in s
      | sizeUnVarSet s == sizeUnVarSet dom = new_dom
      | otherwise = delUnVarSet s v
    del_edge_count = IntSet.size neighbors
    lb' = lb - del_edge_count
    ub' = ub - del_edge_count

instance Outputable UnVarGraph where
    ppr u@(UnVarGraph ei g _ _) 
      | ei == Additive = ppr g
      | otherwise = ppr (complementUnVarGraph u)
