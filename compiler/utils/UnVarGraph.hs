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
  , edge_count :: Int -- Intentionally lazy!
  }

edgeCount :: UnVarGraph -> Int
edgeCount g 
  | Additive <- edge_interpretation g = edge_count g
  | otherwise = nodes*nodes - edge_count g
  where
    nodes = IntMap.size (edges g)

mkUnVarGraph :: OverlayResolution -> IntMap UnVarSet -> UnVarGraph
mkUnVarGraph ei edges
  = UnVarGraph
  { edge_interpretation = ei
  , edges = edges
  , edge_count = foldr ((+) . sizeUnVarSet) 0 edges
  }

balance :: UnVarGraph -> UnVarGraph
balance g@(UnVarGraph _ edges ec)
  | ratio < 0.6 = g
  | otherwise = complementUnVarGraph g
  where
    nodes = IntMap.size edges
    max_edges = nodes * nodes
    ratio :: Double
    ratio = fromIntegral ec / fromIntegral max_edges

complementUnVarGraph :: UnVarGraph -> UnVarGraph
complementUnVarGraph (UnVarGraph res edges _) 
  = mkUnVarGraph (complementOverlayResolution res) (complementEdges edges)

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
emptyUnVarGraph = mkUnVarGraph Subtractive IntMap.empty

unionUnVarGraph :: UnVarGraph -> UnVarGraph -> UnVarGraph
unionUnVarGraph (UnVarGraph Additive e1 _) (UnVarGraph Additive e2 _)
  = balance $ mkUnVarGraph Additive $ IntMap.unionWith unionUnVarSet e1 e2
unionUnVarGraph (UnVarGraph Subtractive e1 _) (UnVarGraph Subtractive e2 _)
  = balance $ mkUnVarGraph Subtractive $ IntMap.unionWith intersectionUnVarSet e1' e2'
  where
    -- diffn = nodes of the union *not* mentioned in graph n
    diff1 = UnVarSet $ IntMap.keysSet e2 `IntSet.difference` IntMap.keysSet e1
    diff2 = UnVarSet $ IntMap.keysSet e1 `IntSet.difference` IntMap.keysSet e2
    e1' = unionUnVarSet diff1 <$> e1
    e2' = unionUnVarSet diff2 <$> e2
unionUnVarGraph u1 u2
  = unionUnVarGraph u1' u2' -- we could be smarter here
  where
    nodes1 = IntMap.size (edges u1)
    nodes2 = IntMap.size (edges u2)
    (u1', u2')
      | nodes1 < nodes2 = (complementUnVarGraph u1, u2)
      | otherwise = (u1, complementUnVarGraph u2)
    
unionUnVarGraphs :: [UnVarGraph] -> UnVarGraph
unionUnVarGraphs = foldr unionUnVarGraph emptyUnVarGraph

-- completeBipartiteGraph A B = { {a,b} | a ∈ A, b ∈ B }
completeBipartiteGraph :: UnVarSet -> UnVarSet -> UnVarGraph
completeBipartiteGraph u1@(UnVarSet s1) u2@(UnVarSet s2) 
  = balance $ UnVarGraph Additive edges ec
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
  = UnVarGraph Subtractive (IntMap.fromSet (const emptyUnVarSet) s) 0

isCompleteGraph_maybe :: UnVarGraph -> Maybe UnVarSet
isCompleteGraph_maybe (UnVarGraph Subtractive e _) 
  = Just (UnVarSet (IntMap.keysSet e))
isCompleteGraph_maybe _ = Nothing

neighbors :: UnVarGraph -> Var -> UnVarSet
neighbors (UnVarGraph ie edges _) v 
  = fromMaybe emptyUnVarSet (interpret_edge <$> IntMap.lookup (k v) edges)
  where 
    dom = UnVarSet $ IntMap.keysSet edges
    interpret_edge 
      | ie == Additive = id
      | otherwise = differenceUnVarSet dom

delNode :: UnVarGraph -> Var -> UnVarGraph
delNode (UnVarGraph ei g _) v 
  = mkUnVarGraph ei g2 -- No rebalance here, since the graph gets smaller anyway
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

instance Outputable UnVarGraph where
    ppr (UnVarGraph Additive g _) = pprEdges "+" g
    ppr (UnVarGraph _ g _) = pprEdges "-" (complementEdges g)

pprEdges :: String -> IntMap UnVarSet -> SDoc
pprEdges sign
  = (text "UnVarGraph" <> text sign <+>) 
  . brackets 
  . hcat 
  . punctuate comma 
  . map (\(k, v) -> ppr (getUnique k) <+> text ":->" <+> ppr v)
  . IntMap.toList
