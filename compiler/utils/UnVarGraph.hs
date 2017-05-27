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
    , UnVarGraph
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
newtype UnVarSet = UnVarSet IntSet
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

newtype UnVarGraph = UnVarGraph UnVarSet

emptyUnVarGraph :: UnVarGraph
emptyUnVarGraph = UnVarGraph emptyUnVarSet

unionUnVarGraph :: UnVarGraph -> UnVarGraph -> UnVarGraph
unionUnVarGraph (UnVarGraph u1) (UnVarGraph u2) = UnVarGraph (unionUnVarSet u1 u2)
    
unionUnVarGraphs :: [UnVarGraph] -> UnVarGraph
unionUnVarGraphs = foldr unionUnVarGraph emptyUnVarGraph

completeBipartiteGraph :: UnVarSet -> UnVarSet -> UnVarGraph
completeBipartiteGraph u1 u2 = UnVarGraph (unionUnVarSet u1 u2)
        
completeGraph :: UnVarSet -> UnVarGraph
completeGraph = UnVarGraph

isCompleteGraph_maybe :: UnVarGraph -> Maybe UnVarSet
isCompleteGraph_maybe (UnVarGraph u) = Just u

neighbors :: UnVarGraph -> Var -> UnVarSet
neighbors (UnVarGraph u) v = u

delNode :: UnVarGraph -> Var -> UnVarGraph
delNode (UnVarGraph u) v = UnVarGraph $ delUnVarSet u v

instance Outputable UnVarGraph where
    ppr (UnVarGraph u) = ppr u
