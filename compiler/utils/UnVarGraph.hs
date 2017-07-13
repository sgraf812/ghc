{-# LANGUAGE BangPatterns #-}
{-

Copyright (c) 2014 Joachim Breitner

A data structure for undirected graphs of variables
(or in plain terms: Sets of unordered pairs of numbers)


This is very specifically tailored for the use in UsageAnal. In particular it
is optimized for the nearly complete and sparse cases, which are quite common
for co-call graphs.

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

newtype UnVarGraph 
  -- we regard this as the isomorphism Bool ~ Multiplicity without depending on Usage.hs
  = UnVarGraph (IntMap Bool)
  deriving Eq

edgeCount :: UnVarGraph -> Int
-- This isn't really edge count anymore, but yeah
edgeCount (UnVarGraph m) = n*(n-1) + IntMap.size (IntMap.filter (== True) m)
  where
    n = IntMap.size m

emptyUnVarGraph :: UnVarGraph
emptyUnVarGraph = UnVarGraph IntMap.empty

unionUnVarGraph :: UnVarGraph -> UnVarGraph -> UnVarGraph
unionUnVarGraph (UnVarGraph m1) (UnVarGraph m2) = UnVarGraph (IntMap.unionWith (||) m1 m2)
  
unionUnVarGraphs :: [UnVarGraph] -> UnVarGraph
unionUnVarGraphs = foldr unionUnVarGraph emptyUnVarGraph

-- completeBipartiteGraph A B = { {a,b} | a ∈ A, b ∈ B }
completeBipartiteGraph :: UnVarSet -> UnVarSet -> UnVarGraph
completeBipartiteGraph (UnVarSet s1) (UnVarSet s2) 
  = UnVarGraph (IntMap.unionWith (\_ _ -> True) (mkMap s1) (mkMap s2))
  where
    mkMap = IntMap.fromSet (const False)
      
completeGraph :: UnVarSet -> UnVarGraph
completeGraph (UnVarSet s) = UnVarGraph (IntMap.fromSet (const True) s)

isCompleteGraph_maybe :: UnVarGraph -> Maybe UnVarSet
isCompleteGraph_maybe (UnVarGraph m) 
  | IntMap.foldr (&&) True m
  = Just (UnVarSet (IntMap.keysSet m))
isCompleteGraph_maybe _ = Nothing

neighbors :: UnVarGraph -> Var -> UnVarSet
neighbors (UnVarGraph m) v = 
  case IntMap.lookup (k v) m of
    Nothing -> emptyUnVarSet
    Just False -> UnVarSet (IntSet.delete (k v) (IntMap.keysSet m))
    Just True -> UnVarSet (IntMap.keysSet m)

delNode :: UnVarGraph -> Var -> UnVarGraph
delNode (UnVarGraph m) v = UnVarGraph (IntMap.delete (k v) m)

instance Outputable UnVarGraph where
    ppr (UnVarGraph g) = text "UnVarGraph" <+> ppr g
