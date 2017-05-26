module CallArity.Types where

import BasicTypes
import CoreSyn
import Id
import Maybes
import Outputable
import UnVarGraph
import Usage
import VarEnv

import Control.Monad ( guard )
import Data.List ( tails, partition )

---------------------------------------
-- Functions related to UsageType    --
---------------------------------------

-- Result type for the two analyses.
-- See Note [Analysis I: The arity analyis]
-- and Note [Analysis II: The Co-Called analysis]
data UsageType
  = UT
  { ut_cocalled :: !UnVarGraph
  -- ^ Models cardinality, e.g. at most {1, many} via the co-call relation
  , ut_uses :: !(VarEnv SingleUse)
  -- ^ Models how an Id was used, if at all
  , ut_args :: !UsageSig
  -- ^ Collects the signature for captured lambda binders
  , ut_stable :: Bool
  -- ^ Entirely irrelevant for Usage information, but needed for detecting
  -- stabilization of fixed-point iteration.
  }

modifyArgs :: (UsageSig -> UsageSig) -> UsageType -> UsageType
modifyArgs modifier ut = ut { ut_args = modifier (ut_args ut) }

modifyCoCalls :: (UnVarGraph -> UnVarGraph) -> UsageType -> UsageType
modifyCoCalls modifier ut = ut { ut_cocalled = modifier (ut_cocalled ut) }

-- | How an expression uses its interesting variables
-- and the elaborated expression with annotated Ids
type AnalResult = (UsageType, CoreExpr)

emptyUsageType :: UsageType
emptyUsageType = UT emptyUnVarGraph emptyVarEnv topUsageSig False

botUsageType :: UsageType
botUsageType = unusedArgs emptyUsageType

unitUsageType :: Id -> SingleUse -> UsageType
unitUsageType id use = emptyUsageType { ut_uses = unitVarEnv id use }

unusedArgs :: UsageType -> UsageType
unusedArgs ut = ut { ut_args = botUsageSig }

delUsageTypes :: [Id] -> UsageType -> UsageType
delUsageTypes ids ae = foldr delUsageType ae ids

delUsageType :: Id -> UsageType -> UsageType
delUsageType id (UT g ae args s) = UT (g `delNode` id) (ae `delVarEnv` id) args s

domType :: UsageType -> UnVarSet
domType ut = varEnvDom (ut_uses ut)

domTypes :: [UsageType] -> UnVarSet
domTypes = foldr unionUnVarSet emptyUnVarSet . map domType

makeIdArg :: Id -> UsageType -> UsageType
makeIdArg id ut = delUsageType id (modifyArgs (consUsageSig (lookupUsage NonRecursive ut id)) ut)

-- In the result, find out the minimum arity and whether the variable is called
-- at most once.
lookupUsage :: RecFlag -> UsageType -> Id -> Usage
lookupUsage rec (UT g ae _ _) id = case lookupVarEnv ae id of
  Just use
    -- we assume recursive bindings to be called multiple times, what's the
    -- point otherwise? It's a little sad we don't encode it in the co-call
    -- graph directly, though.
    -- See Note [Thunks in recursive groups]
    | isRec rec -> manifyUsage (Used Once use)
    | id `elemUnVarSet` neighbors g id -> Used Many use
    | otherwise -> Used Once use
  Nothing -> botUsage

calledWith :: UsageType -> Id -> UnVarSet
calledWith ut id = neighbors (ut_cocalled ut) id

-- Replaces the co-call graph by a complete graph (i.e. no information)
multiplyUsages :: Multiplicity -> UsageType -> UsageType
multiplyUsages Once ut = ut
multiplyUsages Many ut@(UT _ u args _)
  = UT
  { ut_cocalled = completeGraph (domType ut)
  , ut_uses = mapVarEnv (\use -> bothSingleUse use use) u
  , ut_args = manifyUsageSig args
  , ut_stable = False
  }

asCompleteGraph :: UsageType -> Maybe UnVarSet
asCompleteGraph ut = do
  s <- UnVarGraph.isCompleteGraph_maybe (ut_cocalled ut)
  guard (sizeUnVarSet s == sizeUnVarSet (domType ut))
  return s

bothUsageTypes :: [UsageType] -> UsageType
bothUsageTypes uts 
  = UT cocalled uses args False
  where
    uses = foldr bothUseEnv emptyVarEnv (map ut_uses uts)
    args 
      = ut_args 
      . expectJust "bothUsageTypes: argument list empty" 
      . listToMaybe
      $ uts
    -- Cross calls between complete graphs yield another complete graph.
    -- This is an important optimization for large tuples, like occuring
    -- when analysing top-level binds as let bindings
    (completes, incompletes) 
      -- = ([], uts)
      = partition (isJust . asCompleteGraph) uts
    completeDom
      = unionUnVarSets 
      . map (fromJust . asCompleteGraph) 
      $ completes
    completePart = completeGraph completeDom
    graphs = completePart : map ut_cocalled incompletes
    doms = completeDom : map domType incompletes
    -- all tails, beginning with a two element list
    pairings = drop 2 . reverse . tails $ doms
    crossCalls = flip map pairings $ \(dom:others) -> 
      -- There room for improvement by reusing the result of `unionUnVarSets`
      completeBipartiteGraph dom (unionUnVarSets others) 
    cocalled = unionUnVarGraphs (graphs ++ crossCalls)

-- | Corresponds to sequential composition of expressions.
-- Used for application and cases.
-- Note this returns the @UsageSig@ from the first argument.
bothUsageType :: UsageType -> UsageType -> UsageType
bothUsageType ut1 ut2 = bothUsageTypes [ut1, ut2]

-- | Used when combining results from alternative cases
lubUsageType :: UsageType -> UsageType -> UsageType
lubUsageType (UT g1 u1 args1 _) (UT g2 u2 args2 _)
  = UT
  { ut_cocalled = unionUnVarGraph g1 g2
  , ut_uses = lubUseEnv u1 u2
  , ut_args = lubUsageSig args1 args2
  , ut_stable = False
  }

lubUseEnv :: VarEnv SingleUse -> VarEnv SingleUse -> VarEnv SingleUse
lubUseEnv = plusVarEnv_C lubSingleUse

bothUseEnv :: VarEnv SingleUse -> VarEnv SingleUse -> VarEnv SingleUse
bothUseEnv = plusVarEnv_C bothSingleUse

lubUsageTypes :: [UsageType] -> UsageType
lubUsageTypes = foldl lubUsageType botUsageType

-- | Peels off a single argument usage from the signature, corresponding to how
-- @App f a@ uses @a@ under the given incoming arity.
peelArgUsage :: UsageType -> (Usage, UsageType)
peelArgUsage ut = (usg, ut { ut_args = args' })
  where
    (usg, args') = unconsUsageSig (ut_args ut)

markStable :: UsageType -> UsageType
markStable ut = ut { ut_stable = True }

-- * Pretty-printing

instance Outputable UsageType where
  ppr (UT cocalled arities args _) = vcat
    [ text "arg usages:" <+> ppr args
    , text "co-calls:" <+> ppr cocalled
    , text "uses:" <+> ppr arities
    ]
