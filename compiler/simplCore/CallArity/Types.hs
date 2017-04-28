module CallArity.Types where

import CoreArity ( typeArity )
import CoreSyn
import Id
import Outputable
import UnVarGraph
import Usage
import VarEnv

---------------------------------------
-- Functions related to UsageType    --
---------------------------------------

-- Result type for the two analyses.
-- See Note [Analysis I: The arity analyis]
-- and Note [Analysis II: The Co-Called analysis]
data UsageType
  = UT
  { ut_cocalled :: !UnVarGraph
  -- ^ Models cardinality, e.g. at most {1, many} via the co-call relation for
  -- _interesting_ variables
  , ut_uses :: !(VarEnv SingleUse)
  -- ^ Models per var usage and absence (card 0)
  , ut_args :: !UsageSig
  -- ^ Collects the signature for captured lambda binders
  }

modifyArgs :: (UsageSig -> UsageSig) -> UsageType -> UsageType
modifyArgs modifier ut = ut { ut_args = modifier (ut_args ut) }

modifyCoCalls :: (UnVarGraph -> UnVarGraph) -> UsageType -> UsageType
modifyCoCalls modifier ut = ut { ut_cocalled = modifier (ut_cocalled ut) }

-- | How an expression uses its interesting variables
-- and the elaborated expression with annotated Ids
type AnalResult = (UsageType, CoreExpr)

emptyUsageType :: UsageType
emptyUsageType = UT emptyUnVarGraph emptyVarEnv topUsageSig

botUsageType :: UsageType
botUsageType = unusedArgs emptyUsageType

unitUsageType :: Id -> SingleUse -> UsageType
unitUsageType id use = emptyUsageType { ut_uses = unitVarEnv id use }

unusedArgs :: UsageType -> UsageType
unusedArgs ut = ut { ut_args = botUsageSig }

delUsageTypes :: [Id] -> UsageType -> UsageType
delUsageTypes ids ae = foldr delUsageType ae ids

delUsageType :: Id -> UsageType -> UsageType
delUsageType id (UT g ae args) = UT (g `delNode` id) (ae `delVarEnv` id) args

domType :: UsageType -> UnVarSet
domType ut = varEnvDom (ut_uses ut)

makeIdArg :: Id -> UsageType -> UsageType
makeIdArg id ut = delUsageType id (modifyArgs (consUsageSig (lookupUsage ut id)) ut)

-- In the result, find out the minimum arity and whether the variable is called
-- at most once.
lookupUsage :: UsageType -> Id -> Usage
lookupUsage (UT g ae _) id = case lookupVarEnv ae id of
  Just use
    | id `elemUnVarSet` neighbors g id -> Used Many use
    | otherwise -> Used Once use
  Nothing -> botUsage

calledWith :: UsageType -> Id -> UnVarSet
calledWith ut id = neighbors (ut_cocalled ut) id

-- Replaces the co-call graph by a complete graph (i.e. no information)
multiplyUsages :: Multiplicity -> UsageType -> UsageType
multiplyUsages Once ut = ut
multiplyUsages Many ut@(UT _ u args)
  = UT
  { ut_cocalled = completeGraph (domType ut)
  , ut_uses = mapVarEnv (\use -> bothSingleUse use use) u
  , ut_args = manifyUsageSig args
  }

-- | Corresponds to sequential composition of expressions.
-- Used for application and cases.
-- Note this returns the @UsageSig@ from the first argument.
bothUsageType :: UsageType -> UsageType -> UsageType
bothUsageType ut1@(UT g1 u1 args) ut2@(UT g2 u2 _)
  = UT
  { ut_cocalled = unionUnVarGraphs [g1, g2, completeBipartiteGraph (domType ut1) (domType ut2)]
  , ut_uses = bothUseEnv u1 u2
  , ut_args = args
  }

-- | Used when combining results from alternative cases
lubUsageType :: UsageType -> UsageType -> UsageType
lubUsageType (UT g1 u1 args1) (UT g2 u2 args2)
  = UT
  { ut_cocalled = unionUnVarGraph g1 g2
  , ut_uses = lubUseEnv u1 u2
  , ut_args = lubUsageSig args1 args2
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

-- * Pretty-printing

instance Outputable UsageType where
  ppr (UT cocalled arities args) = vcat
    [ text "arg usages:" <+> ppr args
    , text "co-calls:" <+> ppr cocalled
    , text "arities:" <+> ppr arities
    ]
