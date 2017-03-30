module CallArity.Types where

import BasicTypes
import CoreArity ( typeArity )
import CoreSyn
import Id
import Outputable
import UnVarGraph
import Usage
import VarEnv

---------------------------------------
-- Functions related to UsageType --
---------------------------------------

-- Result type for the two analyses.
-- See Note [Analysis I: The arity analyis]
-- and Note [Analysis II: The Co-Called analysis]
data UsageType
  = UT
  { ut_cocalled :: !UnVarGraph
  -- ^ Models cardinality, e.g. at most {1, many} via the co-call relation for
  -- _interesting_ variables
  , ut_uses :: !(VarEnv Use)
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

-- Which bindings should we look at?
-- See Note [Which variables are interesting]
isInteresting :: Var -> Bool
isInteresting v = not $ null (typeArity (idType v))

emptyUsageType :: UsageType
emptyUsageType = UT emptyUnVarGraph emptyVarEnv topUsageSig

unitUsageType :: Id -> Use -> UsageType
unitUsageType id use = emptyUsageType { ut_uses = unitVarEnv id use }

unusedArgsUsageType :: Arity -> UsageType
unusedArgsUsageType arity = trimArgs arity (unusedArgs emptyUsageType)

unusedArgs :: UsageType -> UsageType
unusedArgs ut = ut { ut_args = botUsageSig }

trimArgs :: Int -> UsageType -> UsageType
trimArgs arity = modifyArgs (trimUsageSig arity)

typeDelList :: [Id] -> UsageType -> UsageType
typeDelList ids ae = foldr typeDel ae ids

typeDel :: Id -> UsageType -> UsageType
typeDel id (UT g ae args) = UT (g `delNode` id) (ae `delVarEnv` id) args

domType :: UsageType -> UnVarSet
domType ca_type = varEnvDom (ut_uses ca_type)

makeIdArg :: Id -> UsageType -> UsageType
makeIdArg id ut = typeDel id (modifyArgs (consUsageSig (lookupUsage ut id)) ut)

-- In the result, find out the minimum arity and whether the variable is called
-- at most once.
lookupUsage :: UsageType -> Id -> Usage
lookupUsage (UT g ae _) id = case lookupVarEnv ae id of
  Just a
    | id `elemUnVarSet` neighbors g id -> Many a
    | otherwise -> One a
  Nothing
    | isInteresting id -> botUsage
    -- If v is boring, we will not find it in ut_usage, but always assume topUsage.
    -- See Note [Taking boring variables into account]
    | otherwise -> topUsage

calledWith :: UsageType -> Id -> UnVarSet
calledWith ut id
  | isInteresting id
  = neighbors (ut_cocalled ut) id
  | otherwise
  = domType ut

addCrossCoCalls :: UnVarSet -> UnVarSet -> UsageType -> UsageType
addCrossCoCalls set1 set2
  = modifyCoCalls (completeBipartiteGraph set1 set2 `unionUnVarGraph`)

-- Replaces the co-call graph by a complete graph (i.e. no information)
calledMultipleTimes :: UsageType -> UsageType
calledMultipleTimes res = modifyCoCalls (const (completeGraph (domType res))) res

-- Used for application and cases
both :: UsageType -> UsageType -> UsageType
both r1 r2 = addCrossCoCalls (domType r1) (domType r2) ((r1 `lubType` r2) { ut_args = ut_args r1 })

-- Used when combining results from alternative cases; take the minimum
lubType :: UsageType -> UsageType -> UsageType
lubType (UT g1 ae1 args1) (UT g2 ae2 args2)
  = UT (g1 `unionUnVarGraph` g2) (ae1 `lubUseEnv` ae2) (lubUsageSig args1 args2)

lubUseEnv :: VarEnv Use -> VarEnv Use -> VarEnv Use
lubUseEnv = plusVarEnv_C lubUse

lubTypes :: [UsageType] -> UsageType
lubTypes = foldl lubType (unusedArgs emptyUsageType)

-- | Peels off a single argument usage from the signature, corresponding to how
-- @App f a@ uses @a@ under the given incoming arity.
peelUsageType :: UsageType -> (Usage, UsageType)
peelUsageType ut = (usg, ut { ut_args = args' })
  where
    (usg, args') = unconsUsageSig (ut_args ut)

-- * Pretty-printing

instance Outputable UsageType where
  ppr (UT cocalled arities args) = vcat
    [ text "arg usages:" <+> ppr args
    , text "co-calls:" <+> ppr cocalled
    , text "arities:" <+> ppr arities
    ]
