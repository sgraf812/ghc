module UsageAnal.Types where

import BasicTypes
import CoreSyn
import FamInstEnv
import Id
import Outputable
import Usage
import VarEnv
import WwLib ( findTypeShape )

import Data.List ( foldl', foldl1' )

---------------------------------------
-- Functions related to UsageType    --
---------------------------------------

-- Result type for the two analyses.
-- See Note [Analysis I: The arity analyis]
-- and Note [Analysis II: The Co-Called analysis]
data UsageType
  = UT
  { ut_usages     :: !(VarEnv Usage)
  -- ^ Models the usage an `Id` was exposed to
  , ut_args     :: !UsageSig
  -- ^ Collects the signature for captured lambda binders
  }

modifyArgs :: (UsageSig -> UsageSig) -> UsageType -> UsageType
modifyArgs modifier ut = ut { ut_args = modifier (ut_args ut) }

-- | How an expression uses its interesting variables
-- and the elaborated expression with annotated Ids
type AnalResult = (UsageType, CoreExpr)

emptyUsageType :: UsageType
emptyUsageType = UT emptyVarEnv topUsageSig

botUsageType :: UsageType
botUsageType = unusedArgs emptyUsageType

unitUsageType :: Id -> Use -> UsageType
unitUsageType id use = emptyUsageType { ut_usages = unitVarEnv id (Used Once use) }

unusedArgs :: UsageType -> UsageType
unusedArgs ut = ut { ut_args = botUsageSig }

forgetFreeVarUsages :: UsageType -> UsageType
forgetFreeVarUsages ut = botUsageType { ut_args = ut_args ut }

delUsageTypes :: [Id] -> UsageType -> UsageType
delUsageTypes ids ut = foldr delUsageType ut ids

delUsageType :: Id -> UsageType -> UsageType
delUsageType id (UT usages args) = UT (usages `delVarEnv` id) args

-- | See Note [Trimming a demand to a type] in Demand.hs.
trimUsageToTypeShape :: FamInstEnvs -> Id -> Usage -> Usage
trimUsageToTypeShape fam_envs id = trimUsage (findTypeShape fam_envs (idType id))

-- In the result, find out the minimum arity and whether the variable is called
-- at most once.
lookupUsage :: RecFlag -> FamInstEnvs -> UsageType -> Id -> Usage
lookupUsage rec_flag fam_envs ut id = trimUsageToTypeShape fam_envs id usage 
  where
    usage = case lookupVarEnv (ut_usages ut) id of
      Just usage
        -- we assume recursive bindings to be called multiple times, what's the
        -- point otherwise? It's a little sad we don't encode it in the co-call
        -- graph directly, though.
        -- See Note [Thunks in recursive groups]
        | isRec rec_flag -> manifyUsage usage
        | otherwise -> usage
      Nothing -> botUsage

-- Replaces the co-call graph by a complete graph (i.e. no information)
multiplyUsages :: Multiplicity -> UsageType -> UsageType
multiplyUsages Once ut = ut
multiplyUsages Many (UT usages args)
  = UT
  { ut_usages = mapVarEnv (\usage -> bothUsage usage usage) usages
  , ut_args = manifyUsageSig args
  }

bothUsageTypes :: [UsageType] -> UsageType
bothUsageTypes = foldl1' bothUsageType

-- | Corresponds to sequential composition of expressions.
-- Used for application and cases.
-- Note this returns the @UsageSig@ from the first argument.
bothUsageType :: UsageType -> UsageType -> UsageType
bothUsageType (UT u1 args) (UT u2 _)
  = UT
  { ut_usages = bothUseEnv u1 u2
  , ut_args = args
  }

-- | Used when combining results from alternative cases
lubUsageType :: UsageType -> UsageType -> UsageType
lubUsageType (UT u1 args1) (UT u2 args2)
  = UT
  { ut_usages = lubUseEnv u1 u2
  , ut_args = lubUsageSig args1 args2
  }

lubUseEnv :: VarEnv Usage -> VarEnv Usage -> VarEnv Usage
lubUseEnv = plusVarEnv_C lubUsage

bothUseEnv :: VarEnv Usage -> VarEnv Usage -> VarEnv Usage
bothUseEnv = plusVarEnv_C bothUsage

lubUsageTypes :: [UsageType] -> UsageType
lubUsageTypes = foldl' lubUsageType botUsageType

-- | Peels off a single argument usage from the signature, corresponding to how
-- @App f a@ uses @a@ under the given incoming arity.
peelArgUsage :: UsageType -> (Usage, UsageType)
peelArgUsage ut = (usg, ut { ut_args = args' })
  where
    (usg, args') = unconsUsageSig (ut_args ut)

-- * Pretty-printing

instance Outputable UsageType where
  ppr (UT usages args) = vcat
    [ text "arg usages:" <+> ppr args
    , text "usages:" <+> ppr usages
    ]
