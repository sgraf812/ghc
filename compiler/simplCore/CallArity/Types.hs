module CallArity.Types where

import Maybes
import Outputable
import Binary

---------------------------------------
-- Functions related to CallArityType --
---------------------------------------

-- Result type for the two analyses.
-- See Note [Analysis I: The arity analyis]
-- and Note [Analysis II: The Co-Called analysis]
data Cardinality
  = Zero
  | One {-# UNPACK #-} !Arity
  | Many {-# UNPACK #-} !Arity
  deriving (Eq, Show)

arity :: Cardinality -> Maybe Arity
arity (One a) = Just a
arity (Many a) = Just a
arity _ = Nothing

lubCardinality :: Cardinality -> Cardinality -> Cardinality
lubCardinality Zero u = u
lubCardinality u Zero = u
lubCardinality (One arity1) (One arity2) = One (min arity1 arity2)
lubCardinality = Many . min `on` expectJust ": Zero has no arity" . arity

botCardinality :: Cardinality
botCardinality = Zero

topCardinality :: Cardinality
topCardinality = Many 0

type CardinalitySig = [Cardinality]

topCardinalitySig :: CardinalitySig
topCardinalitySig = []

data CallArityType
  = CAT
  { cat_cocalled :: UnVarGraph -- ^ Models cardinality, e.g. 1, many via the co-call relation for _interesting_ variables
  , cat_arities :: VarEnv Arity -- ^ Models per var usage and absence (card 0)
  , cat_args :: CardinalitySig -- ^ Collects the signature for captured lambda binders
  }

-- | How an expression uses its interesting variables
-- and the elaborated expression with annotated Ids
type AnalResult = (CallArityType, CoreExpr)

emptyArityType :: CallArityType
emptyArityType = CAT emptyUnVarGraph emptyVarEnv topCardinalitySig

unitArityType :: Var -> Arity -> CallArityType
unitArityType v arity = emptyArityType { cat_arities = unitVarEnv v arity }

unusedArgsArityType :: Int -> CallArityType
unusedArgsArityType arity = trimArgs arity (unusedArgs emptyArityType)

unusedArgs :: CallArityType -> CallArityType
unusedArgs cat = cat { cat_args = repeat Zero }

trimArgs :: Int -> CallArityType -> CallArityType
trimArgs arity cat = cat { cat_args = take arity (cat_args cat) }

typeDelList :: [Var] -> CallArityType -> CallArityType
typeDelList vs ae = foldr typeDel ae vs

typeDel :: Var -> CallArityType -> CallArityType
typeDel v (CAT g ae args) = CAT (g `delNode` v) (ae `delVarEnv` v) args

domType :: CallArityType -> UnVarSet
domType ca_type = varEnvDom (cat_arities ca_type)

makeIdArg :: Id -> CallArityType -> CallArityType
makeIdArg id ca_type = typeDel id ca_type
  { cat_args = lookupCallArityType ca_type id : cat_args ca_type }

-- In the result, find out the minimum arity and whether the variable is called
-- at most once.
lookupCallArityType :: CallArityType -> Var -> Cardinality
lookupCallArityType (CAT g ae _) v = case lookupVarEnv ae v of
  Just a
    | v `elemUnVarSet` neighbors g v -> Many a
    | otherwise -> One a
  Nothing
    | isInteresting v -> botCardinality
    -- If v is boring, we will not find it in cat_usage, but always assume topCardinality.
    -- See Note [Taking boring variables into account]
    | otherwise -> topCardinality

calledWith :: CallArityType -> Var -> UnVarSet
calledWith ca_type v
  | isInteresting v
  = neighbors (cat_cocalled ca_type) v
  | otherwise
  = domType ca_type

modifyCoCalls :: (UnVarGraph -> UnVarGraph) -> CallArityType -> CallArityType
modifyCoCalls modifier ca_type
  = ca_type { cat_cocalled = modifier (cat_cocalled ca_type) }

addCrossCoCalls :: UnVarSet -> UnVarSet -> CallArityType -> CallArityType
addCrossCoCalls set1 set2
  = modifyCoCalls (completeBipartiteGraph set1 set2 `unionUnVarGraph`)

-- Replaces the co-call graph by a complete graph (i.e. no information)
calledMultipleTimes :: CallArityType -> CallArityType
calledMultipleTimes res = modifyCoCalls (const (completeGraph (domType res))) res

-- Used for application and cases
both :: CallArityType -> CallArityType -> CallArityType
both r1 r2 = addCrossCoCalls (domType r1) (domType r2) ((r1 `lubType` r2) { cat_args = cat_args r1 })

-- Used when combining results from alternative cases; take the minimum
lubType :: CallArityType -> CallArityType -> CallArityType
lubType (CAT g1 ae1 args1) (CAT g2 ae2 args2) -- both args should really be the same
  = CAT (g1 `unionUnVarGraph` g2) (ae1 `lubArityEnv` ae2) (zipWith lubCardinality args1 args2)

lubArityEnv :: VarEnv Arity -> VarEnv Arity -> VarEnv Arity
lubArityEnv = plusVarEnv_C min

lubTypes :: [CallArityType] -> CallArityType
lubTypes = foldl lubType (unusedArgs emptyArityType) -- note that this isn't safe for empty input, because of unusedArgs.

-- | Peels off a single argument usage from the signature, corresponding to how
-- @App f a@ uses @a@ under the given incoming arity.
peelCallArityType :: CallArityType -> (Cardinality, CallArityType)
peelCallArityType ca_f
  | arg:args <- cat_args ca_f
  -- The called expression had a signature we can return.
  = (arg, ca_f { cat_args = args })

  | otherwise
  -- The called function had no signature or has not
  -- been analysed with high enough incoming arity
  -- (e.g. when loading the signature from an imported id).
  -- ca_f is rather useless for analysing a, so we conservatively
  -- assume topCardinality here.
  = (topCardinality, ca_f)

-- * Pretty-printing

-- | Formats incoming arity like a Call demand.
pprArity :: Arity -> SDoc
pprArity 0 = text "U"
pprArity arity = text "C" <> parens (pprArity (arity - 1))

instance Outputable Cardinality where
  ppr Zero = text "A"
  ppr (One arity) = text "1*" <> pprArity arity
  ppr (Many arity) = pprArity arity

instance Outputable CallArityType where
  ppr (CAT cocalled arities args) =
    text "arg usages:" <+> ppr args
    <+> text "co-calls:" <+> ppr cocalled
    <+> text "arities:" <+> ppr arities

-- | Used for printing top-level cardinality pragmas in interface files
pprIfaceStrictSig :: CardinalitySig -> SDoc
pprIfaceStrictSig = hcat . map ppr

-- * Serialization

instance Binary Cardinality where
  put_ bh Zero = putByte bh 0
  put_ bh (One arity) = putByte bh 1 >> put bh arity
  put_ bh (Many arity) = putByte bh 2 >> put bh arity
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return Zero
      1 -> One <$> get bh
      _ -> Many <$> get bh
