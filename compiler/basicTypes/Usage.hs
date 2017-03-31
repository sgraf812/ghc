module Usage where

import BasicTypes
import Binary
import Maybes ( expectJust )
import Outputable

import Data.Function ( on )

-- * Types

type Use = Arity

data Multiplicity
  = Once
  | Many
  deriving (Eq, Ord, Show)

data Usage
  = Absent
  | Used Multiplicity {-# UNPACK #-} !Use
  deriving (Eq, Show)

use :: Usage -> Maybe Use
use (Used _ u) = Just u
use _ = Nothing

data UsageSig
  = BotUsageSig -- ^ All further args absent
  | TopUsageSig -- ^ All further args used many times
  | ArgUsage !Usage !UsageSig -- ^ Specific arg use
  deriving (Eq, Show)

-- * Lattice operations

-- TODO: decide if botUse would be valuable, and if so, change @Use@ to an
-- appropriate integer type with pos. Inf.

topUse :: Use
topUse = 0

lubUse :: Use -> Use -> Use
lubUse = min

botMultiplicity :: Multiplicity
botMultiplicity = Once

topMultiplicity :: Multiplicity
topMultiplicity = Many

lubMultiplicity :: Multiplicity -> Multiplicity -> Multiplicity
lubMultiplicity Once m = m
lubMultiplicity m Once = m
lubMultiplicity _ _    = Many

botUsage :: Usage
botUsage = Absent

topUsage :: Usage
topUsage = Used topMultiplicity topUse

lubUsage :: Usage -> Usage -> Usage
lubUsage Absent u = u
lubUsage u Absent = u
lubUsage (Used m1 u1) (Used m2 u2) = Used (lubMultiplicity m1 m2) (lubUse u1 u2)

botUsageSig :: UsageSig
botUsageSig = BotUsageSig

topUsageSig :: UsageSig
topUsageSig = TopUsageSig

lubUsageSig :: UsageSig -> UsageSig -> UsageSig
lubUsageSig BotUsageSig s = s
lubUsageSig s BotUsageSig = s
lubUsageSig TopUsageSig _ = TopUsageSig
lubUsageSig _ TopUsageSig = TopUsageSig
lubUsageSig (ArgUsage u1 s1) (ArgUsage u2 s2) = ArgUsage (lubUsage u1 u2) (lubUsageSig s1 s2)

-- * Working with @Use@, @Usage@ and @UsageSig@

mapUseArity :: (Arity -> Arity) -> Use -> Use
mapUseArity f use = f use

consUsageSig :: Usage -> UsageSig -> UsageSig
consUsageSig u s
  | u == botUsage
  , s == botUsageSig
  = botUsageSig

  | u == topUsage
  , s == topUsageSig
  = topUsageSig

  | otherwise
  = ArgUsage u s

unconsUsageSig :: UsageSig -> (Usage, UsageSig)
unconsUsageSig BotUsageSig = (botUsage, BotUsageSig)
unconsUsageSig TopUsageSig = (topUsage, TopUsageSig)
unconsUsageSig (ArgUsage u s) = (u, s)

trimUsageSig :: Arity -> UsageSig -> UsageSig
trimUsageSig 0 _ = topUsageSig
trimUsageSig _ TopUsageSig = topUsageSig
trimUsageSig arity sig = consUsageSig headUsage (trimUsageSig (arity - 1) tailUsage)
  where
    (headUsage, tailUsage) = unconsUsageSig sig

-- * Pretty-printing

-- | Formats use like a Call demand.
pprUse :: Use -> SDoc
pprUse 0 = text "U"
pprUse u = text "C" <> parens (pprUse (u - 1))

instance Outputable Multiplicity where
  ppr Once = text "1"
  ppr Many = text "ω"

instance Outputable Usage where
  ppr Absent = text "A"
  ppr (Used multi use) = ppr multi <> char '*' <> pprUse use

instance Outputable UsageSig where
  ppr BotUsageSig = text "A,A.."
  ppr TopUsageSig = text "U,U.."
  ppr (ArgUsage u sig) = ppr u <> char ',' <> ppr sig

-- * Serialization

-- | Mostly important for serializing @UsageSig@ in interface files.
instance Binary Multiplicity where
  put_ bh Once = putByte bh 0
  put_ bh Many = putByte bh 1
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return Once
      _ -> return Many

-- | Mostly important for serializing @UsageSig@ in interface files.
instance Binary Usage where
  put_ bh Absent = putByte bh 0
  put_ bh (Used multi use) = putByte bh 1 >> put_ bh multi >> put_ bh use
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return Absent
      _ -> Used <$> get bh <*> get bh

instance Binary UsageSig where
  put_ bh BotUsageSig = putByte bh 0
  put_ bh TopUsageSig = putByte bh 1
  put_ bh (ArgUsage u sig) = putByte bh 2 >> put_ bh u >> put_ bh sig
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return BotUsageSig
      1 -> return TopUsageSig
      _ -> ArgUsage <$> get bh <*> get bh
