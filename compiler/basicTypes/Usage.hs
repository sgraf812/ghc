module Usage
  ( Multiplicity (..)
  , botMultiplicity, topMultiplicity, lubMultiplicity
  , Use
  , topUse, lubUse, abstractUse, applyUse
  , Usage (..)
  , multiplicity, use, botUsage, topUsage, lubUsage
  , UsageSig
  , botUsageSig, topUsageSig, lubUsageSig, consUsageSig, unconsUsageSig
  , useArity
  , trimUse, trimUsage, trimUsageSig
  ) where

import BasicTypes
import Binary
import Outputable

-- * Types

data Multiplicity
  = Once
  | Many
  deriving (Eq, Ord, Show)

-- | The @Ord@ instance is incompatible with the lattice and only used when
-- acting as a key type in a map.
data Use
  = TopUse
  -- ^ A single use where we don't know any further details of how
  --
  --     * a potential nested lambda body is used
  --     * potential product components are used
  | Call !Usage
  -- ^ A single use where the lambda body is used according to @Usage@.
  deriving (Eq, Ord, Show)

-- | The @Ord@ instance is incompatible with the lattice and only used when
-- acting as a key type in a map.
data Usage
  = Absent
  | Used !Multiplicity !Use
  deriving (Eq, Ord, Show)

multiplicity :: Usage -> Maybe Multiplicity
multiplicity (Used m _) = Just m
multiplicity _ = Nothing

use :: Usage -> Maybe Use
use (Used _ u) = Just u
use _ = Nothing

-- | The constructors should not be exported. Use @consUsageSig@ and
-- @unconsUsageSig@ instead, or else the derived @Eq@ instance is invalid.
data UsageSig
  = BotUsageSig -- ^ All further args absent
  | TopUsageSig -- ^ All further args used many times
  | ArgUsage !Usage !UsageSig -- ^ Specific arg use
  deriving (Eq, Show)

-- * Lattice operations

-- TODO: decide if botUse would be valuable, and if so, change @Use@ to an
-- appropriate integer type with pos. Inf.

topUse :: Use
topUse = TopUse

lubUse :: Use -> Use -> Use
lubUse TopUse _ = TopUse
lubUse _ TopUse = TopUse
lubUse (Call u1) (Call u2) = Call (lubUsage u1 u2)

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

-- | Abstracts the given @Use@ as a singular body @Usage@ behind a
-- lambda binder. This is useful in the @App@lication rule and the only way
-- to introduce a call use.
abstractUse :: Use -> Use
abstractUse use = Call (Used Once use)

-- | Dual to @abstractUse@, this will return the @Usage@ of the lambda body,
-- relative to the given single @Use@ of the outer expression. Useful in the
-- @Lam@bda rule and the only meaningful way to eliminate a call use.
applyUse :: Use -> Usage
applyUse (Call usage) = usage
applyUse _ = topUsage

useArity :: Use -> Arity
useArity (Call (Used _ u)) = 1 + useArity u
useArity _ = 0

trimUse :: Arity -> Use -> Use
trimUse arity (Call usage)
  | arity > 0 = Call (trimUsage (arity - 1) usage)
trimUse _ _ = topUse

trimUsage :: Arity -> Usage -> Usage
trimUsage arity (Used multi use) = Used multi (trimUse arity use)
trimUsage _ u = u

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

-- | Trims a @UsageSig@ by looking at how the associated value is used.
--
-- The resulting @UsageSig@ will only have as many arguments as the @Use@ has
-- call nestings.
trimUsageSig :: Use -> UsageSig -> UsageSig
trimUsageSig _ BotUsageSig = BotUsageSig
trimUsageSig (Call Absent) _ = BotUsageSig -- Since the result isn't forced, no further argument will
trimUsageSig _ TopUsageSig = TopUsageSig
trimUsageSig (Call (Used _ u)) sig = consUsageSig head_usage (trimUsageSig u tail_usage)
  where
    (head_usage, tail_usage) = unconsUsageSig sig
trimUsageSig _ _ = TopUsageSig

-- * Pretty-printing

instance Outputable Multiplicity where
  ppr Once = text "1"
  ppr Many = text "ω"

instance Outputable Use where
  ppr TopUse = text "U"
  ppr (Call usage) = text "C" <> parens (ppr usage)

instance Outputable Usage where
  ppr Absent = text "A"
  ppr (Used multi use) = ppr multi <> char '*' <> ppr use

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
instance Binary Use where
  put_ bh TopUse = putByte bh 0
  put_ bh (Call usage) = putByte bh 1 >> put_ bh usage
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return TopUse
      _ -> Call <$> get bh

-- | Mostly important for serializing @UsageSig@ in interface files.
instance Binary Usage where
  put_ bh Absent = putByte bh 0
  put_ bh (Used multi use) = putByte bh 1 >> put_ bh multi >> put_ bh use
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return Absent
      _ -> Used <$> get bh <*> get bh

-- | Mostly important for serializing @UsageSig@ in interface files.
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
