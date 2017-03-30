module Usage where

import BasicTypes
import Binary
import Maybes ( expectJust )
import Outputable

import Data.Function ( on )

-- * Types

type Use = Arity

data Usage
  = Zero
  | One {-# UNPACK #-} !Use
  | Many {-# UNPACK #-} !Use
  deriving (Eq, Show)

use :: Usage -> Maybe Use
use (One u) = Just u
use (Many u) = Just u
use _ = Nothing

data UsageSig
  = BotUsageSig -- ^ All further args absent
  | TopUsageSig -- ^ All further args used many times
  | ArgUsage !Usage !UsageSig -- ^ Specific arg use
  deriving (Eq, Show)

-- * Lattice operations

topUse :: Use
topUse = 0

-- TODO: decide if botUse would be valuable, and if so, change @Use@ to an
-- appropriate integer type with pos. Inf.

lubUse :: Use -> Use -> Use
lubUse = min

botUsage :: Usage
botUsage = Zero

topUsage :: Usage
topUsage = Many topUse

lubUsage :: Usage -> Usage -> Usage
lubUsage Zero u = u
lubUsage u Zero = u
lubUsage (One u1) (One u2) = One (lubUse u1 u2)
lubUsage u1 u2 = Many (extractAndLubUse u1 u2)
  where
    extractAndLubUse = lubUse `on` expectJust ": Zero has no use" . use

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

instance Outputable Usage where
  ppr Zero = text "A"
  ppr (One u) = text "1*" <> pprUse u
  ppr (Many u) = pprUse u

instance Outputable UsageSig where
  ppr BotUsageSig = text "AA.."
  ppr TopUsageSig = text "UU.."
  ppr (ArgUsage u sig) = ppr u <> ppr sig

-- * Serialization

-- | Mostly important for serializing @UsageSig@ in interface files.
instance Binary Usage where
  put_ bh Zero = putByte bh 0
  put_ bh (One use) = putByte bh 1 >> put_ bh use
  put_ bh (Many use) = putByte bh 2 >> put_ bh use
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return Zero
      1 -> One <$> get bh
      _ -> Many <$> get bh

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
