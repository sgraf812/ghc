module Usage
  ( Multiplicity (..)
  , botMultiplicity, topMultiplicity, lubMultiplicity
  , SingleUse
  , topSingleUse, lubSingleUse, bothSingleUse, abstractSingleUse, applySingleUse
  , Usage (..)
  , multiplicity, botUsage, topUsage, lubUsage, bothUsage, manifyUsage, expandArity
  , UsageSig
  , botUsageSig, topUsageSig, lubUsageSig, consUsageSig, unconsUsageSig, manifyUsageSig
  , trimSingleUse, trimUsage, trimUsageSig
  ) where

import BasicTypes
import Binary
import Outputable

-- * Types

data Multiplicity
  = Once
  | Many
  deriving (Eq, Ord, Show)

-- | A @SingleUse@ describes how an expression is used, after it hit WHNF.
-- Some examples:
--
--    * A single use of @seq a b@ unleashes nothing beyond the WHNF use on @a@,
--      but uses @b@ fully, in an unspecified manner.
--    * A single use of @f x@ unleashes, beyond evaluation to WHNF, a call use
--      on @f@, where the result of the call (e.g. the lambda body) is used once.
--
-- The @Ord@ instance is incompatible with the lattice and only used when
-- acting as a key type in a map.
data SingleUse
  = HeadUse
  -- ^ A @SingleUse@ which just evaluates the expression to WHNF. No resulting
  -- lambdas are called and usage of all product components is absent.
  | Call !Multiplicity !SingleUse
  -- ^ @Call m u@ denotes a @SingleUse@ where, after hitting WHNF, the lambda
  -- body is used according to @u@ with multiplicity @m@. @Call Many u@ would
  -- mean the expression was called potentially many times, after being brought
  -- to WHNF.
  --
  -- Use @abstractSingleUse@ to introduce this constructor and
  -- @abstractSingleUse@ to eliminate @Call@s.
  | TopUse
  -- ^ A @SingleUse@ where, after hitting WHNF of the expression,
  -- we don't know any further details of how
  --
  --     * a resulting nested lambda body is used
  --     * resulting product components are used
  deriving (Eq, Ord, Show)

-- | @Id@entifiers can be used multiple times and are the only means to
-- introduce sharing of work, evaluating expressions into WHNF, that is.
-- @Usage@ can track how often an identifier was used and how each of the
-- @SingleUse@s looked like.
--
-- The @Ord@ instance is incompatible with the lattice and only used when
-- acting as a key type in a map.
data Usage
  = Absent
  | Used !Multiplicity !SingleUse
  deriving (Eq, Ord, Show)

multiplicity :: Usage -> Maybe Multiplicity
multiplicity (Used m _) = Just m
multiplicity _ = Nothing

singleUse :: Usage -> Maybe SingleUse
singleUse (Used _ u) = Just u
singleUse _ = Nothing

-- | The constructors should not be exported. Use @consUsageSig@ and
-- @unconsUsageSig@ instead, or else the derived @Eq@ instance is invalid.
data UsageSig
  = BotUsageSig -- ^ All further args absent
  | TopUsageSig -- ^ All further args used many times
  | ArgUsage !Usage !UsageSig -- ^ Specific arg use
  deriving (Eq, Show)

-- * Lattice operations

botMultiplicity :: Multiplicity
botMultiplicity = Once

topMultiplicity :: Multiplicity
topMultiplicity = Many

lubMultiplicity :: Multiplicity -> Multiplicity -> Multiplicity
lubMultiplicity Once m = m
lubMultiplicity m Once = m
lubMultiplicity _ _    = Many

botSingleUse :: SingleUse
botSingleUse = HeadUse

topSingleUse :: SingleUse
topSingleUse = TopUse

lubSingleUse :: SingleUse -> SingleUse -> SingleUse
lubSingleUse TopUse _ = TopUse
lubSingleUse _ TopUse = TopUse
lubSingleUse HeadUse u = u
lubSingleUse u HeadUse = u
lubSingleUse (Call m1 u1) (Call m2 u2) = Call (lubMultiplicity m1 m2) (lubSingleUse u1 u2)

-- | Think 'plus' on @SingleUse@s, for sequential composition.
bothSingleUse :: SingleUse -> SingleUse -> SingleUse
bothSingleUse TopUse _ = TopUse
bothSingleUse _ TopUse = TopUse
bothSingleUse HeadUse u = u
bothSingleUse u HeadUse = u
bothSingleUse (Call _ u1) (Call _ u2) = Call Many (lubSingleUse u1 u2)

botUsage :: Usage
botUsage = Absent

topUsage :: Usage
topUsage = Used topMultiplicity topSingleUse

lubUsage :: Usage -> Usage -> Usage
lubUsage Absent u = u
lubUsage u Absent = u
lubUsage (Used m1 u1) (Used m2 u2) = Used (lubMultiplicity m1 m2) (lubSingleUse u1 u2)

-- | Think 'plus' on @Usage@s, for sequential composition.
-- E.g. if @Usage@s from scrutinee and case branches should be combined.
bothUsage :: Usage -> Usage -> Usage
bothUsage Absent u = u
bothUsage u Absent = u
bothUsage (Used _ u1) (Used _ u2) = Used Many (bothSingleUse u1 u2)

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

-- | Abstracts the given @SingleUse@ as a singular body @Usage@ behind a
-- lambda binder. This is useful in the @App@lication rule.
abstractSingleUse :: SingleUse -> SingleUse
abstractSingleUse use = Call Once use

-- | Dual to @abstractSingleUse@, this will return the @Usage@ of the lambda body,
-- relative to the given single @Use@ of the outer expression. Useful in the
-- @Lam@bda rule.
applySingleUse :: SingleUse -> Usage
applySingleUse HeadUse = Absent -- The lambda will be reduced to WHNF, but the body will stay untouched.
applySingleUse (Call multi use) = Used multi use
applySingleUse _ = topUsage

trimSingleUse :: Arity -> SingleUse -> SingleUse
trimSingleUse arity (Call m body)
  | arity > 0 = Call m (trimSingleUse (arity - 1) body)
trimSingleUse _ _ = topSingleUse

trimUsage :: Arity -> Usage -> Usage
trimUsage arity (Used m use) = Used m (trimSingleUse arity use)
trimUsage arity usg = usg

-- | @manifyUsage u = bothUsage u u@. For when an id is used more than once
-- with the same @Usage@. This is different than just changing the top-level
-- @Multiplicity@ to @Many@, which would correspond to an additional @seq@
-- @Usage@ of the top-level expression (e.g. without applying any args).
manifyUsage :: Usage -> Usage
manifyUsage u = bothUsage u u

expandArity :: Usage -> Arity -> Arity
expandArity Absent cheap_arity
  -- We could potentially expand as far as we want, since the result doesn't
  -- seem to be used. This happens when doing something like @seq (f 1 2) e@,
  -- where @e@ doesn't contain any reference to @f@. We *could* expand @f@,
  -- but that would be counter-intuitive, since someone who writes such code
  -- would expect that the call to @seq@ reduces something.
  = cheap_arity
expandArity (Used Many _) 0
  -- This is a special case, accounting for the fact that let-bindings
  -- are evaluated at most once. Consider @f `seq` ... f x ... @: @seq@ makes
  -- it possible to end up with an @Usage@ of @Used Many (Call Once TopUse)@,
  -- where the outer @Multiplicity@ and the top-level one-shot @Multiplicity@
  -- are out of sync. Eta-expansion would be counter-intuitive, as the lifted
  -- abstraction would hide the work which we wanted to evaluate strictly.
  -- Thus we don't eta-expand:
  = 0
expandArity (Used _ u) cheap_arity
  = impl u cheap_arity
  where
    impl HeadUse cheap_arity -- the application expression we accumulated does non-trivial work, so
      -- Same reason as for the above @Absent@ case
      = cheap_arity
    impl TopUse cheap_arity
      -- No chance we can expand anything
      = cheap_arity
    impl (Call Many u) 0
      -- the application expression we accumulated does non-trivial work,
      -- which we aren't allowed to push into a non-one-shot lambda. So
      -- we don't expand any further.
      = 0
    impl (Call _ u) cheap_arity
      -- This is the case that may actually expand arity:
      -- When we're out of @cheap_arity@ here, we may expand nonetheless.
      -- It's OK to push work into a one-shot lambda, or to expand as long
      -- as the accumulated application expression is cheap.
      = 1 + impl u (max 0 (cheap_arity - 1))

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

-- | Maps @manifyUsage@ over each argument usage.
manifyUsageSig :: UsageSig -> UsageSig
manifyUsageSig TopUsageSig = TopUsageSig
manifyUsageSig BotUsageSig = BotUsageSig
manifyUsageSig (ArgUsage u s) = consUsageSig (manifyUsage u) (manifyUsageSig s)

-- | Trims a @UsageSig@ by looking at how the associated value is used.
--
-- The resulting @UsageSig@ will only have as many arguments as the @SingleUse@ has
-- call nestings.
trimUsageSig :: SingleUse -> UsageSig -> UsageSig
trimUsageSig _ BotUsageSig = BotUsageSig
trimUsageSig HeadUse _ = BotUsageSig -- Since the result isn't forced beyond WHNF, no further argument will
trimUsageSig _ TopUsageSig = TopUsageSig
trimUsageSig (Call _ u) sig = consUsageSig head_usage (trimUsageSig u tail_usage)
  where
    (head_usage, tail_usage) = unconsUsageSig sig
trimUsageSig _ _ = TopUsageSig

-- * Pretty-printing

instance Outputable Multiplicity where
  ppr Once = text "1"
  ppr Many = text "ω"

instance Outputable SingleUse where
  ppr HeadUse = text "HU"
  ppr TopUse = text "U"
  ppr (Call multi body) = text "C^" <> ppr multi <> parens (ppr body)

instance Outputable Usage where
  ppr Absent = text "A"
  ppr (Used multi use) = ppr multi <> char '*' <> ppr use

pprEllipsis :: Usage -> SDoc
pprEllipsis usage = ppr usage <> char ',' <> ppr usage <> text ".."

instance Outputable UsageSig where
  ppr BotUsageSig = pprEllipsis botUsage
  ppr TopUsageSig = pprEllipsis topUsage
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
instance Binary SingleUse where
  put_ bh HeadUse = putByte bh 0
  put_ bh TopUse = putByte bh 1
  put_ bh (Call multi use) = putByte bh 2 >> put_ bh multi >> put_ bh use
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return HeadUse
      1 -> return TopUse
      _ -> Call <$> get bh <*> get bh

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
