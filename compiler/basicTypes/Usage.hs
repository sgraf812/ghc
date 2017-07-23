{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fprof-auto #-}

module Usage
  ( Multiplicity (..)
  , botMultiplicity, topMultiplicity, lubMultiplicity
  , Use
  , botUse, topUse, lubUse, leqUse, bothUse, mkCallUse, peelCallUse, mkProductUse, peelProductUse, boundDepth
  , Usage (..)
  , multiplicity, botUsage, topUsage, lubUsage, bothUsage
  , manifyUsage, oneifyUsage, expandArity
  , UsageSig
  , botUsageSig, topUsageSig, lubUsageSig, leqUsageSig
  , consUsageSig, unconsUsageSig, usageSigFromUsages, manifyUsageSig
  , trimUse, trimUsage, trimUsageSig
  , u'1HU, u'1C1U
  , usageFromDemand, overwriteDemandWithUsage, usageSigFromStrictSig, overwriteStrictSigWithUsageSig
  ) where

#include "HsVersions.h"

import BasicTypes
import Binary
import Demand ( TypeShape(..), StrictSig, splitStrictSig )
import qualified Demand
import Outputable
import Util

import Control.Arrow ( second )

-- * Types

data Multiplicity
  = Once
  | Many
  deriving (Eq, Ord, Show)

-- | A `Use` describes how an expression is used, after it hit WHNF.
-- Some examples:
--
--    * A single use of @seq a b@ unleashes nothing beyond the WHNF use on @a@,
--      but uses @b@ fully, in an unspecified manner.
--    * A single use of @f x@ unleashes, beyond evaluation to WHNF, a call use
--      on @f@, where the result of the call (e.g. the lambda body) is used once.
--
-- The `Ord` instance is incompatible with the lattice and only used when
-- acting as a key type in a map.
data Use
  = HeadUse
  -- ^ A `Use` which just evaluates the expression to WHNF. No resulting
  -- lambdas are called and usage of all product components is absent.
  | Call !Multiplicity !Use
  -- ^ @Call m u@ denotes a `Use` where, after hitting WHNF, the lambda
  -- body is used according to @u@ with multiplicity @m@. @Call Many u@ would
  -- mean the expression was called potentially many times, after being brought
  -- to WHNF.
  --
  -- Use `mkCallUse` to introduce this constructor and `peelCallUse` to
  -- eliminate `Call`s.
  | Product ![Usage]
  -- ^ A `Use` which, after evaluating a product constructor, will use the
  -- product's components according to the `Usage`s given.
  --
  -- Use `mkProductUse` to introduce this constructor and `peelProductUse` to
  -- eliminate `Product`s.
  | UnknownUse
  -- ^ A `Use` where, after hitting WHNF of the expression,
  -- we don't know any further details of how
  --
  --     * a resulting nested lambda body is used
  --     * resulting product components are used
  deriving (Eq, Ord, Show)

-- | A smart constructor for `Call` which normalizes according to the equivalence
-- @Call Many UnknownUse = UnknownUse@.
mkCallUse :: Multiplicity -> Use -> Use
mkCallUse Many UnknownUse = UnknownUse
mkCallUse m u = Call m u

-- | A smart constructor for `Product` which normalizes according to the equivalences
-- @Product [topUsage, topUsage..] === topUse@ and
-- @Product [botUsage, botUsage..] === botUse@.
mkProductUse :: [Usage] -> Use
mkProductUse components
  -- Order is important here: We want to regard U() as HU
  | all (== botUsage) components = botUse
  -- This contradicts Note [Don't optimise UProd(Used) to Used], but
  -- I fixed the issue with WW that probably was the reason for the hack.
  | all (== topUsage) components = topUse 
  | otherwise = Product components

-- | `CoreSym.Id`entifiers can be used multiple times and are the only means to
-- introduce sharing of work, evaluating expressions into WHNF, that is.
-- `Usage` can track how often an identifier was used and how each of the
-- `Use`s looked like.
--
-- The `Ord` instance is incompatible with the lattice and only used when
-- acting as a key type in a map.
data Usage
  = Absent
  | Used !Multiplicity !Use
  deriving (Eq, Ord, Show)

multiplicity :: Usage -> Maybe Multiplicity
multiplicity (Used m _) = Just m
multiplicity _ = Nothing

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

botUse :: Use
botUse = HeadUse

topUse :: Use
topUse = UnknownUse

lubUse :: Use -> Use -> Use
lubUse UnknownUse _ = UnknownUse
lubUse _ UnknownUse = UnknownUse
lubUse HeadUse u = u
lubUse u HeadUse = u
lubUse (Product c1) (Product c2)
  | equalLength c1 c2
  -- If this is not true, we probably have uses from different case branches.
  -- In that case, returning topUse is the right thing to do.
  = mkProductUse (zipWith lubUsage c1 c2)
lubUse (Call m1 u1) (Call m2 u2)
  = mkCallUse (lubMultiplicity m1 m2) (lubUse u1 u2)
lubUse _ _ = topUse

leqUse :: Use -> Use -> Bool
leqUse a b = lubUse a b == b

-- | Think \'plus\' on `Use`s, for sequential composition.
bothUse :: Use -> Use -> Use
bothUse UnknownUse _ = UnknownUse
bothUse _ UnknownUse = UnknownUse
bothUse HeadUse u = u
bothUse u HeadUse = u
bothUse (Product c1) (Product c2)
  | equalLength c1 c2
  = mkProductUse (zipWith bothUsage c1 c2)
bothUse (Call _ u1) (Call _ u2)
  = mkCallUse Many (lubUse u1 u2)
bothUse _ _ = topUse

botUsage :: Usage
botUsage = Absent

topUsage :: Usage
topUsage = Used topMultiplicity topUse

lubUsage :: Usage -> Usage -> Usage
lubUsage Absent u = u
lubUsage u Absent = u
lubUsage (Used m1 u1) (Used m2 u2) = Used (lubMultiplicity m1 m2) (lubUse u1 u2)

-- | Think \'plus\' on `Usage`s, for sequential composition.
-- E.g. if `Usage`s from scrutinee and case branches should be combined.
bothUsage :: Usage -> Usage -> Usage
bothUsage Absent u = u
bothUsage u Absent = u
bothUsage (Used _ u1) (Used _ u2) = Used Many (bothUse u1 u2)

botUsageSig :: UsageSig
botUsageSig = BotUsageSig

topUsageSig :: UsageSig
topUsageSig = TopUsageSig

lubUsageSig :: UsageSig -> UsageSig -> UsageSig
lubUsageSig BotUsageSig s = s
lubUsageSig s BotUsageSig = s
lubUsageSig TopUsageSig _ = TopUsageSig
lubUsageSig _ TopUsageSig = TopUsageSig
lubUsageSig (ArgUsage u1 s1) (ArgUsage u2 s2) = consUsageSig (lubUsage u1 u2) (lubUsageSig s1 s2)

leqUsageSig :: UsageSig -> UsageSig -> Bool
leqUsageSig u1 u2 = lubUsageSig u1 u2 == u2

-- * Working with `Use`, `Usage` and `UsageSig`

-- | Eliminates a `Call`. This will return the `Usage` of the lambda body,
-- relative to the given `Use` of the outer expression. Useful in the
-- `CoreSyn.Lam`bda rule.
peelCallUse :: Use -> Maybe Usage
peelCallUse HeadUse = Just Absent -- The lambda will be reduced to WHNF, but the body will stay untouched.
peelCallUse (Call multi use) = Just (Used multi use)
peelCallUse UnknownUse = Just topUsage
peelCallUse _ = Nothing

-- | @peelProductUse len_hint use@ tries to treat @use@ as a product use and
-- returns the list of usages on its components. It will adhere to the @len_hint@,
-- meaning that the @product_use@ is constrained to have that length.
-- This is mostly so that `botUse` and `topUse`, oblivious to length
-- information, can be translated (back) into a product use.
--
-- Examples:
--
--    - @peelProductUse (length comps) (mkProductUse comps) == Just comps@
--    - @peelProductUse n topUse == Just (replicate n topUsage)@
--    - @peelProductUse n (mkCallUse Once topUse) == Nothing@
peelProductUse :: Arity -> Use -> Maybe [Usage]
peelProductUse n HeadUse = Just (replicate n botUsage)
peelProductUse n UnknownUse = Just (replicate n topUsage)
peelProductUse n (Product comps) | comps `lengthIs` n = Just comps
peelProductUse _ _ = Nothing -- type error, might happen with GADTs and unsafeCoerce (#9208)

-- | Since the lattice modeled by `Use` has infinite height, we run might
-- run into trouble regarding convergence. This happens in practice for product
-- usages on lazy infinite stream functions such as `filter`, where the recursion
-- propagates strictly increasing product use chains for the argument.
-- That would never converge, so at some point we have to artificially bound
-- the height of the lattice.
--
-- Although there also may be infinitely many nested Calls, we don't need to
-- worry about them, since there should be no program for which the analysis
-- constructs an infinite chain of Calls.
boundDepth :: Int -> Use -> Use
boundDepth max_height use = snd (boundUse 0 use)
  where
    wrap impl height u -- simple caching wrapper around the actual impl
      | ret@(True, _) <- impl height u
      = ret
      | otherwise
      = (False, u)
    boundUsage = wrap impl
      where
        impl height (Used m u) = second (Used m) (boundUse height u)
        impl _ u = (False, u)
    boundUse = wrap impl
      where
        impl height (Product comps)
          | height < max_height
          , (changed, comps') <- mapAndUnzip (boundUsage (height + 1)) comps
          = (or changed, mkProductUse comps')
          | otherwise
          = (True, topUse)
        impl height (Call m u) = second (mkCallUse m) (boundUse height u)
        impl _ u = (False, u)

trimUseBounded :: Int -> TypeShape -> Use -> Use
trimUseBounded _ _ HeadUse = HeadUse
trimUseBounded d (TsFun shape) u
  -- Infinite arity is prohibited by the type system, so we don't have to modify d here
  | Just (Used m body) <- peelCallUse u
  = mkCallUse m (trimUseBounded d shape body)
trimUseBounded d (TsProd shapes) u
  -- TsProd may be infinitely deep, so we have to cut off at some point
  | d < 10
  , Just comps <- peelProductUse (length shapes) u
  = mkProductUse (zipWith (trimUsageBounded (d+1)) shapes comps)
trimUseBounded _ _ _ = topUse 
    
trimUsageBounded :: Int -> TypeShape -> Usage -> Usage
trimUsageBounded d shape (Used m use) = Used m (trimUseBounded d shape use)
trimUsageBounded _ _ usg = usg

trimUse :: TypeShape -> Use -> Use
trimUse = trimUseBounded 0 

trimUsage :: TypeShape -> Usage -> Usage
trimUsage = trimUsageBounded 0

-- | @manifyUsage u = bothUsage u u@. For when an id is used more than once
-- with the same `Usage`. This is different than just changing the top-level
-- `Multiplicity` to `Many`, which would correspond to an additional `seq`
-- `Usage` of the top-level expression (e.g. without applying any args).
manifyUsage :: Usage -> Usage
manifyUsage u = bothUsage u u

oneifyUsage :: Usage -> Usage
oneifyUsage Absent = Absent
oneifyUsage (Used _ use) = Used Once use

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
  -- it possible to end up with an `Usage` of @Used Many (Call Once UnknownUse)@,
  -- where the outer @Multiplicity@ and the top-level one-shot @Multiplicity@
  -- are out of sync. Eta-expansion would be counter-intuitive, as the lifted
  -- abstraction would hide the work which we wanted to evaluate strictly.
  -- Thus we don't eta-expand:
  = 0
expandArity (Used _ u) cheap_arity
  = impl u cheap_arity
  where
    impl HeadUse cheap_arity
      -- Same reason as for the above @Absent@ case, we can expand arbitrarily. 
      -- Although for the cheap_arity = 0 case, we *should* not expand at all,
      -- because that would yield surprising behavior.
      = cheap_arity
    impl (Call Many _) 0
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
    impl _ cheap_arity
      -- No chance we can expand anything
      = cheap_arity

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

usageSigFromUsages :: [Usage] -> UsageSig
usageSigFromUsages = foldr consUsageSig topUsageSig

-- | Maps @manifyUsage@ over each argument usage.
manifyUsageSig :: UsageSig -> UsageSig
manifyUsageSig TopUsageSig = TopUsageSig
manifyUsageSig BotUsageSig = BotUsageSig
manifyUsageSig (ArgUsage u s) = consUsageSig (manifyUsage u) (manifyUsageSig s)

-- | Trims a `UsageSig` by arity, so that any arguments beyond that arity get `topUsage`.
--
-- It holds that @forall n. trimUsage n sig `leqUsageSig` sig@.
trimUsageSig :: Arity -> UsageSig -> UsageSig
trimUsageSig 0 _ = TopUsageSig
trimUsageSig _ TopUsageSig = TopUsageSig
trimUsageSig n sig = consUsageSig head_usage (trimUsageSig (n-1) tail_usage)
  where
    (head_usage, tail_usage) = unconsUsageSig sig

-- * Specific `Usage`s/`Use`s

-- | `Usage` unleashed on `x` in @x `seq` ...@.
u'1HU:: Usage
u'1HU = Used Once HeadUse

-- | 'Called once with one argument' `Usage`: @1*C^1(U)@
u'1C1U :: Usage
u'1C1U = Used Once (mkCallUse Once topUse)

-- * Pretty-printing

instance Outputable Multiplicity where
  ppr Once = text "1"
  ppr Many = text "w"

instance Outputable Use where
  ppr HeadUse = text "HU"
  ppr UnknownUse = text "U"
  ppr (Product components) = text "U" <> parens (hcat (punctuate (char ',') (map ppr components)))
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

-- | Mostly important for serializing `UsageSig` in interface files.
instance Binary Multiplicity where
  put_ bh Once = putByte bh 0
  put_ bh Many = putByte bh 1
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return Once
      _ -> return Many

-- | Mostly important for serializing `UsageSig` in interface files.
instance Binary Use where
  put_ bh HeadUse = putByte bh 0
  put_ bh UnknownUse = putByte bh 1
  put_ bh (Product components) = putByte bh 2 >> put_ bh components
  put_ bh (Call multi use) = putByte bh 3 >> put_ bh multi >> put_ bh use
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return HeadUse
      1 -> return UnknownUse
      2 -> Product <$> get bh
      _ -> Call <$> get bh <*> get bh

-- | Mostly important for serializing `UsageSig` in interface files.
instance Binary Usage where
  put_ bh Absent = putByte bh 0
  put_ bh (Used multi use) = putByte bh 1 >> put_ bh multi >> put_ bh use
  get  bh = do
    h <- getByte bh
    case h of
      0 -> return Absent
      _ -> Used <$> get bh <*> get bh

-- | Mostly important for serializing `UsageSig` in interface files.
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

-- * Conversion to and from @Demand.hs@

-- | For conveniently working with PrimOps. I've no nerve right now to go through
-- all entries in primops.txt.pp.
usageSigFromStrictSig :: StrictSig -> UsageSig
usageSigFromStrictSig sig
  = foldr consUsageSig tail_sig
  . map (usageFromArgUse . Demand.getUseDmd) 
  $ dmds
  where
    (dmds, _) = splitStrictSig sig
    tail_sig
      | Demand.isBottomingSig sig
      = botUsageSig -- Diverging or throwing: all other args are unused
      | otherwise 
      = topUsageSig 

multiplicityFromCount :: Demand.Count -> Multiplicity
multiplicityFromCount Demand.One = Once
multiplicityFromCount Demand.Many = Many

singleUseFromUseDmd :: Demand.UseDmd -> Use
singleUseFromUseDmd Demand.UHead = botUse
singleUseFromUseDmd (Demand.UCall c u) = mkCallUse (multiplicityFromCount c) (singleUseFromUseDmd u)
singleUseFromUseDmd (Demand.UProd comps) = mkProductUse (map usageFromArgUse comps)
singleUseFromUseDmd Demand.Used = topUse

usageFromArgUse :: Demand.ArgUse -> Usage
usageFromArgUse Demand.Abs = Absent
usageFromArgUse (Demand.Use c u) = Used (multiplicityFromCount c) (singleUseFromUseDmd u)

usageFromDemand :: Demand.Demand -> Usage
usageFromDemand = usageFromArgUse . Demand.getUseDmd

-- | Overwrites the usage component of a `Demand.Demand` with the given `Usage`.
overwriteDemandWithUsage :: Usage -> Demand.Demand -> Demand.Demand
overwriteDemandWithUsage = Demand.setUseDmd . usageToArgUse

usageToArgUse :: Usage -> Demand.ArgUse
usageToArgUse Absent = Demand.Abs
usageToArgUse (Used multi use)
  = Demand.Use (multiplicityToCount multi) (singleUseToUseDmd use)

multiplicityToCount :: Multiplicity -> Demand.Count
multiplicityToCount Once = Demand.One
multiplicityToCount Many = Demand.Many

singleUseToUseDmd :: Use -> Demand.UseDmd
singleUseToUseDmd HeadUse = Demand.UHead
singleUseToUseDmd UnknownUse = Demand.Used
singleUseToUseDmd (Product comps) = Demand.UProd (map usageToArgUse comps)
singleUseToUseDmd (Call multi use)
  = Demand.UCall (multiplicityToCount multi) (singleUseToUseDmd use)

-- | Overwrites the usage component of a `Demand.StrictSig` with the given
-- `UsageSig`.
overwriteStrictSigWithUsageSig :: UsageSig -> StrictSig -> StrictSig
overwriteStrictSigWithUsageSig usage_sig strict_sig = strict_sig'
  where
    strict_sig' = Demand.mkClosedStrictSig (overwrite usage_sig dmds) dmd_result
    (dmds, dmd_result) = Demand.splitStrictSig strict_sig
    overwrite _ [] = []
    overwrite sig (dmd:dmds)
      | (usage, sig') <- unconsUsageSig sig
      = overwriteDemandWithUsage usage dmd : overwrite sig' dmds
