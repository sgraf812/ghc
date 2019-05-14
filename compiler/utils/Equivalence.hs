-- | A simple union-find data structure with sub-optimal performance.
-- Interface inspired by the equivalence-persistent package.
module Equivalence (
        Equivalence, Rep, empty, newClass, equate, domain, equiv, lookup, modify
    ) where

import GhcPrelude hiding (lookup)

import Control.Arrow (first)
import Control.Monad (when)
import Control.Monad.Trans.State.Strict hiding (modify)
import Data.Coerce
import Maybes
import Unique
import UniqSupply
import UniqFM
import Outputable hiding (empty)

type RelEnv a = UniqFM (Either Unique a)

data Equivalence a = Equivalence
  { eq_us  :: !UniqSupply
  , eq_rel :: !(RelEnv a)
  }

-- Ideally we'd have a dependent phantom type on the 'Equivalence' this thing
-- belongs to...
newtype Rep = Rep { unRep :: Unique }
  deriving Eq

compressPaths :: (Unique -> Maybe a -> RelEnv a -> (b, RelEnv a)) -> RelEnv a -> Unique -> (b, RelEnv a)
compressPaths f rel u = snd $ go u
  where
    go u = case lookupUFM rel u of
      Nothing -> (,) u $ f u Nothing rel
      Just (Right a) -> (,) u $ f u (Just a) rel
      Just (Left u') ->
        let g (u'', (ret, rel')) = (u'', (ret, addToUFM rel' u' (Left u'')))
        in g $ go u'

adjustDeep :: (a -> a) -> RelEnv a -> Unique -> RelEnv a
adjustDeep f rel u = snd $ compressPaths g rel u
  where
    g _ Nothing  rel = ((), rel)
    g u (Just a) rel = ((), addToUFM rel u (Right (f a)))

empty :: UniqSupply -> Equivalence a
empty us = Equivalence us emptyUFM

newClass :: a -> Equivalence a -> (Rep, Equivalence a)
newClass a eq = (Rep u, eq { eq_us = us', eq_rel = rel' })
  where
    (u, us') = takeUniqFromSupply (eq_us eq)
    rel'     = addToUFM (eq_rel eq) u (Right a)

domain :: Equivalence a -> [Rep]
domain eq = coerce (nonDetKeysUFM (eq_rel eq))
    -- It's OK to use nonDetKeysUFM here, because Rep has no Ord instance

reprAndValue :: Rep -> Equivalence a -> ((Rep, a), Equivalence a)
reprAndValue (Rep u) eq = ((Rep u', a), eq { eq_rel = rel' })
  where
    ((u', ma), rel') = compressPaths f (eq_rel eq) u
    f u' ma rel = ((u', ma), rel)
    a = expectJust "Equivalence.equate: Dangling equivalence class" ma

repr :: Rep -> Equivalence a -> (Rep, Equivalence a)
repr r eq = first fst (reprAndValue r eq)

lookup :: Rep -> Equivalence a -> (a, Equivalence a)
lookup r eq = first snd (reprAndValue r eq)

equiv :: Rep -> Rep -> Equivalence a -> (Bool, Equivalence a)
equiv a b eq = flip runState eq $
  (==) <$> state (repr a) <*> state (repr b)

modify :: (a -> a) -> Rep -> Equivalence a -> Equivalence a
modify f (Rep u) eq = eq { eq_rel = adjustDeep f (eq_rel eq) u }

equate :: (a -> a -> a) -> Rep -> Rep -> Equivalence a -> Equivalence a
equate f r1 r2 eq = flip execState eq $ do
  (r1', a1) <- state (reprAndValue r1)
  (r2', a2) <- state (reprAndValue r2)
  when (r1' /= r2') $ do
    eq <- get
    let rel1 = addToUFM (eq_rel eq) (unRep r1') (Right (f a1 a2))
    let rel2 = addToUFM rel1 (unRep r2') (Left (unRep r1'))
    put (eq { eq_rel = rel2 })