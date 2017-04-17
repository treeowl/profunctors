{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

#if __GLASGOW_HASKELL__ >= 704 && __GLASGOW_HASKELL__ < 708
{-# LANGUAGE Trustworthy #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2014-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types
--
----------------------------------------------------------------------------
module Data.Profunctor.Strong
  (
  -- * Strength
    Strong(..)
  , uncurry'
  , Tambara(..)
  , tambara, untambara
  , Pastro(..)
  , pastro, unpastro
  -- * Costrength
  , Costrong(..)
  , Cotambara(..)
  , cotambara, uncotambara
  , Copastro(..)
  ) where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Monad (liftM)
import Control.Monad.Fix
import Data.Bifunctor.Clown (Clown(..))
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Tannen (Tannen(..))
import Data.Functor.Contravariant (Contravariant(..))
import Data.Functor.Identity (Identity (..))
import Data.Monoid hiding (Product)
import Data.Profunctor.Adjunction
import Data.Profunctor.Monad
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Tagged
import Data.Tuple
import Data.Coerce
import Prelude hiding (id,(.))

------------------------------------------------------------------------------
-- Strong
------------------------------------------------------------------------------

-- | Generalizing 'Star' of a strong 'Functor'
--
-- /Note:/ Every 'Functor' in Haskell is strong with respect to @(,)@.
--
-- This describes profunctor strength with respect to the product structure
-- of Hask.
--
-- <http://www-kb.is.s.u-tokyo.ac.jp/~asada/papers/arrStrMnd.pdf>
--
class Profunctor p => Strong p where
  -- | Laws:
  --
  -- @
  -- 'first'' ≡ 'dimap' 'swap' 'swap' '.' 'second''
  -- 'lmap' 'fst' ≡ 'rmap' 'fst' '.' 'first''
  -- 'lmap' ('second' f) '.' 'first'' ≡ 'rmap' ('second' f) '.' 'first'
  -- 'first'' '.' 'first'' ≡ 'dimap' assoc unassoc '.' 'first'' where
  --   assoc ((a,b),c) = (a,(b,c))
  --   unassoc (a,(b,c)) = ((a,b),c)
  -- @
  first' :: p a b  -> p (a, c) (b, c)
  first' = dimap swap swap . second'

  -- | Laws:
  --
  -- @
  -- 'second'' ≡ 'dimap' 'swap' 'swap' '.' 'first''
  -- 'lmap' 'snd' ≡ 'rmap' 'snd' '.' 'second''
  -- 'lmap' ('first' f) '.' 'second'' ≡ 'rmap' ('first' f) '.' 'second''
  -- 'second'' '.' 'second'' ≡ 'dimap' unassoc assoc '.' 'second'' where
  --   assoc ((a,b),c) = (a,(b,c))
  --   unassoc (a,(b,c)) = ((a,b),c)
  -- @
  second' :: p a b -> p (c, a) (c, b)
  second' = dimap swap swap . first'

  -- | A custom definition of 'lensical' will often be more efficient than
  -- the default.
  lensical :: Functor f => (s -> a) -> (s -> b -> t) -> p a (f b) -> p s (f t)
  lensical getter setter = dimap (setter &&& getter) (uncurry fmap) . second'

  -- | A custom definition of 'prolensical' will sometimes be more efficient
  -- than the default.
  prolensical :: (s -> a) -> (s -> b -> t) -> p a b -> p s t
  prolensical getter setter = dimap (setter &&& getter) (uncurry ($)) . second'

#if __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL first' | second' #-}
#endif

-- | A suitable definition of 'dimap' for an instance defining 'lensical'
dimapLensically :: Strong p => (a' -> a) -> (b -> b') -> p a b -> p a' b'
dimapLensically f g = (runIdentity #.)
                      . lensical f (const g)
                      . (Identity #.)

-- | A suitable definition of 'dimap' for an instance defining 'prolensical'
dimapProlensically :: Strong p => (a' -> a) -> (b -> b') -> p a b -> p a' b'
dimapProlensically f g = prolensical f (const g)

-- | A suitable definition of 'first'' for an instance defining 'lensical'
firstLensically :: Strong p => p a b -> p (a, c) (b, c)
firstLensically = (runIdentity #.)
                  . lensical fst (\(_, c) b -> (b, c))
                  . (Identity #.)

-- | A suitable definition of 'first'' for an instance defining 'prolensical'
firstProlensically :: Strong p => p a b -> p (a, c) (b, c)
firstProlensically = prolensical fst (\(_, c) b -> (b, c))

-- | A suitable definition of 'second'' for an instance defining 'lensical'
secondLensically :: Strong p => p a b -> p (c, a) (c, b)
secondLensically = (runIdentity #.)
                  . lensical snd (\(c, _) b -> (c, b))
                  . (Identity #.)

-- | A suitable definition of 'second'' for an instance defining 'prolensical'
secondProlensically :: Strong p => p a b -> p (c, a) (c, b)
secondProlensically = prolensical snd (\(c, _) b -> (c, b))

-- | A suitable definition of 'lensical' for an instance defining
-- 'prolensical'
lensicalProlensically ::
     (Strong p, Functor f)
  => (s -> a) -> (s -> b -> t) -> p a (f b) -> p s (f t)
lensicalProlensically getter setter = prolensical getter (fmap . setter)

-- | A suitable definition of 'prolensical' for an instance defining
-- 'lensical'.
prolensicalLensically :: Strong p =>
  (s -> a) -> (s -> b -> t) -> p a b -> p s t
prolensicalLensically getter setter =
    (runIdentity #.) . lensical getter setter . (Identity #.)
-- This is efficient given good definitions of 'lensical',
-- '#.', and '.#'.


uncurry' :: Strong p => p a (b -> c) -> p (a, b) c
uncurry' = rmap (\(f,x) -> f x) . first'
{-# INLINE uncurry' #-}

instance Strong (->) where
  first' ab ~(a, c) = (ab a, c)
  {-# INLINE first' #-}
  second' ab ~(c, a) = (c, ab a)
  {-# INLINE second' #-}
  lensical getter setter afb s = setter s <$> afb (getter s)
  {-# INLINE lensical #-}

instance Monad m => Strong (Kleisli m) where
  first' (Kleisli f) = Kleisli $ \ ~(a, c) -> do
     b <- f a
     return (b, c)
  {-# INLINE first' #-}
  second' (Kleisli f) = Kleisli $ \ ~(c, a) -> do
     b <- f a
     return (c, b)
  {-# INLINE second' #-}
  lensical getter setter (Kleisli mafb) =
    Kleisli $ \s -> liftM (fmap (setter s)) (mafb (getter s))
  {-# INLINE lensical #-}
  prolensical getter setter (Kleisli mafb) =
    Kleisli $ \s -> liftM (setter s) $ mafb (getter s)
  {-# INLINE prolensical #-}

instance Functor m => Strong (Star m) where
  first' (Star f) = Star $ \ ~(a, c) -> (\b' -> (b', c)) <$> f a
  {-# INLINE first' #-}
  second' (Star f) = Star $ \ ~(c, a) -> (,) c <$> f a
  {-# INLINE second' #-}
  lensical getter setter (Star f) = Star $ \s ->
    fmap (fmap (setter s)) $ f (getter s)
  {-# INLINE lensical #-}
  prolensical getter setter (Star f) = Star $ \s ->
    fmap (setter s) $ f (getter s)
  {-# INLINE prolensical #-}

-- | 'Arrow' is 'Strong' 'Category'
instance Arrow p => Strong (WrappedArrow p) where
  first' (WrapArrow k) = WrapArrow (first k)
  {-# INLINE first' #-}
  second' (WrapArrow k) = WrapArrow (second k)
  {-# INLINE second' #-}

instance Strong (Forget r) where
  first' (Forget k) = Forget (k . fst)
  {-# INLINE first' #-}
  second' (Forget k) = Forget (k . snd)
  {-# INLINE second' #-}
  lensical getter _setter (Forget k) = Forget $ k . getter
  {-# INLINE lensical #-}

instance Contravariant f => Strong (Clown f) where
  first' (Clown fa) = Clown (contramap fst fa)
  {-# INLINE first' #-}
  second' (Clown fa) = Clown (contramap snd fa)
  {-# INLINE second' #-}
  lensical getter _setter (Clown fa) = Clown $
    contramap getter fa
  prolensical getter _setter (Clown fa) = Clown $
    contramap getter fa

instance (Strong p, Strong q) => Strong (Product p q) where
  first' (Pair p q) = Pair (first' p) (first' q)
  {-# INLINE first' #-}
  second' (Pair p q) = Pair (second' p) (second' q)
  {-# INLINE second' #-}
  lensical getter setter (Pair p q) =
    Pair (lensical getter setter p) (lensical getter setter q)
  {-# INLINE lensical #-}
  prolensical getter setter (Pair p q) =
    Pair (prolensical getter setter p) (prolensical getter setter q)
  {-# INLINE prolensical #-}

instance (Functor f, Strong p) => Strong (Tannen f p) where
  first' (Tannen fp) = Tannen (fmap first' fp)
  {-# INLINE first' #-}
  second' (Tannen fp) = Tannen (fmap second' fp)
  {-# INLINE second' #-}
  lensical getter setter (Tannen p) =
    Tannen $ fmap (lensical getter setter) p
  {-# INLINE lensical #-}
  prolensical getter setter (Tannen p) =
    Tannen $ fmap (prolensical getter setter) p
  {-# INLINE prolensical #-}


----------------------------------------------------------------------------
-- * Tambara
----------------------------------------------------------------------------

-- | 'Tambara' cofreely makes any 'Profunctor' 'Strong'.
newtype Tambara p a b = Tambara { runTambara :: forall c. p (a, c) (b, c) }

instance Profunctor p => Profunctor (Tambara p) where
  dimap f g (Tambara p) = Tambara $ dimap (first f) (first g) p
  {-# INLINE dimap #-}
  lmap f (Tambara p) = Tambara $ lmap (first f) p
  {-# INLINE lmap #-}
  rmap f (Tambara p) = Tambara $ rmap (first f) p
  {-# INLINE rmap #-}
  f #. Tambara g = Tambara (first f #. g)
  {-# INLINE (#.) #-}
  Tambara f .# g = Tambara (f .# first g)
  {-# INLINE (.#) #-}

instance ProfunctorFunctor Tambara where
  promap f (Tambara p) = Tambara (f p)

instance ProfunctorComonad Tambara where
  proextract (Tambara p) = dimap (\a -> (a,())) fst p
  produplicate (Tambara p) = Tambara (Tambara $ dimap hither yon p) where
    hither :: ((a, b), c) -> (a, (b, c))
    hither ~(~(x,y),z) = (x,(y,z))

    yon    :: (a, (b, c)) -> ((a, b), c)
    yon    ~(x,~(y,z)) = ((x,y),z)

instance Profunctor p => Strong (Tambara p) where
  first' = runTambara . produplicate
  {-# INLINE first' #-}
  prolensical getter setter (Tambara p) =
    Tambara $ dimap (\ ~(s,c) -> (getter s,(s, c)))
                    (\ ~(b,~(s,c)) -> (setter s b, c)) p
  lensical getter setter (Tambara p) =
    Tambara $ dimap (\ ~(s,c) -> (getter s, (s, c)))
                    (\ ~(fb,~(s,c)) -> (setter s <$> fb, c)) p

instance Category p => Category (Tambara p) where
  id = Tambara id
  Tambara p . Tambara q = Tambara (p . q)

instance Arrow p => Arrow (Tambara p) where
  arr f = Tambara $ arr $ first f
  first (Tambara f) = Tambara (arr go . first f . arr go) where
    go :: ((a, b), c) -> ((a, c), b)
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowChoice p => ArrowChoice (Tambara p) where
  left (Tambara f) = Tambara (arr yon . left f . arr hither) where
    hither :: (Either a b, c) -> Either (a, c) (b, c)
    hither (Left y, s) = Left (y, s)
    hither (Right z, s) = Right (z, s)

    yon :: Either (a, c) (b, c) -> (Either a b, c)
    yon (Left (y, s)) = (Left y, s)
    yon (Right (z, s)) = (Right z, s)

instance ArrowApply p => ArrowApply (Tambara p) where
  app = Tambara $ app . arr (\((Tambara f, x), s) -> (f, (x, s)))

instance ArrowLoop p => ArrowLoop (Tambara p) where
  loop (Tambara f) = Tambara (loop (arr go . f . arr go)) where
    go :: ((a, b), c) -> ((a, c), b)
    go ~(~(x,y),z) = ((x,z),y)

instance ArrowZero p => ArrowZero (Tambara p) where
  zeroArrow = Tambara zeroArrow

instance ArrowPlus p => ArrowPlus (Tambara p) where
  Tambara f <+> Tambara g = Tambara (f <+> g)

instance Profunctor p => Functor (Tambara p a) where
  fmap = rmap

instance (Profunctor p, Arrow p) => Applicative (Tambara p a) where
  pure x = arr (const x)
  f <*> g = arr (uncurry id) . (f &&& g)

instance (Profunctor p, ArrowPlus p) => Alternative (Tambara p a) where
  empty = zeroArrow
  f <|> g = f <+> g

instance ArrowPlus p => Monoid (Tambara p a b) where
  mempty = zeroArrow
  mappend f g = f <+> g

-- |
-- @
-- 'tambara' ('untambara' f) ≡ f
-- 'untambara' ('tambara' f) ≡ f
-- @
tambara :: Strong p => (p :-> q) -> p :-> Tambara q
tambara f p = Tambara $ f $ first' p

-- |
-- @
-- 'tambara' ('untambara' f) ≡ f
-- 'untambara' ('tambara' f) ≡ f
-- @
untambara :: Profunctor q => (p :-> Tambara q) -> p :-> q
untambara f p = dimap (\a -> (a,())) fst $ runTambara $ f p


-- Some sort of (co?)freeish strong profunctor.
newtype Tambourine p a b =
  Tambourine { runTambourine :: forall s t. (s -> a) -> (s -> b -> t) -> p s t }
instance Profunctor (Tambourine p) where
  dimap = dimapProlensically
  (#.) _ = coerce
  p .# _ = coerce p

instance Strong (Tambourine p) where
  first' = firstLensically
  second' = secondProlensically
  lensical getter setter (Tambourine p) = Tambourine $
    \sa sbt -> p (getter . sa) (\s1 fb -> sbt s1 ((setter (sa s1)) <$> fb))
  prolensical getter setter (Tambourine p) = Tambourine $
    \sa sbt -> p (getter . sa) (\s1 b -> sbt s1 $ setter (sa s1) b)

instance ProfunctorFunctor Tambourine where
  promap f (Tambourine p) = Tambourine $ \getter setter -> f (p getter setter)

instance ProfunctorComonad Tambourine where
  proextract (Tambourine p) = p id (flip const)
  produplicate (Tambourine p) = Tambourine $
    \getter setter -> Tambourine $ \getter' setter' ->
       p (getter . getter') (\s1 b -> setter' s1 (setter (getter' s1) b))

tambourineToTambara :: Tambourine p a b -> Tambara p a b
tambourineToTambara (Tambourine q) =
  Tambara $ q fst (\(_,c) b -> (b,c))

tambaraToTambourine :: Profunctor p => Tambara p a b -> Tambourine p a b
tambaraToTambourine (Tambara q) =
  Tambourine $ \sa sbt -> dimap (\s -> (sa s, s)) (uncurry (flip sbt)) q

instance (Profunctor p, Category p) => Category (Tambourine p) where
  -- id could also be defined
  -- id = Tambourine $ \sa sbt -> lmap (\s -> sbt s (sa s)) id
  id = Tambourine $ \sa sbt -> rmap (\s -> sbt s (sa s)) id
  Tambourine p . Tambourine q = Tambourine $
    \sa sbt -> p snd (sbt . fst) . q sa (,)

instance (Profunctor p, Arrow p) => Arrow (Tambourine p) where
  first = first'
  arr f = Tambourine $ \sa sbt -> arr $ \s -> sbt s (f (sa s))

instance (Profunctor p, ArrowApply p) => ArrowApply (Tambourine p) where
  app = Tambourine $ \sa sbt -> flip lmap app $
    \s -> case sa s of
            (Tambourine t, b) -> (t (const b) sbt, s)

instance (Profunctor p, ArrowLoop p) => ArrowLoop (Tambourine p) where
  loop = tambaraToTambourine . loop . tambourineToTambara
{-
  -- TODO Check if this uses the right d, and if it otherwise
  -- makes sense.
  loop (Tambourine p) = Tambourine $ \sa sbt ->
    loop $ p (first sa) (\ ~(s,_d) ~(c,d) -> (sbt s c, d))
-}


instance (Profunctor p, ArrowZero p) => ArrowZero (Tambourine p) where
  zeroArrow = Tambourine $ \_ sbt -> rmap (uncurry sbt) zeroArrow

instance (Profunctor p, ArrowPlus p) => ArrowPlus (Tambourine p) where
  Tambourine f <+> Tambourine g = Tambourine $ \sa sbt -> f sa sbt <+> g sa sbt

instance Functor (Tambourine p a) where
  fmap = rmap

instance (Profunctor p, Arrow p) => Applicative (Tambourine p a) where
  pure x = Tambourine $ \_ sbt -> arr (\s -> sbt s x)
  -- TODO See if this is worth implementing directly.
  f <*> g = tambaraToTambourine (tambourineToTambara f <*> tambourineToTambara g)

instance (Profunctor p, ArrowPlus p) => Alternative (Tambourine p a) where
  empty = zeroArrow
  f <|> g = f <+> g

instance (Profunctor p, ArrowPlus p) => Monoid (Tambourine p a b) where
  mempty = zeroArrow
  mappend f g = f <+> g

liftTambourine :: Strong p => p :-> Tambourine p
liftTambourine p = Tambourine $ \sa sbt -> prolensical sa sbt p

lowerTambourine :: Tambourine p :-> p
lowerTambourine (Tambourine p) = p id (flip const)

tambourine :: (p :-> q) -> Tambourine p :-> q
tambourine f = f . lowerTambourine

untambourine :: Strong p => (Tambourine p :-> q) -> p :-> q
untambourine f = f . liftTambourine

----------------------------------------------------------------------------
-- * Pastro
----------------------------------------------------------------------------

-- | Pastro -| Tambara
--
-- @
-- Pastro p ~ exists z. Costar ((,)z) `Procompose` p `Procompose` Star ((,)z)
-- @
--
-- 'Pastro' freely makes any 'Profunctor' 'Strong'.
data Pastro p a b where
  Pastro :: ((y, z) -> b) -> p x y -> (a -> (x, z)) -> Pastro p a b

instance Profunctor (Pastro p) where
  dimap f g (Pastro l m r) = Pastro (g . l) m (r . f)
  lmap f (Pastro l m r) = Pastro l m (r . f)
  rmap g (Pastro l m r) = Pastro (g . l) m r
  w #. Pastro l m r = Pastro (w #. l) m r
  Pastro l m r .# w = Pastro l m (r .# w)

instance ProfunctorFunctor Pastro where
  promap f (Pastro l m r) = Pastro l (f m) r

instance ProfunctorMonad Pastro where
  proreturn p = Pastro fst p $ \a -> (a,())
  projoin (Pastro l (Pastro m n o) p) = Pastro lm n op where
    op a = case p a of
      (b, f) -> case o b of
         (c, g) -> (c, (f, g))
    lm (d, (f, g)) = l (m (d, g), f)

instance ProfunctorAdjunction Pastro Tambara where
  counit (Pastro g (Tambara p) f) = dimap f g p
  unit p = Tambara (Pastro id p id)

instance Strong (Pastro p) where
  first' (Pastro l m r) = Pastro l' m r' where
    r' (a,c) = case r a of
      (x,z) -> (x,(z,c))
    l' (y,(z,c)) = (l (y,z), c)
  second' (Pastro l m r) = Pastro l' m r' where
    r' (c,a) = case r a of
      (x,z) -> (x,(c,z))
    l' (y,(c,z)) = (c,l (y,z))

-- |
-- @
-- 'pastro' ('unpastro' f) ≡ f
-- 'unpastro' ('pastro' f) ≡ f
-- @
pastro :: Strong q => (p :-> q) -> Pastro p :-> q
pastro f (Pastro r g l) = dimap l r (first' (f g))

-- |
-- @
-- 'pastro' ('unpastro' f) ≡ f
-- 'unpastro' ('pastro' f) ≡ f
-- @
unpastro :: (Pastro p :-> q) -> p :-> q
unpastro f p = f (Pastro fst p (\a -> (a, ())))

-- Some other (co?)freeish strong profunctor.
data Pasta p s t where
  Pasta :: (s -> a) -> (s -> b -> t) -> p a b -> Pasta p s t

instance Profunctor (Pasta p) where
  dimap = dimapProlensically

instance Strong (Pasta p) where
  first' = firstLensically
  second' = secondProlensically
  prolensical getter setter (Pasta sa sbt p) =
    Pasta (sa . getter) (\s b1 -> setter s (sbt (getter s) b1)) p

instance ProfunctorFunctor Pasta where
  promap f (Pasta sa sbt p) = Pasta sa sbt (f p)

instance ProfunctorMonad Pasta where
  proreturn p = Pasta id (flip const) p
  projoin (Pasta sa sbt (Pasta sa' sbt' p)) =
    Pasta (sa' . sa) (\a -> sbt a . sbt' (sa a)) p

instance ProfunctorAdjunction Pasta Tambourine where
  counit (Pasta sa sbt (Tambourine p)) = p sa sbt
  unit p = Tambourine $ \sa sbt -> Pasta sa sbt p

liftPasta :: p :-> Pasta p
liftPasta = Pasta id (flip const)

lowerPasta :: Strong p => Pasta p :-> p
lowerPasta (Pasta getter setter p) = prolensical getter setter p

pasta :: Strong p => (p :-> q) -> Pasta p :-> q
pasta f = f . lowerPasta

unpasta :: (Pasta p :-> q) -> p :-> q
unpasta f = f . liftPasta



--------------------------------------------------------------------------------
-- * Costrength for (,)
--------------------------------------------------------------------------------

-- | Analogous to 'ArrowLoop', 'loop' = 'unfirst'
class Profunctor p => Costrong p where
  -- | Laws:
  --
  -- @
  -- 'unfirst' ≡ 'unsecond' '.' 'dimap' 'swap' 'swap'
  -- 'lmap' (,()) ≡ 'unfirst' '.' 'rmap' (,())
  -- 'unfirst' '.' 'lmap' ('second' f) ≡ 'unfirst' '.' 'rmap' ('second' f)
  -- 'unfirst' '.' 'unfirst' = 'unfirst' '.' 'dimap' assoc unassoc where
  --   assoc ((a,b),c) = (a,(b,c))
  --   unassoc (a,(b,c)) = ((a,b),c)
  -- @
  unfirst  :: p (a, d) (b, d) -> p a b
  unfirst = unsecond . dimap swap swap

  -- | Laws:
  --
  -- @
  -- 'unsecond' ≡ 'unfirst' '.' 'dimap' 'swap' 'swap'
  -- 'lmap' ((),) ≡ 'unsecond' '.' 'rmap' ((),)
  -- 'unsecond' '.' 'lmap' ('first' f) ≡ 'unsecond' '.' 'rmap' ('first' f)
  -- 'unsecond' '.' 'unsecond' = 'unsecond' '.' 'dimap' unassoc assoc where
  --   assoc ((a,b),c) = (a,(b,c))
  --   unassoc (a,(b,c)) = ((a,b),c)
  -- @
  unsecond :: p (d, a) (d, b) -> p a b
  unsecond = unfirst . dimap swap swap

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL unfirst | unsecond #-}
#endif

instance Costrong (->) where
  unfirst f a = b where (b, d) = f (a, d)
  unsecond f a = b where (d, b) = f (d, a)

instance Functor f => Costrong (Costar f) where
  unfirst (Costar f) = Costar f'
    where f' fa = b where (b, d) = f ((\a -> (a, d)) <$> fa)
  unsecond (Costar f) = Costar f'
    where f' fa = b where (d, b) = f ((,) d <$> fa)

instance Costrong Tagged where
  unfirst (Tagged bd) = Tagged (fst bd)
  unsecond (Tagged db) = Tagged (snd db)

instance ArrowLoop p => Costrong (WrappedArrow p) where
  unfirst (WrapArrow k) = WrapArrow (loop k)

instance MonadFix m => Costrong (Kleisli m) where
  unfirst (Kleisli f) = Kleisli (liftM fst . mfix . f')
    where f' x y = f (x, snd y)

instance Functor f => Costrong (Cokleisli f) where
  unfirst (Cokleisli f) = Cokleisli f'
    where f' fa = b where (b, d) = f ((\a -> (a, d)) <$> fa)

instance (Functor f, Costrong p) => Costrong (Tannen f p) where
  unfirst (Tannen fp) = Tannen (fmap unfirst fp)
  unsecond (Tannen fp) = Tannen (fmap unsecond fp)

instance (Costrong p, Costrong q) => Costrong (Product p q) where
  unfirst (Pair p q) = Pair (unfirst p) (unfirst q)
  unsecond (Pair p q) = Pair (unsecond p) (unsecond q)

----------------------------------------------------------------------------
-- * Cotambara
----------------------------------------------------------------------------

-- | Cotambara cofreely constructs costrength
data Cotambara q a b where
    Cotambara :: Costrong r => (r :-> q) -> r a b -> Cotambara q a b

instance Profunctor (Cotambara p) where
  lmap f (Cotambara n p) = Cotambara n (lmap f p)
  rmap g (Cotambara n p) = Cotambara n (rmap g p)
  dimap f g (Cotambara n p) = Cotambara n (dimap f g p)

instance ProfunctorFunctor Cotambara where
  promap f (Cotambara n p) = Cotambara (f . n) p

instance ProfunctorComonad Cotambara where
  proextract (Cotambara n p)  = n p
  produplicate (Cotambara n p) = Cotambara id (Cotambara n p)

instance Costrong (Cotambara p) where
  unfirst (Cotambara n p) = Cotambara n (unfirst p)

instance Functor (Cotambara p a) where
  fmap = rmap

-- |
-- @
-- 'cotambara' '.' 'uncotambara' ≡ 'id'
-- 'uncotambara' '.' 'cotambara' ≡ 'id'
-- @
cotambara :: Costrong p => (p :-> q) -> p :-> Cotambara q
cotambara = Cotambara

-- |
-- @
-- 'cotambara' '.' 'uncotambara' ≡ 'id'
-- 'uncotambara' '.' 'cotambara' ≡ 'id'
-- @
uncotambara :: Profunctor q => (p :-> Cotambara q) -> p :-> q
uncotambara f p = proextract (f p)

----------------------------------------------------------------------------
-- * Copastro
----------------------------------------------------------------------------

-- | Copastro -| Cotambara
--
-- Copastro freely constructs costrength
newtype Copastro p a b = Copastro { runCopastro :: forall r. Costrong r => (forall x y. p x y -> r x y) -> r a b }

instance Profunctor (Copastro p) where
  dimap f g (Copastro h) = Copastro $ \ n -> dimap f g (h n)
  lmap f (Copastro h) = Copastro $ \ n -> lmap f (h n)
  rmap g (Copastro h) = Copastro $ \ n -> rmap g (h n)

instance ProfunctorAdjunction Copastro Cotambara where
 unit p = Cotambara id (proreturn p)
 counit (Copastro h) = proextract (h id)

instance ProfunctorFunctor Copastro where
  promap f (Copastro h) = Copastro $ \n -> h (n . f)

instance ProfunctorMonad Copastro where
  proreturn p = Copastro $ \n -> n p
  projoin p = Copastro $ \c -> runCopastro p (\x -> runCopastro x c)

instance Costrong (Copastro p) where
  unfirst (Copastro p) = Copastro $ \n -> unfirst (p n)
  unsecond (Copastro p) = Copastro $ \n -> unsecond (p n)
