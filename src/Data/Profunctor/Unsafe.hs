{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 708
{-# LANGUAGE Trustworthy #-}
#elif __GLASGOW_HASKELL >= 704
{-# LANGUAGE Unsafe #-}
#endif
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2011-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- For a good explanation of profunctors in Haskell see Dan Piponi's article:
--
-- <http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html>
--
-- This module includes /unsafe/ composition operators that are useful in
-- practice when it comes to generating optimal core in GHC.
--
-- If you import this module you are taking upon yourself the obligation
-- that you will only call the operators with @#@ in their names with functions
-- that are operationally identity such as @newtype@ constructors or the field
-- accessor of a @newtype@.
--
-- If you are ever in doubt, use 'rmap' or 'lmap'.
----------------------------------------------------------------------------
module Data.Profunctor.Unsafe
  (
  -- * Profunctors
    Profunctor(..)
  ) where

import Control.Arrow
import Control.Category
import Control.Comonad (Cokleisli(..))
import Control.Monad (liftM)
import Data.Bifunctor.Biff (Biff(..))
import Data.Bifunctor.Clown (Clown(..))
import Data.Bifunctor.Joker (Joker(..))
import Data.Bifunctor.Product (Product(..))
import Data.Bifunctor.Tannen (Tannen(..))
#if __GLASGOW_HASKELL__ < 710
import Data.Functor
#endif
import Data.Functor.Contravariant (Contravariant(..))
import Data.Tagged
import Prelude hiding (id,(.),sequence)

#if __GLASGOW_HASKELL__ >= 708
import Data.Coerce
import Data.Type.Coercion (Coercion (..))
import qualified Data.Type.Coercion as DTC
#endif

import Unsafe.Coerce

{-# ANN module "Hlint: ignore Redundant lambda" #-}
{-# ANN module "Hlint: ignore Collapse lambdas" #-}

infixr 9 #.
infixl 8 .#

----------------------------------------------------------------------------
-- Profunctors
----------------------------------------------------------------------------

-- | Formally, the class 'Profunctor' represents a profunctor
-- from @Hask@ -> @Hask@.
--
-- Intuitively it is a bifunctor where the first argument is contravariant
-- and the second argument is covariant.
--
-- You can define a 'Profunctor' by either defining 'dimap' or by defining both
-- 'lmap' and 'rmap'.
--
-- If you supply 'dimap', you should ensure that:
--
-- @'dimap' 'id' 'id' ≡ 'id'@
--
-- If you supply 'lmap' and 'rmap', ensure:
--
-- @
-- 'lmap' 'id' ≡ 'id'
-- 'rmap' 'id' ≡ 'id'
-- @
--
-- If you supply both, you should also ensure:
--
-- @'dimap' f g ≡ 'lmap' f '.' 'rmap' g@
--
-- These ensure by parametricity:
--
-- @
-- 'dimap' (f '.' g) (h '.' i) ≡ 'dimap' g h '.' 'dimap' f i
-- 'lmap' (f '.' g) ≡ 'lmap' g '.' 'lmap' f
-- 'rmap' (f '.' g) ≡ 'rmap' f '.' 'rmap' g
-- @
class Profunctor p where
  -- | Map over both arguments at the same time.
  --
  -- @'dimap' f g ≡ 'lmap' f '.' 'rmap' g@
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g
  {-# INLINE dimap #-}

  -- | Map the first argument contravariantly.
  --
  -- @'lmap' f ≡ 'dimap' f 'id'@
  lmap :: (a -> b) -> p b c -> p a c
  lmap f = dimap f id
  {-# INLINE lmap #-}

  -- | Map the second argument covariantly.
  --
  -- @'rmap' ≡ 'dimap' 'id'@
  rmap :: (b -> c) -> p a b -> p a c
  rmap = dimap id
  {-# INLINE rmap #-}

  -- | Strictly map the second argument argument
  -- covariantly with a function that is assumed
  -- operationally to be a cast, such as a newtype
  -- constructor.
  --
  -- /Note:/ This operation is explicitly /unsafe/
  -- since an implementation may choose to use
  -- 'unsafeCoerce' to implement this combinator
  -- and it has no way to validate that your function
  -- meets the requirements.
  --
  -- If you implement this combinator with
  -- 'unsafeCoerce', then you are taking upon yourself
  -- the obligation that you don't use GADT-like
  -- tricks to distinguish values.
  --
  -- If you import "Data.Profunctor.Unsafe" you are
  -- taking upon yourself the obligation that you
  -- will only call this with a first argument that is
  -- operationally identity.
  --
  -- The semantics of this function with respect to bottoms
  -- should match the default definition:
  --
  -- @('Profuctor.Unsafe.#.') ≡ \\f -> \\p -> p \`seq\` 'rmap' f p@
#if __GLASGOW_HASKELL__ >= 708
  ( #. ) :: Coercible c b => (b -> c) -> p a b -> p a c
  ( #. ) = case rliftCoerce of
             Nothing -> \f -> \p -> p `seq` rmap f p
             Just c -> \_ -> DTC.coerceWith (c Coercion)
#else
  ( #. ) :: (b -> c) -> p a b -> p a c
  ( #. ) = \f -> \p -> p `seq` rmap f p
#endif
  {-# INLINE ( #. ) #-}

  -- | Strictly map the first argument argument
  -- contravariantly with a function that is assumed
  -- operationally to be a cast, such as a newtype
  -- constructor.
  --
  -- /Note:/ This operation is explicitly /unsafe/
  -- since an implementation may choose to use
  -- 'unsafeCoerce' to implement this combinator
  -- and it has no way to validate that your function
  -- meets the requirements.
  --
  -- If you implement this combinator with
  -- 'unsafeCoerce', then you are taking upon yourself
  -- the obligation that you don't use GADT-like
  -- tricks to distinguish values.
  --
  -- If you import "Data.Profunctor.Unsafe" you are
  -- taking upon yourself the obligation that you
  -- will only call this with a second argument that is
  -- operationally identity.
  --
  -- @('.#') ≡ \\p -> p \`seq\` \\f -> 'lmap' f p@
#if __GLASGOW_HASKELL__ >= 708
  ( .# ) :: Coercible b a => p b c -> (a -> b) -> p a c
  ( .# ) = case lliftCoerce of
             Nothing -> \p -> p `seq` \f -> lmap f p
             Just c -> \p _ -> DTC.coerceWith (c Coercion) p
#else
  ( .# ) :: p b c -> (a -> b) -> p a c
  ( .# ) = \p -> p `seq` \f -> lmap f p
#endif
  {-# INLINE ( .# ) #-}

#if __GLASGOW_HASKELL__ >= 708
  lliftCoerce :: Maybe (Coercion s a -> Coercion (p a c) (p s c))
  lliftCoerce = (\c l -> c l Coercion) <$> diliftCoerce
  rliftCoerce :: Maybe (Coercion b t -> Coercion (p c b) (p c t))
  rliftCoerce = (\c r -> c Coercion r) <$> diliftCoerce
  diliftCoerce :: Maybe (Coercion s a -> Coercion b t -> Coercion (p a b) (p s t))
  diliftCoerce = Nothing
#endif

#if __GLASGOW_HASKELL__ >= 708
  {-# MINIMAL dimap | (lmap, rmap) #-}
#endif

instance Profunctor (->) where
  dimap ab cd bc = cd . bc . ab
  {-# INLINE dimap #-}
  lmap = flip (.)
  {-# INLINE lmap #-}
  rmap = (.)
  {-# INLINE rmap #-}
#if __GLASGOW_HASKELL__ >= 708
  ( #. ) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  ( .# ) pbc _ = coerce pbc
  diliftCoerce = Just (\Coercion Coercion -> Coercion)
#else
  ( #. ) _ = unsafeCoerce
  ( .# ) pbc _ = unsafeCoerce pbc
#endif
  {-# INLINE ( #. ) #-}
  {-# INLINE ( .# ) #-}

instance Profunctor Tagged where
  dimap _ f (Tagged s) = Tagged (f s)
  {-# INLINE dimap #-}
  lmap _ = retag
  {-# INLINE lmap #-}
  rmap = fmap
  {-# INLINE rmap #-}
#if __GLASGOW_HASKELL__ >= 708
  ( #. ) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  diliftCoerce = Just (\Coercion Coercion -> Coercion)
#else
  ( #. ) _ = unsafeCoerce
#endif
  {-# INLINE ( #. ) #-}
  Tagged s .# _ = Tagged s
  {-# INLINE ( .# ) #-}

instance Monad m => Profunctor (Kleisli m) where
  dimap f g (Kleisli h) = Kleisli (liftM g . h . f)
  {-# INLINE dimap #-}
  lmap k (Kleisli f) = Kleisli (f . k)
  {-# INLINE lmap #-}
  rmap k (Kleisli f) = Kleisli (liftM k . f)
  {-# INLINE rmap #-}
  -- We cannot safely overload (#.) because we didn't provide the 'Monad'.
#if __GLASGOW_HASKELL__ >= 708
  ( .# ) pbc _ = coerce pbc
  lliftCoerce = Just (\Coercion -> Coercion)
#else
  ( .# ) pbc _ = unsafeCoerce pbc
#endif
  {-# INLINE ( .# ) #-}

instance Functor w => Profunctor (Cokleisli w) where
  dimap f g (Cokleisli h) = Cokleisli (g . h . fmap f)
  {-# INLINE dimap #-}
  lmap k (Cokleisli f) = Cokleisli (f . fmap k)
  {-# INLINE lmap #-}
  rmap k (Cokleisli f) = Cokleisli (k . f)
  {-# INLINE rmap #-}
  -- We cannot safely overload (.#) because we didn't provide the 'Functor'.
#if __GLASGOW_HASKELL__ >= 708
  ( #. ) _ = coerce (\x -> x :: b) :: forall a b. Coercible b a => a -> b
  rliftCoerce = Just (\Coercion -> Coercion)
#else
  ( #. ) _ = unsafeCoerce
#endif
  {-# INLINE ( #. ) #-}

instance Contravariant f => Profunctor (Clown f) where
  lmap f (Clown fa) = Clown (contramap f fa)
  {-# INLINE lmap #-}
  rmap _ (Clown fa) = Clown fa
  {-# INLINE rmap #-}
  dimap f _ (Clown fa) = Clown (contramap f fa)
  {-# INLINE dimap #-}
#if __GLASGOW_HASKELL__ >= 708
  rliftCoerce = Just (\Coercion -> Coercion)
#endif

instance Functor f => Profunctor (Joker f) where
  lmap _ (Joker fb) = Joker fb
  {-# INLINE lmap #-}
  rmap g (Joker fb) = Joker (fmap g fb)
  {-# INLINE rmap #-}
  dimap _ g (Joker fb) = Joker (fmap g fb)
  {-# INLINE dimap #-}
#if __GLASGOW_HASKELL__ >= 708
  lliftCoerce = Just (\Coercion -> Coercion)
#endif

instance (Profunctor p, Functor f, Functor g) => Profunctor (Biff p f g) where
  lmap f (Biff p) = Biff (lmap (fmap f) p)
  rmap g (Biff p) = Biff (rmap (fmap g) p)
  dimap f g (Biff p) = Biff (dimap (fmap f) (fmap g) p)

instance (Profunctor p, Profunctor q) => Profunctor (Product p q) where
  lmap  f   (Pair p q) = Pair (lmap f p) (lmap f q)
  {-# INLINE lmap #-}
  rmap    g (Pair p q) = Pair (rmap g p) (rmap g q)
  {-# INLINE rmap #-}
  dimap f g (Pair p q) = Pair (dimap f g p) (dimap f g q)
  {-# INLINE dimap #-}
  ( #. ) f (Pair p q) = Pair (f #. p) (f #. q)
  {-# INLINE ( #. ) #-}
  ( .# ) (Pair p q) f = Pair (p .# f) (q .# f)
  {-# INLINE ( .# ) #-}

  -- This is rather disgusting!
  --
  -- data Product p q a b ~= (p a b, q a b)
  --
  -- so if we can produce a coercion from (p a b) to (p s t)
  -- and one from (q a b) to (q s t), we should surely be able
  -- to produce one from (Product p q a b) to (Product p q s t).
  -- Unfortunately, GHC isn't smart enough for that, so we have to
  -- cheat our way into a perfecty legitimate coercion using
  -- unsafeCoerce.
  diliftCoerce :: forall s t a b. Maybe
                  (Coercion s a -> Coercion b t
                     -> Coercion (Product p q a b) (Product p q s t))
  diliftCoerce = (\p q c1 c2 ->
       case p c1 c2 of { Coercion ->
       case q c1 c2 of { Coercion ->
          unsafeCoerce (Coercion :: Coercion (p a b, q a b) (p s t, q s t)) }})
       <$> (diliftCoerce :: Maybe (Coercion s a -> Coercion b t
                                   -> Coercion (p a b) (p s t)))
       <*> (diliftCoerce :: Maybe (Coercion s a -> Coercion b t
                                   -> Coercion (q a b) (q s t)))
  lliftCoerce :: forall s a c.
                 Maybe (Coercion s a -> Coercion (Product p q a c) (Product p q s c))
  lliftCoerce = (\p q c ->
     case p c of { Coercion ->
     case q c of { Coercion ->
       unsafeCoerce $ (Coercion :: Coercion (p a c, q a c) (p s c, q s c)) }})
                 <$> (lliftCoerce :: Maybe (Coercion s a -> Coercion (p a c) (p s c)))
                 <*> (lliftCoerce :: Maybe (Coercion s a -> Coercion (q a c) (q s c)))

instance (Functor f, Profunctor p) => Profunctor (Tannen f p) where
  lmap f (Tannen h) = Tannen (lmap f <$> h)
  {-# INLINE lmap #-}
  rmap g (Tannen h) = Tannen (rmap g <$> h)
  {-# INLINE rmap #-}
  dimap f g (Tannen h) = Tannen (dimap f g <$> h)
  {-# INLINE dimap #-}
  ( #. ) f (Tannen h) = Tannen ((f #.) <$> h)
  {-# INLINE ( #. ) #-}
  ( .# ) (Tannen h) f = Tannen ((.# f) <$> h)
  {-# INLINE ( .# ) #-}
