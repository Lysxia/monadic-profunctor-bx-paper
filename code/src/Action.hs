{-

Haskell representation of everything action.
(Section 10)

-}

{-# LANGUAGE MultiParamTypeClasses  #-}

module Action where

-- comonad
import Control.Comonad

-- contravariant
import Data.Functor.Contravariant

-- profunctor
import Data.Profunctor

-- An action is when a type "acts" on another.
-- i.e. when every inhabitant corresponds to an endofunction on the acted upon type.
-- There are two way of acting, that are subtly different: left and right.
-- The difference arises when you perform many actions as this affects the order
-- that the functions are applied.
class Action x y where
  -- Whether the action is left or right depends on where the acting type is
  actL :: (x,y) -> y
  --       ^ left
  actR :: (y,x) -> y
  --         ^ right

  -- These actions can also be presented in curried form.
  -- Here it is clear that the x set is "acting" on y as an endofunction on y is returned
  -- e.g. actLCurried x :: y -> y
  actLCurried :: x -> y -> y
  actLCurried = curry actL
  actRCurried :: y -> x -> y
  actRCurried = curry actR

-- Typically the acting set supports some sort of algebraic structure, which is
-- respected by the endofunction actions
-- In other words, the act functions act as a homomorphism between the given monoid
-- and the monoid of endofunctors
-- Laws:
--   act mempty = id
--   act (m1 `mappend` m2) = act m1 . act m2
class Monoid m => MonoidAction m a where
  monoidActL :: (m,a) -> a
  monoidActR :: (a,m) -> a

-- "monad are monoids in the category of endofunctors"

-- Monads can represent actions on functors, as they are monoids (return, join)
-- in the cat of endofunctors
class (Monad m, Functor f) => MonadAction m f where
  monadActL :: m (f a) -> f a
  monadActR :: f (m a) -> f a

-- -----------------------------------------------------------------------------
-- Time to flip some arrows and head over to the opposite cat

-- Just a monoid, but the arrows are flipped
-- Every type in haskell is trivially a comonoid (https://bartoszmilewski.com/2017/01/02/comonads/)
class Comonoid m where
  destroy :: m -> ()
  split :: m -> (m,m)

class Comonoid m => MonoidCoAction m a where
  coMonoidActL :: a -> (m,a)
  coMonoidActR :: a -> (a,m)

class (Comonad m, Contravariant f) => MonadCoAction m f where
  coMonadActL :: f a -> m (f a)
  coMonadActR :: f a -> f (m a) -- coAct in the paper

-- ProfunctorMonadInternalise is a right monad coaction on the first (contravariant)
-- parameter of a profunctor.