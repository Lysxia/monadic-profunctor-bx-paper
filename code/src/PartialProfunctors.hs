{-

This module contains the 'PartialProfunctor' type class, which adds partiality
to the 'Profunctor' type class using a 'Maybe'.

This has applications in representing Bidirectional Transformations as in Haskell
as it allows for failure.

-}

{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PartialProfunctors where

-- base
import           Data.Functor.Contravariant
import           Control.Monad

-- comonad
import Control.Comonad

-- profunctors
import           Data.Profunctor

class Profunctor p => PartialProfunctor p where
  internaliseMaybe :: p u v -> p (Maybe u) v

  comap :: (u -> Maybe u') -> p u' v -> p u v
  comap f = dimap'' f id

-- contrast with the following in our original paper
--
-- class MonadPartial m where
--   toFailure :: Maybe a -> m a

-- data Fwd m u v = Fwd { unFwd :: m v }      -- ignore contrv. parameter
-- data Bwd m u v = Bwd { unBwd :: u -> m v } -- maps from contrv. parameter

-- Recovering what we have in the original paper
dimap'' :: (PartialProfunctor p, Profunctor p) => (u -> Maybe u') -> (v -> v') -> p u' v -> p u v'
dimap'' f g = dimap' f g . internaliseMaybe
  where
    dimap' :: Profunctor p => (u -> Maybe u') -> (v -> v') -> p (Maybe u') v -> p u v'
    dimap' = dimap

-- Alias in the paper
upon :: (PartialProfunctor p, Profunctor p) =>  p u' v -> (u -> Maybe u') -> p u v
upon = flip comap

-- Note: this is like a natural transformation for a bifunctor P : C^op x C -> Set
--   internaliseMaybe :: P -> P . (Maybe x Id)

-- Perhaps this should satisfy something that looks a lot like monad algebra properties
-- Let a = internaliseMaybe and M = Maybe then
-- I think we should require

--                      a
--        P     ------------------> P . (M x Id)
--
--        |                           |
--      a |                           | P mu id
--        |                           |
--        v                           v

--    P . (M x Id)   ---------->   P . (M . M x Id)
--                      a M

--                 a
--        P -------------> P . (M x Id)
--        \                |
--         \               |  P eta id
--          \              |
--           \             v
--            -----------> P

-- The following is just to verify that these properties are well typed
algebra :: ()
algebra = ()
  where
    unit :: (Profunctor p, PartialProfunctor p) => [p u v -> p u v]
    unit = [dimap return id . internaliseMaybe, id]

    assoc :: (Profunctor p, PartialProfunctor p) => [p u v -> p (Maybe (Maybe u)) v]
    assoc = [dimap join id . internaliseMaybe, internaliseMaybe . internaliseMaybe]

    join :: Maybe (Maybe a) -> Maybe a
    join = flip (>>=) id

class (Monad m, Contravariant f) => MonadCoAction m f where
  coAct :: f u -> f (m u)

laws :: ()
laws = ()
  where
    unial :: forall m f a . (MonadCoAction m f) => [f a -> f a]
    unial = [id, contramap (return @m) . coAct]

    assoc :: MonadCoAction m f => [f a -> f (m (m a))]
    assoc = [contramap join . coAct, coAct . coAct]
