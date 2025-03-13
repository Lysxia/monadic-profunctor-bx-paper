{-

Here Bidirectional Transformations are represented by a 'Profmonad', allowing them
to be defined using the highly usable do-notation.

-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module BidirectionalProfunctors where

-- profunctors
import           Data.Profunctor

-------------------------------------------------------------------------------------
-- Reconstructing stuff from the ESOP 2019 paper, but using the Profunctor package
-------------------------------------------------------------------------------------

-- Note I am using QuantifiedConstraints now (update from what we do in the paper)
class (Profunctor p, forall u . Monad (p u)) => Profmonad p

data Fwd m u v = Fwd { unFwd :: m v }      -- ignore contrv. parameter
data Bwd m u v = Bwd { unBwd :: u -> m v } -- maps from contrv. parameter

-- Fwd functor, profunctor, monad, and applicative

instance Functor m => Functor (Fwd m u) where
  fmap f (Fwd m) = Fwd $ fmap f m

instance Functor m => Profunctor (Fwd m) where
  dimap _ fwf (Fwd mx) = Fwd (fmap fwf mx)

instance Monad m => Monad (Fwd m u) where
  Fwd py >>= kz = Fwd (py >>= unFwd . kz)

-- Derived applicative instance
instance Monad m => Applicative (Fwd m u) where
  pure x = Fwd (return x)
  mf <*> mx = mf >>= (\f -> mx >>= (\x -> return (f x)))

-- Bwd functor, profunctor, monad, and applicative

instance Functor m => Functor (Bwd m u) where
  fmap f (Bwd m) = Bwd $ \u -> fmap f $ m u

instance Functor m => Profunctor (Bwd m) where
  dimap bwf fwf (Bwd kx) = Bwd ((fmap fwf) . kx . bwf)

instance Monad m => Monad (Bwd m u) where
  Bwd my >>= kz = Bwd (\u -> my u >>= (\y -> unBwd (kz y) u))

-- Derived
instance Monad m => Applicative (Bwd m u) where
  pure x = Bwd (\_ ->return x)
  mf <*> mx = mf >>= (\f -> mx >>= (\x -> return (f x)))

--- Pairing construction

data (:*:) p q u v = (:*:) { pfst :: p u v,  psnd :: q u v }

instance (Functor (p u), Functor (q u)) => Functor ((p :*: q) u) where
  fmap f (p :*: q) = fmap f p :*: fmap f q

instance (Profunctor p, Profunctor q)
      => Profunctor (p :*: q) where
  dimap fwf bwf (py :*: qy) = dimap fwf bwf py :*: dimap fwf bwf qy

instance (Profunctor p, Profunctor q, Monad (p u), Monad (q u)) => Monad ((p :*: q) u) where
  py :*: qy >>= kz = (py >>= pfst . kz) :*: (qy >>= psnd . kz)

-- Derived
instance (Profunctor p, Profunctor q, Monad (p u), Monad (q u)) => Applicative ((p :*: q) u) where
  pure y = return y :*: return y
  mf <*> mx = mf >>= (\f -> mx >>= (\x -> return (f x)))

instance (Profmonad p, Profmonad q) => Profmonad (p :*: q)
