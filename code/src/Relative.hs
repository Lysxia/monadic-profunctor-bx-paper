{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Relative where

-- base
import           Prelude       hiding (Monad(..))
import           Data.Kind

-- profunctors
import           Data.Profunctor

-- functor
-- -----------------------------------------------------------------------------

class RFunctor (f :: * -> *) where
  type SubCats f a :: Constraint
  type SubCats f a = ()
  rfmap :: (SubCats f a, SubCats f b) => (a -> b) -> f a -> f b

-- monad
-- -----------------------------------------------------------------------------

class RMonad t where
  type RSubCats t z :: Constraint
  type RSubCats t z = ()
  return :: (RSubCats t x) => x -> t x
  (>>=) :: (RSubCats t x, RSubCats t y) => t x -> (x -> t y) -> t y

extend :: (RSubCats t x, RSubCats t y, RMonad t) => (x -> t y) -> t x -> t y
extend x y = y Relative.>>= x

instance RMonad [] where
  type RSubCats [] z = ()
  return x = [x]
  mx >>= f = concat . map f $ mx

-- subclasses:

class RMonad m => RMonadPlus m where
  mzeroR :: m a
  mplusR :: RSubCats m a => m a -> m a -> m a

mfilterR :: (RSubCats m a, RMonadPlus m) => (a -> Bool) -> m a -> m a
mfilterR p ma = ma >>= \a -> if p a then return a else mzeroR

class RMonad m => RMonadFail m where
  fail :: String -> m a

-- profunctor
-- -----------------------------------------------------------------------------

class RProfunctor p where
  type PSubCats p d c :: Constraint
  type PSubCats p d c = ()
  lmapR :: ( PSubCats p d c
          , PSubCats p d' c
          ) => (d' -> d) -> p d c -> p d' c
  lmapR f = dimapR f id
  rmapR :: ( PSubCats p d c
          , PSubCats p d c')
          => (c -> c') -> p d c -> p d c'
  rmapR = dimapR id
  dimapR :: ( PSubCats p d c
            , PSubCats p d' c
            , PSubCats p d c'
            , PSubCats p d' c')
          => (d' -> d) -> (c -> c') -> p d c -> p d' c'
  dimapR f g = lmapR f . rmapR g
  {-# MINIMAL (dimapR) | (lmapR, rmapR) #-}


-- partial profunctor
-- -----------------------------------------------------------------------------

class RProfunctor p => RProfunctorPartial p where
  toFailureP :: p u v -> p (Maybe u) v

comap :: ( RProfunctorPartial p, RProfunctor p, PSubCats p (Maybe u') v, PSubCats p u v)
      => (u -> Maybe u') -> p u' v -> p u v
comap f = dimapR f id . toFailureP
