{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE UndecidableInstances  #-}

module BiLogicLogic where

-- base
import           Control.Applicative
import           Control.Monad

-- profunctors
import           Data.Profunctor

-- logict
import           Control.Monad.Logic

-- local
import           BidirectionalProfunctors
import           Util

------
-- Instead of partial profunctors

class (Profunctor p, Monad n) => ProfunctorMonadInternalise p n where
  internaliseMonad :: p u v -> p (n u) v

-- Recovering what we have in the paper
dimap'' :: (ProfunctorMonadInternalise p n, Monad n, Profunctor p) => (u -> n u') -> (v -> v') -> p u' v -> p u v'
dimap'' f g = dimap' f g . internaliseMonad
  where
    dimap' :: Profunctor p => (u -> n u') -> (v -> v') -> p (n u') v -> p u v'
    dimap' = dimap

comap :: (ProfunctorMonadInternalise p n, Profunctor p) => (u -> n u') -> p u' v -> p u v
comap f = dimap'' f id

-------------------------------


newtype ND m u v = ND { unND :: (:*:) (Fwd m) (Bwd Logic) u v }

instance Functor m => Functor (ND m u) where
  fmap f (ND m) = ND $ fmap f m

instance Functor m => Profunctor (ND m) where
  dimap bwf fwf (ND x) = ND (dimap bwf fwf x)

instance Monad m => ProfunctorMonadInternalise (ND m) Logic where
  internaliseMonad :: forall u v . ND m u v -> ND m (Logic u) v
  internaliseMonad (ND (Fwd py :*: Bwd qy)) = ND (Fwd py :*: Bwd (\x -> x >>= qy))

instance Monad m => Monad (ND m u) where
  (ND x) >>= k = ND (x >>= (unND . k))

instance (Monad m, Monad (ND m u)) => Applicative (ND m u) where
  pure = ND . pure
  mf <*> mx = mf >>= (\f -> mx >>= (return . f))

-- constructor
mkND :: Monad m => m v -> (u -> Logic v) -> ND m u v
mkND choices check = ND (Fwd choices :*: Bwd check)

mkAlignedND :: Monad m => m v -> (v -> Bool) ->  ND m v v
mkAlignedND gen check = mkND gen (\y -> if check y then return y else empty)

-- deconstructors
choices :: Monad m => ND m u v -> m v -- forward direction
choices = unFwd . pfst . unND

choose :: Monad m => (m v -> v) -> ND m u v -> v
choose f = f . unFwd . pfst . unND

check :: Monad m => ND m u v -> u -> Logic v -- backward direction
check = unBwd . psnd . unND

-- # Example

parents :: [ (String, String) ]
parents = [
  ("Gomez", "Wednesday")
  , ("Morticia", "Wednesday")
  , ("Grandmama", "Gomez")
  , ("Grandmama", "Bob")]

childrenOf :: String -> Logic String
childrenOf p = do
  (p', c) <- pick parents
  guard (p == p')
  pure c

parentOf :: String -> Logic String
parentOf c = do
  (p, c') <- pick parents
  guard (c == c')
  pure p

pick :: [a] -> Logic a
pick = foldr ((<|>) . pure) empty

-- Maybe:

parentOfB :: String -> ND Logic String String
parentOfB n = mkAlignedND
                (parentOf n)
                (\s -> s `elem` observeAll (parentOf n))

comap' :: (u -> Logic u') -> ND Logic u' v -> ND Logic u v
comap' f (ND ((Fwd fwd') :*: (Bwd bwd'))) =
   ND ((Fwd fwd') :*: (Bwd (\x -> f x >>= bwd')))
   -- bwd' :: u' -> [v]


grandparentsOfB :: String -> ND Logic String String
grandparentsOfB c = do
  parent <- childrenOf `comap` parentOfB c
  parentOfB parent

exampleChoose =
  observeAll $ choices (grandparentsOfB "Wednesday")

exampleCheck =
  observeAll $ check (grandparentsOfB "Wednesday") "Grandmama"
