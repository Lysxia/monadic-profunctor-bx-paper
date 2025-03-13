{-

Implementation of a Bidirectional generator/checker as a monadic profunctor.
Differences to ESOP paper: integration with Profunctor package.

-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Bigen where

-- base
import           Control.Monad

-- profunctors
import           Data.Profunctor

-- QuickCheck
import           Test.QuickCheck hiding (generate, classify)

-- local
import           BidirectionalProfunctors
import           PartialProfunctors

newtype G u v = G { unG :: (:*:) (Fwd Gen) (Bwd Maybe) u v }

instance Functor (G u) where
  fmap f (G m) = G $ fmap f m

instance Profunctor G where
  dimap bwf fwf (G x) = G (dimap bwf fwf x)

instance PartialProfunctor G where
  internaliseMaybe :: forall u v . G u v -> G (Maybe u) v
  internaliseMaybe (G (Fwd py :*: Bwd qy)) = G (Fwd py :*: Bwd (join . fmap qy))

-- supporting internaliseMaybe must mean it supports choice:
-- (a sub-class of profunctors: https://hackage.haskell.org/package/profunctors-5.6.2/docs/Data-Profunctor-Choice.html#t:Choice)

swapE :: Either a b -> Either b a
swapE = either Right Left

instance Choice G where
  left' :: G a b -> G (Either a c) (Either b c)
  left' p = mkG
              (generate $ rmap Left p)
              (f $ check p)
    where
      f ::  (a -> Maybe b) -> Either a c -> Maybe (Either b c)
      f g (Left a) = Left <$> g a
      f g (Right c) = Nothing
        -- we can only generate values on the Left
        -- => a value on the right is wrong
  right' :: G a b -> G (Either c a) (Either c b)
  right' = dimap swapE swapE . left'
-- * lawful proof sketch at bottom

mkG :: Gen v -> (u -> Maybe v) -> G u v
mkG generate check = G (Fwd generate :*: Bwd check)

generate :: G u v -> Gen v -- forward direction
generate = unFwd . pfst . unG

check :: G u v -> u -> Maybe v -- backward direction
check = unBwd . psnd . unG

instance Monad (G u) where
  return = pure
  (G x) >>= k = G (x >>= (unG . k))

instance Monad (G u) => Applicative (G u) where
  pure = G . pure
  mf <*> mx = mf >>= (\f -> mx >>= (return . f))

-- binary search tree example

mkAlignedG :: Gen v -> (v -> Bool) -> G v v
mkAlignedG gen check = mkG gen (\y -> if check y then Just y else Nothing)

toPredicate :: G u v -> u -> Bool
toPredicate g x = isJust (check g x) where
  isJust (Just _) = True
  isJust Nothing  = False

genBool = pure . const False

bool :: Double -> G Bool Bool
bool p = mkAlignedG
  (genBool p)
  ( == False)
  --(\ _ -> True) this is a degenerate def cos it should only accept what it gens

inRange :: (Int, Int) -> G Int Int
inRange (min, max) = mkAlignedG
  (choose (min, max))
  (\x -> min <= x && x <= max)

data Tree = Leaf | Node Tree Int Tree deriving (Eq, Show)

nodeValue :: Tree -> Maybe Int
nodeValue (Node _ n _) = Just n
nodeValue _            = Nothing

nodeLeft :: Tree -> Maybe Tree
nodeLeft (Node l _ _) = Just l
nodeLeft _            = Nothing

nodeRight :: Tree -> Maybe Tree
nodeRight (Node _ _ r) = Just r
nodeRight _            = Nothing

isLeaf :: Tree -> Bool
isLeaf Leaf = True
isLeaf (Node _ _ _) = False

leaf :: G Tree Tree
leaf = mkAlignedG (return Leaf) isLeaf

bst :: (Int, Int) -> G Tree Tree
bst (min, max) | min > max = leaf
bst (min, max) = do
  isLeaf' <- comap (Just . isLeaf) (bool 0.5)
  if isLeaf' then return Leaf
  else do
    n <- comap nodeValue (inRange (min, max))
    l <- comap nodeLeft  (bst (min, n - 1))
    r <- comap nodeRight (bst (n + 1, max))
    return (Node l n r)

genBST :: Gen Tree
genBST =
  generate (bst (0, 20))

checkBST :: Tree -> Bool
checkBST =
  toPredicate (bst (0, 20))

-- if you 'sample' 'genBST' and check one with 'checkBST' it checks out.

-- Lawfulness of Choice:

(====) :: a -> a -> a
(====) = undefined

one g =
  dimap swapE swapE (right' g)
  ==== {- def. right' -}
  dimap swapE swapE ((dimap swapE swapE . left') g)
  ==== {- dimap comp law -}
  dimap (swapE . swapE) (swapE . swapE) (left' g)
  ==== {- swaps cancel -}
  dimap id id (left' g)
  ==== {- dimap id law -}
  left' g

-- meet in middle proof

two g@(G (Fwd g' :*: Bwd c)) =
  rmap Left g
  ==== {- def g -}
  rmap Left (G (Fwd g' :*: Bwd c))
  ==== {- rmap f == dimap id f -}
  dimap id Left (G (Fwd g' :*: Bwd c))
  ==== {- dimap_G -}
  (G $ dimap id Left (Fwd g' :*: Bwd c))
  ==== {- dimap_(:*:) -}
  (G (dimap id Left (Fwd g') :*: dimap id Left (Bwd c)))
  ==== {- dimap_Fwd -}
  (G (Fwd (fmap Left g') :*: dimap id Left (Bwd c)))
  ==== {- dimap_Fwd -}
  (G (Fwd (fmap Left g') :*: (Bwd (fmap Left . c . id))))
  ==== {- id -}
  (G (Fwd (fmap Left g') :*: (Bwd (fmap Left . c))))

