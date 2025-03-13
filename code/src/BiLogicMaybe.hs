{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module BiLogicMaybe where

-- base
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fail (MonadFail)
import qualified Control.Monad.Fail as F
import           Data.List
import           Data.Maybe

-- containers
import           Data.Set           (Set)
import qualified Data.Set           as S

-- logict
import           Control.Monad.Logic

-- mtl
import          Control.Monad.State.Lazy

-- profunctors
import           Data.Profunctor

-- QuickCheck
import           Test.QuickCheck      hiding (generate, classify)

-- transformers
import           Control.Monad.Trans.Maybe

-- local
import           BidirectionalProfunctors
import           PartialProfunctors
import           Util

-- Logic example

--  "what move will I select?"
--
-- choices -------> decision
--                     ||
--                     ||
--                     ||
--             ?       \/
-- choices <------- decision
--
--  "Is this a valid move?"


-- -----------------------------------------------------------------------------
-- Maybe
-- -----------------------------------------------------------------------------

newtype ND m u v = ND { unND :: (:*:) (Fwd m) (Bwd Maybe) u v }

-- instances:

instance Functor m => Functor (ND m u) where
  fmap f (ND m) = ND $ fmap f m

instance Functor m => Profunctor (ND m) where
  dimap bwf fwf (ND x) = ND (dimap bwf fwf x)

instance Monad m => PartialProfunctor (ND m) where
  internaliseMaybe :: forall u v . ND m u v -> ND m (Maybe u) v
  internaliseMaybe (ND (Fwd py :*: Bwd qy)) = ND (Fwd py :*: Bwd (join . fmap qy))

instance Monad m => Monad (ND m u) where
  return = pure
  (ND x) >>= k = ND (x >>= (unND . k))

instance (Monad m, Monad (ND m u)) => Applicative (ND m u) where
  pure = ND . pure
  mf <*> mx = mf >>= (\f -> mx >>= (return . f))

-- constructor
mkND :: Monad m => m v -> (u -> Maybe v) -> ND m u v
mkND choices check = ND (Fwd choices :*: Bwd check)

mkAlignedND :: Monad m => m v -> (v -> Bool) ->  ND m v v
mkAlignedND gen check = mkND gen (\y -> if check y then Just y else Nothing)

-- deconstructors
choices :: Monad m => ND m u v -> m v -- forward direction
choices = unFwd . pfst . unND

choose :: Monad m => (m v -> v) -> ND m u v -> v
choose f = f . unFwd . pfst . unND

check :: Monad m => ND m u v -> u -> Maybe v -- backward direction
check = unBwd . psnd . unND

toPredicate :: Monad m => ND m u v -> u -> Bool
toPredicate nd x = isJust (check nd x) where
  isJust (Just _) = True
  isJust Nothing  = False

-- This generalises Gen
-- -----------------------------------------------------------------------------

mkG :: Gen v -> (u -> Maybe v) -> ND Gen u v
mkG = mkND

generate :: ND Gen u v -> Gen v -- forward direction
generate = choices

-- Gen bin search example:

mkAlignedG :: Gen v -> (v -> Bool) -> ND Gen v v
mkAlignedG gen check = mkG gen (\y -> if check y then Just y else Nothing)

genBool = pure . const False

bool :: Double -> ND Gen Bool Bool
bool p = mkAlignedG
  (genBool p)
  (const True)

inRange :: (Int, Int) -> ND Gen Int Int
inRange (min, max) = mkAlignedG
  (Test.QuickCheck.choose (min, max))
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
isLeaf _    = False

leaf :: ND Gen Tree Tree
leaf = mkAlignedG (return Leaf) isLeaf

bst :: (Int, Int) -> ND Gen Tree Tree
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

-- examples
-- -----------------------------------------------------------------------------

-- chess example

possibleMoves :: [String]
possibleMoves = ["castle","conceed"]

emptyStrat :: ND [] String String
emptyStrat =  mkND [] (const Nothing)

test1 :: [String]
test1 = choices emptyStrat

test2 :: Bool
test2 = toPredicate emptyStrat "conceed"

castleOrDieStrat :: ND [] String String
castleOrDieStrat = mkND
                    possibleMoves
                    (\s -> if s `elem` possibleMoves then Just s else Nothing)

test3 :: [String]
test3 = choices castleOrDieStrat

test4 :: Bool
test4 = toPredicate castleOrDieStrat "castle"
test5 = toPredicate castleOrDieStrat "conceed"
test6 = toPredicate castleOrDieStrat "pawn"

-- curry example

trueOrFalse :: MonadPlus m =>m Bool
trueOrFalse = mplus (pure True) (pure False)

trueOrFalseND :: MonadPlus m => ND m Bool Bool
trueOrFalseND = mkND
                  trueOrFalse
                  (const (Just True)) -- they can only provide a bool

ctest1 = choices (trueOrFalseND @[])
ctest2 = toPredicate (trueOrFalseND @[]) True
ctest3 = toPredicate (trueOrFalseND @[]) False

listND :: Eq a => [a] -> ND [] a a
listND xs = mkND
            xs
            (\x -> if x `elem` xs then Just x else Nothing)

ltest1 = choices (listND [1,2,3])
ltest2 = toPredicate (listND [1,2,3]) 1
ltest3 = toPredicate (listND [1,2,3]) 4

trueND :: Monad m => ND m Bool Bool
trueND = mkND
          (pure True)
          (\b -> if b then Just b else Nothing)

ttest1 = choices (trueND @[])
ttest2 = toPredicate (trueND @[]) True
ttest3 = toPredicate (trueND @[]) False

falseND :: Monad m => ND m Bool Bool
falseND = mkND
          (pure False)
          (\b -> if b then Nothing else Just b)

ftest1 = choices (falseND @[])
ftest2 = toPredicate (falseND @[]) True
ftest3 = toPredicate (falseND @[]) False

startsWith :: Monad m => [Bool] -> ND m [Bool] [Bool]
startsWith [] = return []
startsWith (b : xs)= do
    b <- if b then comap headM trueND else comap headM falseND
    bs <- comap tailM (startsWith xs)
    return (b : bs)

listSndMaybe :: [a] -> Maybe a
listSndMaybe [] = Nothing
listSndMaybe (_:x:_) = Just x

t1 = choices (startsWith @[] [True,False])
t2 = toPredicate (startsWith @[] [True,False]) [True]
t3 = toPredicate (startsWith @[] [True,False]) [True,False]
t4 = toPredicate (startsWith @[] [True,False]) [True,False, True]
t5 = toPredicate (startsWith @[] [True,False]) [True,False, True, True, True]

oneBool :: MonadPlus m => ND m [Bool] [Bool]
oneBool =
  do
    b <- comap f trueOrFalseND
    return [b]
  where
    f :: [Bool] -> Maybe Bool
    f [b] = Just b
    f _ = Nothing

-- >>> choices (oneBool @ [])
-- [[True],[False]]
-- >>> toPredicate (oneBool @ []) []
-- False
-- >>> toPredicate (oneBool @ []) [True]
-- True
-- >>> toPredicate (oneBool @ []) [False]
-- True
-- >>> toPredicate (oneBool @ []) [False, True]
-- False

-- leaving the m general allows for different search strats:
-- http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=879C8454322C07FB7842D1C76B3F8216?doi=10.1.1.157.4578&rep=rep1&type=pdf
-- Maybe = first result of depth first search
-- >>> choices  (oneBool @ Maybe)
--Just [True]
-- see other BiLogic files for other ms

-- n-queens example

conflict :: Pos -> Pos -> Bool
conflict (x1,y1) (x2,y2)
  | y1 == y2 = True -- horizontal conflict
  | x1 == x2 = True -- vertical conflict
  | otherwise = abs (x1 - x2) == abs (y1 - y2)

chessPositions :: [Pos]
chessPositions = [ (x, y) | x <- [0..7], y <- [0..7] ]

type Pos = (Int, Int) -- (x,y)

safePlacing
  :: [Pos] -- already placed queens
  -> ND [] Pos Pos
safePlacing qs
  = mkAlignedND
      (filter safeReCurrentQueens chessPositions)
      safeReCurrentQueens
    where
      safeReCurrentQueens p = all (not . conflict p) qs

q1 = choices (safePlacing [(0,7), (1,5), (2,6), (5,4), (7,3)]) -- Should be [(3,0),(3,1),(4,1)]
-- should be true
q2 = toPredicate (safePlacing [(0,7), (1,5), (2,6), (5,4), (7,3)]) (3,0) -- True
q3 = toPredicate (safePlacing [(0,7), (1,5), (2,6), (5,4), (7,3)]) (3,1) -- True
q4 = toPredicate (safePlacing [(0,7), (1,5), (2,6), (5,4), (7,3)]) (4,1) -- True
-- should be false
q5  = toPredicate (safePlacing [(0,7), (1,5), (2,6), (5,4), (7,3)]) <$> chessPositions \\ [(3,0),(3,1),(4,1)] -- False

-- NOTE very inefficient
nQueens
  :: Int -- how many queens
  -> ND [] [Pos] [Pos] -- list of possible positions for n queens
nQueens 0 = pure []
nQueens n
  | n > 8 = reject
  | n < 0 = reject
  | otherwise = do
    xs <- comap tailM (nQueens (n-1))
    -- add a new member that is not already on the side, and is compatible with everyone
    x  <- comap headM (safePlacing xs)
    return (x:xs)

reject :: MonadFail m => ND m a a
reject = mkAlignedND
          (F.fail "reject")
          (const False)

nq1 = take 1 $ choices (nQueens 8) -- should be [(7,3),(6,1),(5,6),(4,2),(3,5),(2,7),(1,4),(0,0)]
-- should be true
nq2 = toPredicate (nQueens 8) [(1,0), (6,1), (4,2), (7,3), (0,4), (3,5), (5,6), (2,7)]
nq3 = toPredicate (nQueens 8) [(7,3),(6,1),(5,6),(4,2),(3,5),(2,7),(1,4),(0,0)]
nq4 = toPredicate (nQueens 1) [(7,7)]
-- should be false
nq5 = toPredicate (nQueens 8) [(7,7)]
nq6 = toPredicate (nQueens 2) [(7,7), (7,6)]
nq7 = toPredicate (nQueens 2) [(7,7), (7,7)]


