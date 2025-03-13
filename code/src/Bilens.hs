{-

Implementation of a Bidirectional Lens as a monadic profunctor.
Differences to ESOP paper: integration with Profunctor package.

-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Bilens where

-- base
import           Data.Maybe
import           Prelude                  hiding (lookup)

-- containers
import           Data.Map

-- profunctors
import           Data.Profunctor

-- mtl
import           Control.Monad.Reader
import           Control.Monad.State      hiding (get, put)
import           Control.Monad.Writer

-- local
import           BidirectionalProfunctors
import           PartialProfunctors
import           Util

-- type ReaderT r m a = r → m a
-- type StateT s m a = s → m (a, s)
-- type WriterT w m a = m (a, w)

newtype L s u v = L {unL :: (:*:)
                          (Fwd (ReaderT s Maybe))
                          (Bwd (StateT s (WriterT (s -> Bool) Maybe)))
                          u
                          v
                          }

instance Functor (L s u) where
  fmap f (L m) = L $ fmap f m

instance Profunctor (L s) where
  dimap bwd fwd (L x) = L (dimap bwd fwd x)

instance PartialProfunctor (L s) where
  internaliseMaybe :: forall u v . L s u v -> L s (Maybe u) v
  internaliseMaybe ((L (Fwd g :*: Bwd p))) = L (Fwd g :*: Bwd handle)
    where
      handle :: Maybe u -> StateT s (WriterT (s -> Bool) Maybe) v
      handle Nothing = StateT (\_ -> WriterT Nothing)
      handle (Just x) = p x

mkLens :: (s -> Maybe v) -> (u -> s -> Maybe ((v, s), s -> Bool)) -> L s u v
mkLens g p = L ((Fwd $ ReaderT g) :*: (Bwd $ (\u -> StateT (\s -> WriterT (p u s)))))

-- StateT :: (s -> m (a, s)) -> StateT s m a
-- WriterT :: m (a, w) -> WriterT w m a

get :: L s u v -> (s -> Maybe v)
get = runReaderT . unFwd . pfst . unL

put :: L s u v -> (u -> s -> Maybe ((v, s), s -> Bool))
put = (\f u s -> runWriterT $ runStateT (f u) s) . unBwd . psnd . unL

instance Monad (L s u) where
  return = pure
  (L x) >>= f = L (x >>= (unL . f))

instance Semigroup Bool where
  (<>) = (&&)

instance Monoid Bool where
  mempty = True

instance Monad (L s u) => Applicative (L s u) where
  pure = L . pure
  mf <*> mx = mf >>= (\f -> mx >>= (return . f))

-- key-value example

type Src = Map Key Value

type Key   = Int
type Value = String

atKey :: Key -> L Src Value Value  -- Key-focussed lens
atKey k = mkLens (lookup k)
  (\v map -> Just ((v, insert k v map), \m' -> lookup k m' == Just v))

atKeys :: [Key] -> L Src [Value] [Value]
atKeys [] = return []
atKeys (k : ks) = do
  x  <- comap headM (atKey k)     -- headM :: [a] -> Maybe a
  xs <- comap tailM (atKeys ks)   -- tailM :: [a] -> Maybe [a]
  return (x : xs)

test1 = isNothing $ get (atKey 0) empty
test2 = get (atKey 0) (singleton 0 "hello") == Just "hello"
test3 = get (atKey 1) (fromList [(0, "hello"), (1, "world")]) == Just "world"

test4 = (fst . fromJust $ put (atKey 0) "hello" empty) == ("hello",fromList [(0,"hello")])
test5 = (fst . fromJust $ put (atKey 0) "world" (singleton 0 "hello")) == ("world",fromList [(0,"world")])

test6 = get (atKeys []) empty == Just []
test7 = get (atKeys [0,1]) (fromList [(0, "hello"), (1, "world")]) == Just ["hello", "world"]
test8 = isNothing $ get (atKeys [0,1]) (fromList [(0, "hello"), (2, "world")])

test9 = (fst . fromJust $ put (atKeys [0]) ["hello"] empty) == (["hello"],fromList [(0,"hello")])
test10 = (fst . fromJust $ put (atKeys []) [] empty) == ([], empty)

-- Bigger example: Trees

data Tree = Leaf | Node Tree Int Tree deriving (Eq, Show)

(>>>) :: L s t t -> L t u u -> L s u u
lt >>> ly = mkLens get' put' where
  -- get' :: s -> Maybe u
  get' s = get lt s >>= get ly

  -- put' :: u -> s ->
  --        Maybe ((u, s), s -> Bool)
  put' xu s =
   case get lt s of
     Nothing -> Nothing
     Just t -> do
        ((y, xt), q') <- put ly xu t
        ((_, s'), p') <- put lt xt s
        if q' xt
          then Just ((y, s'), p')
          else Nothing

rootL :: L Tree (Maybe Int) (Maybe Int)
rootL = mkLens getter putter
  where
   getter (Node _ n _) = Just (Just n)
   getter Leaf         = Just Nothing

   putter n' t = Just ((n', t'), p)
    where
      t' = case (t, n') of
        (_,    Nothing) -> Leaf
        (Leaf, Just n)  -> Node Leaf n Leaf
        (Node l _ r, Just n)  -> Node l n r
      p t'' = getter t' == getter t''

rightL :: L Tree Tree Tree
rightL = mkLens getter putter
  where
   getter (Node _ _ r) = Just r
   getter  _           = Nothing

   putter r Leaf = Nothing
   putter r (Node l n _) = Just
     ((r, Node l n r),
       \t' -> Just r == getter t')


spineL :: L Tree [Int] [Int]
spineL = do
  hd <- comap (Just . headM) rootL
  case hd of
    Nothing -> return []
    Just n -> do
      tl <- comap tailM (rightL >>> spineL)
      return (n : tl)

test11 = get spineL Leaf == Just []
test12 = get spineL (Node Leaf 1 Leaf) == Just [1]
test13 = get spineL (Node (Node Leaf 2 Leaf) 1 Leaf) == Just [1]
test14 = get spineL (Node Leaf 1 (Node Leaf 2 Leaf)) == Just [1, 2]

test15 = (fst . fromJust $ put spineL [] Leaf) == ([], Leaf)
test16 = (fst . fromJust $ put spineL [3,4] (Node Leaf 1 (Node Leaf 2 Leaf))) == ([3, 4], Node Leaf 3 (Node Leaf 4 Leaf))
