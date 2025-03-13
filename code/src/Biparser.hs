{-

Implementation of a Biparser as a monadic profunctor.
Differences to ESOP paper: integration with Profunctor package.

-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Biparser where

-- base
import           Control.Monad
import           Data.Char                (isDigit, isSpace)
import           Data.Functor.Identity
import           Prelude                  hiding (print)

-- mtl
import           Control.Monad.State
import           Control.Monad.Writer

-- profunctors
import           Data.Profunctor


-- local
import           BidirectionalProfunctors
import           PartialProfunctors

-- type State  s a = s -> (a, s)
-- type WriterT w m a = m (a, w)

newtype Biparser u v = Biparser { unP :: (:*:) (Fwd (State String)) (Bwd (WriterT String Maybe)) u v }

instance Functor (Biparser u) where
  fmap f (Biparser m) = Biparser $ fmap f m

instance Profunctor Biparser where
  dimap bwf fwf (Biparser x) = Biparser (dimap bwf fwf x)

instance PartialProfunctor Biparser where
  internaliseMaybe :: forall u v . Biparser u v -> Biparser (Maybe u) v
  internaliseMaybe (Biparser (Fwd py :*: Bwd qy)) = Biparser (Fwd py :*: Bwd handle)
    where
      -- Analogous to our previous definition of toFailure
      handle :: Maybe u -> WriterT String Maybe v
      handle Nothing  = WriterT Nothing
      handle (Just a) = qy a

mkBP :: (String -> (v, String)) -> (u -> Maybe (v, String)) -> Biparser u v
mkBP parser print = Biparser ((Fwd $ StateT (Identity . parser)) :*: (Bwd $ WriterT . print))

parse :: Biparser u v -> (String -> (v, String))
parse = runState . unFwd . pfst . unP

print :: Biparser u v -> (u -> Maybe (v, String))
print = (runWriterT .) . unBwd . psnd . unP

instance Monad (Biparser u) where
  return = pure
  (Biparser x) >>= k = Biparser (x >>= (unP . k))

instance Monad (Biparser u) => Applicative (Biparser u) where
  pure = Biparser . pure
  mf <*> mx = mf >>= (\f -> mx >>= (return . f))

-- Simple biparsers

char :: Biparser Char Char
char = mkBP (\ (c : s) -> (c, s)) (\ c -> Just (c, [c]))

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

safeTail :: [a] -> Maybe [a]
safeTail []     = Nothing
safeTail (_:xs) = Just xs

int :: Biparser Int Int
int = do
  ds <- digits `upon` printedInt
  return (read ds)
  where
    printedInt n = Just (show n ++ " ")

digits :: Biparser String String
digits = do
  d <- char `upon` safeHead
  if isDigit d then do
    igits <- digits `upon` safeTail
    return (d : igits)
  else if d == ' ' then return " "
  else error "Expected digit or space"

replicateBiparser :: Int -> Biparser u v -> Biparser [u] [v]
replicateBiparser 0 pv = return []
replicateBiparser n pv = do
  v  <- pv `upon` safeHead
  vs <- (replicateBiparser (n - 1) pv) `upon` safeTail
  return (v : vs)

string :: Biparser String String
string = int `upon` (Just  . length) >>= \n -> replicateBiparser n char

test1 = parse string "6 lambda calculus" == ("lambda", " calculus")
test2 = print string "SKI" == Just ("SKI", "3 SKI")
