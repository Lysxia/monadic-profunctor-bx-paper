{-

New example for journal extension (Section 6)


Implementing the work in this paper:
https://www.microsoft.com/en-us/research/wp-content/uploads/2004/01/picklercombinators.pdf
using our framework.

The domain of the paper is pickling (or marshalling, or serializing),
which is very similar to parsing.

They use a custom structure, that closely relates to parts of our framework:

A pickler (|PU|) is just a pair of things wrapped into a record, making it very
reminiscent of our |(:*:)| structure, and very similar to our biparser

@

type St = [Char]
data PU a = PU
  { appP :: (a,St) -> St -- Bwd (~ uncurry this, to get (a, St -> St), and writer over endomorphisms)
  , appU :: St -> (a,St) -- Fwd (~ state monad)
  }

@

Their |sequ| is |comap| then |bind|

@

sequ :: (b->a) -> PU a -> (a -> PU b) -> PU b
sequ f pa k
  = PU (\ (b,s) ->
        let  a = f b
            pb = k a
        in appP pa (a, appP pb (b,s)))
      (\ s -> let (a,s’) = appU pa s
                      pb = k a
              in appU pb s’)

comap :: (u -> Maybe u') -> p u' v -> p u v
bind :: m a -> (a -> m b) -> m b

@

-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE UndecidableInstances  #-}

module BiPickle where

-- base
import           Control.Applicative
import           Control.Arrow
import           Data.Functor.Identity
import           Data.Maybe

-- htx
import           Text.XML.HXT.DOM.Util

-- mtl
import           Control.Monad.State  hiding (lift)
import           Control.Monad.Writer hiding (lift)

-- profunctors
import           Data.Profunctor

-- local
import           BidirectionalProfunctors
import           PartialProfunctors

-- Type:

type St = [Char] -- from their paper, making it easier to draw comparisons

newtype BiPi u v = BiPi { unBiPi :: (:*:) (Fwd (State St)) (Bwd (WriterT (Endo St) Maybe)) u v }
-- type State  s a = s -> (a, s)
-- type WriterT w m a = m (a, w)

-- Instances:

instance Functor (BiPi u) where
  fmap f (BiPi x) = BiPi $ fmap f x

instance Profunctor BiPi where
  dimap bwf fwf (BiPi x) = BiPi (dimap bwf fwf x)

instance PartialProfunctor BiPi where
  internaliseMaybe :: forall u v . BiPi u v -> BiPi (Maybe u) v
  internaliseMaybe (BiPi (Fwd py :*: Bwd qy)) = BiPi (Fwd py :*: Bwd handle)
    where
      -- Analogous to our previous definition of toFailure
      handle :: Maybe u -> WriterT (Endo St) Maybe v
      handle Nothing = WriterT Nothing
      handle (Just a) = qy a

-- supporting internaliseMaybe must mean it supports choice:
instance Choice BiPi where
  left' :: BiPi a b -> BiPi (Either a c) (Either b c)
  left' p = mkBiPi
              (unpick $ rmap Left p)
              (f $ pick p)
    where
      f :: (a -> Maybe (b, Endo St)) -> Either a c -> Maybe (Either b c, Endo St)
      f g (Left a)  = first Left <$> g a
      f g (Right c) = Nothing -- I think they all follow this pattern

instance Monad (BiPi u) where
  return = pure
  (BiPi x) >>= k = BiPi (x >>= (unBiPi . k))

instance Monad (BiPi u) => Applicative (BiPi u) where
  pure = BiPi . pure
  mf <*> mx = mf >>= (\f -> mx >>= (return . f))

-- Constructor:

mkBiPi :: (St -> (v, St)) -> (u -> Maybe (v, Endo St)) -> BiPi u v
mkBiPi unpick pick
  = BiPi ((Fwd $ StateT (Identity . unpick)) :*: (Bwd $ WriterT . pick))

-- Destructors:

unpick :: BiPi u v -> (St -> (v, St))
unpick = runState . unFwd . pfst . unBiPi

pick :: BiPi u v -> (u -> Maybe (v, Endo St))
pick = (runWriterT .) . unBwd . psnd . unBiPi

-- recovering their pickle and unpickle from paper (with partiality)

pickle :: BiPi u v -> u -> Maybe String
pickle p value
  = let
      f :: (v, Endo St) -> String
      f (v, Endo g) = g []
    in fmap f (pick p value)

unpickle :: BiPi u v -> String -> v
unpickle p s = fst $ unpick p s

-- Their interface:

lift :: a -> BiPi u a
lift = pure

sequ :: (b -> a) -> BiPi a a -> (a -> BiPi b b) -> BiPi b b
sequ f pa k = comap (Just . f) pa >>= k

base = 256

-- | Pickles an integer i in the range 0 <= i < |base|.
belowBase :: BiPi Int Int
belowBase = mkBiPi
              (\(c:s) -> (fromEnum c, s))
              (\x -> Just (x, Endo (\s -> toEnum x : s)))

pair :: BiPi a a -> BiPi b b -> BiPi (a,b) (a,b)
pair pa pb = do
  a <- comap (Just . fst) pa
  b <- comap (Just . snd) pb
  return (a,b)

triple :: BiPi a a -> BiPi b b -> BiPi c c -> BiPi (a,b,c) (a,b,c)
triple pa pb pc = do
  a <- comap (\(a,_,_) -> Just a) pa
  b <- comap (\(_,b,_) -> Just b) pb
  c <- comap (\(_,_,c) -> Just c) pc
  return (a,b,c)

quad :: BiPi a a -> BiPi b b -> BiPi c c -> BiPi d d -> BiPi (a,b,c,d) (a,b,c,d)
quad pa pb pc pd = do
  a <- comap (\(a,_,_,_) -> Just a) pa
  b <- comap (\(_,b,_,_) -> Just b) pb
  c <- comap (\(_,_,c,_) -> Just c) pc
  d <- comap (\(_,_,_,d) -> Just d) pd
  return (a,b,c,d)

wrap :: (a -> b, b -> a) -> BiPi a a -> BiPi b b
wrap (i,j) pa = sequ j pa (lift . i)

zeroTo :: Int -> BiPi Int Int
zeroTo 0 = lift 0
zeroTo n = wrap (\ (hi,lo) -> hi * base + lo, (`divMod` base))
                (pair (zeroTo (n `div` base)) belowBase)

unit :: BiPi () ()
unit = lift ()

char :: BiPi Char Char
char = wrap (toEnum, fromEnum) (zeroTo 255)

bool :: BiPi Bool Bool
bool = wrap (toEnum, fromEnum) (zeroTo 1)

nat :: BiPi Int Int
nat = sequ
        (\x -> if x < half then x else half + x `mod` half)
        belowBase
        (\lo -> if lo < half then lift lo else wrap (\hi->hi*half+lo, \n->n `div` half - 1) nat)
  where half = base `div` 2


fixedList :: BiPi a a -> Int -> BiPi [a] [a]
fixedList pa 0 = lift []
fixedList pa n = wrap (\(a,b) -> a:b, \(a:b) -> (a,b)) (pair pa (fixedList pa (n-1)))

list :: BiPi a a -> BiPi [a] [a]
list = sequ length nat . fixedList

string :: BiPi String String
string = list char


alt :: (a -> Int) -> [BiPi a a] -> BiPi a a
alt tag ps = sequ tag (zeroTo (length ps-1)) (ps !!)

pMaybe :: BiPi a a -> BiPi (Maybe a) (Maybe a)
pMaybe pa = alt tag [lift Nothing, wrap (Just, fromJust) pa]
  where
    tag Nothing = 0; tag (Just x) = 1

pEither :: BiPi a a -> BiPi b b -> BiPi (Either a b) (Either a b)
pEither pa pb = alt tag [wrap (Left, fromLeft) pa, wrap (Right, fromRight) pb]
  where
    tag (Left _) = 0; tag (Right _) = 1
    fromLeft (Left a) = a; fromRight (Right b) = b

-- Their examples:

-- NOTE: to match their hex results, we must use charToHexString
-- e.g.
-- >>> (toEnum 0) :: Char
-- '\NUL'
-- >>> charToHexString '\NUL'
-- "00"

-- Their Bookmarks example example:

type URL = (String, String, Maybe Int, String)
       -- (protocol, host, optional port number, filename)
type Bookmark = (String, URL)
type Bookmarks = [Bookmark]

url :: BiPi URL URL
url = quad string string (pMaybe nat) string

bookmark :: BiPi Bookmark Bookmark
bookmark = pair string url

bookmarks :: BiPi Bookmarks Bookmarks
bookmarks = list bookmark

-- Their more complex Bookmarks example example:

data Bookmark' = Link (String, URL) | Folder (String, Bookmarks')
type Bookmarks' = [Bookmark']

bookmark' :: BiPi Bookmark' Bookmark'
bookmark' = alt tag [ wrap (Link, \(Link a) -> a) (pair string url),
                      wrap (Folder, \(Folder a) -> a) (pair string bookmarks')]
  where tag (Link _) = 0; tag (Folder _) = 1

-- >>> pickle bookmarks' [Link ("Andrew", ("http", "research.microsoft.com", Nothing, "users/akenn"))]
-- Just "\SOH\NUL\ACKAndrew\EOThttp\SYNresearch.microsoft.com\NUL\vusers/akenn"
-- >>> fmap (fmap charToHexString) $ pickle bookmarks' [Link ("Andrew", ("http", "research.microsoft.com", Nothing, "users/akenn"))]
-- Just ["01","00","06","41","6E","64","72","65","77","04","68","74","74","70","16","72","65","73","65","61","72","63","68","2E","6D","69","63","72","6F","73","6F","66","74","2E","63","6F","6D","00","0B","75","73","65","72","73","2F","61","6B","65","6E","6E"]
-- expected: Just "010006416e64726577046874747016726561726368226d6963726f66742e636f6d000b75736572732f616b656e6e"
bookmarks' :: BiPi Bookmarks' Bookmarks'
bookmarks' = list bookmark'

-- Their more complex Lambda example example:

data Lambda = Var String | Lam (String, Lambda) | App (Lambda, Lambda)

lambda = alt tag [ wrap (Var, \(Var x) -> x) string,
                   wrap (Lam, \(Lam x) -> x) (pair string lambda),
                   wrap (App, \(App x) -> x) (pair lambda lambda) ]
  where tag (Var _) = 0; tag (Lam _) = 1; tag (App _) = 2

-- Their sharing example not done
