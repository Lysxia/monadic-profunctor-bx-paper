-- uses a relative monad based on https://www.doc.ic.ac.uk/~dorchard/drafts/tfp-structures-orchard12.pdf

{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module RelativeRecovery where

-- base
import           Prelude       hiding (Monad(..), fail)
import qualified Prelude
import           Control.Monad hiding (Monad(..), fail)
import           Data.Foldable (toList)
import           Data.Kind          ( Constraint )
import           Data.List
import           Data.Maybe

-- containers
import           Data.Set           (Set)
import qualified Data.Set           as S

-- mtl
import           Control.Monad.State.Lazy hiding (Monad(..), fail)

-- profunctors
import           Data.Profunctor

-- transformers
import           Control.Monad.Trans.Maybe

-- local
import           BidirectionalProfunctors   (Fwd(..), Bwd(..), (:*:)(..))
import           Relative
import           Util

-- Fwd instances
instance RFunctor m => RProfunctor (Fwd m) where
  type PSubCats (Fwd m) a b = SubCats m b
  dimapR :: ( PSubCats (Fwd m) d c
            , PSubCats (Fwd m) d' c')
            => (d' -> d) -> (c -> c') -> Fwd m d c -> Fwd m d' c'
  dimapR _ fwf (Fwd mx) = Fwd (rfmap fwf mx)

instance RMonad m => RMonad (Fwd m u) where
  type RSubCats (Fwd m u) v = RSubCats m v
  return x = Fwd (return x)
  Fwd py >>= kz = Fwd (py >>= (unFwd . kz))

instance (RMonad m, RMonadPlus m) => RMonadPlus (Fwd m u) where
  mzeroR = Fwd mzeroR
  (Fwd x) `mplusR` (Fwd y) = Fwd (x `mplusR` y)

-- Bwd instances

instance RFunctor m => RProfunctor (Bwd m) where
  type PSubCats (Bwd m) a b = SubCats m b
  dimapR :: ( PSubCats (Bwd m) d c
            , PSubCats (Bwd m) d' c')
            => (d' -> d) -> (c -> c') -> Bwd m d c -> Bwd m d' c'
  dimapR bwf fwf (Bwd kx) = Bwd ((rfmap fwf) . kx . bwf)

instance RMonad m => RMonad (Bwd m u) where
  type RSubCats (Bwd m u) v = RSubCats m v
  return x = Bwd (\_ -> return x)
  Bwd my >>= kz = Bwd (\u -> my u >>= (\y -> unBwd (kz y) u))

instance (RMonad m, RMonadPlus m) => RMonadPlus (Bwd m u) where
  mzeroR = Bwd (const mzeroR)
  (Bwd x) `mplusR` (Bwd y) = Bwd (\u -> x u `mplusR` y u)

-- (:*:) instances

instance (RProfunctor p, RProfunctor q)
      => RProfunctor (p :*: q) where
  type PSubCats (p :*: q) a b = (PSubCats p a b, PSubCats q a b)
  dimapR :: ( PSubCats (p :*: q) d c
            , PSubCats (p :*: q) d c'
            , PSubCats (p :*: q) d' c
            , PSubCats (p :*: q) d' c')
            => (d' -> d) -> (c -> c') -> (p :*: q) d c -> (p :*: q) d' c'
  dimapR fwf bwf (py :*: qy) = dimapR fwf bwf py :*: dimapR fwf bwf qy

instance {-# OVERLAPPING #-} (RMonad (p u), RMonad (q u)) => RMonad ((p :*: q) u) where
  type RSubCats ((p :*: q) u) v = (RSubCats (p u) v, RSubCats (q u) v)
  return y = return y :*: return y
  py :*: qy >>= kz = (py >>= (pfst . kz)) :*: (qy >>= (psnd . kz))

instance (RMonadPlus (p u), RMonadPlus (q u))
  => RMonadPlus( (p :*: q) u) where
  mzeroR = mzeroR :*: mzeroR
  (p1 :*: p2) `mplusR` (q1 :*: q2) = (p1 `mplusR` q1) :*: (p2 `mplusR` q2)

-- MaybeT (State Bool) instances

instance RMonad (MaybeT (State Bool)) where
  type RSubCats (MaybeT (State Bool)) a = ()
  return = Prelude.return
  (>>=) = (Prelude.>>=)

instance RFunctor (MaybeT (State Bool)) where
  type SubCats (MaybeT (State Bool)) a = ()
  rfmap = fmap

instance RMonadPlus (MaybeT (State Bool)) where
  mzeroR = mzero
  mplusR = mplus

-- Set instances

instance RMonad Set where
  type RSubCats Set a = Ord a
  return = S.singleton
  (>>=) :: (Ord a, Ord b) => Set a -> (a -> Set b) -> Set b
  sa >>= f = S.unions (S.map f sa)

instance RMonadFail Set where
  fail _ = S.empty

instance RMonadPlus Set where
  mzeroR = S.empty
  mplusR = S.union

instance RFunctor Set where
  type SubCats Set a = Ord a
  rfmap = S.map

-- -----------------------------------------------------------------------------

-- RR

newtype RR m u v = RR { unRR :: (:*:) (Fwd m) (Bwd (MaybeT (State Bool))) u v }

-- instances:

instance RFunctor m => RProfunctor (RR m) where
  type PSubCats (RR m) u v = PSubCats ((:*:) (Fwd m) (Bwd (MaybeT (State Bool)))) u v
  dimapR bwf fwf (RR x) = RR (dimapR bwf fwf x)

instance (RFunctor m, RMonad m) => RProfunctorPartial (RR m) where
  toFailureP :: forall u v . RR m u v -> RR m (Maybe u) v
  toFailureP (RR (Fwd py :*: Bwd qy)) = RR (Fwd py :*: Bwd (handle . fmap qy))
    where
      handle :: Maybe (MaybeT (State Bool) v) -> MaybeT (State Bool) v
    -- handle :: Maybe (State Bool (Maybe v)) -> State Bool (Maybe v)
      handle Nothing  = MaybeT $ pure Nothing
      handle (Just v) = v

instance RMonad m => RMonad (RR m u) where
  type RSubCats (RR m u) v = RSubCats m v
  return = RR . return
  (RR x) >>= k = RR (x >>= (unRR . k))

instance (RMonadPlus m, RMonad m) => RMonadPlus (RR m u) where
  mzeroR = RR mzeroR
  (RR x)`mplusR`(RR y) = RR (x `mplusR` y)

-- constructors:

mkRR :: RMonad m => m v -> (u -> MaybeT (State Bool) v) -> RR m u v
mkRR choices check = RR (Fwd choices :*: Bwd check)

-- | Smart constructor for creating an 'RR' that only cares whether an irrecoverable
--   failure has happened
mkIrrecoverable :: RMonad m => m v -> (v -> Bool) ->  RR m v v
mkIrrecoverable gen check = mkRR gen c
  where
    c y
      | check y = pure y
      | otherwise = MaybeT $ pure Nothing

-- | Smart constructor for creating an 'RR' that also keep track of our status
--   regarding recoverable failures.
mkRecoverable :: RMonad m => m v -> (v -> Bool) ->  RR m v v
mkRecoverable gen check = mkRR gen c
  where
    c y
      | check y = MaybeT . state $ const (Just y, True)
      | otherwise =  MaybeT . state $ const (Just y, False)

-- deconstructors:

choicesR :: RMonad m => RR m u v -> m v -- forward direction
choicesR = unFwd . pfst . unRR

chooseR :: RMonad m => (m v -> v) -> RR m u v -> v
chooseR f = f . unFwd . pfst . unRR

checkR :: RMonad m => RR m u v -> u -> MaybeT (State Bool) v -- backward direction
checkR = unBwd . psnd . unRR

-- We have three more specialised check functions that consider the different types
-- of failure (recoverable and irrecoverable):
--    ultimateSuccess checks both
--    recoveredSuccess checks for just recoverable failures
--    justSuccess checks for just irrecoverable failures

-- | Checks that nothing has gone wrong: nothing irrecoverable has happened, and
--   we are in a good state according to the recoverable failure flag.
ultimateSuccess
  :: RMonad m => RR m u v -> u -> Bool
ultimateSuccess nd x = isJust (evalState (runMaybeT (checkR nd x)) True) -- nothing irrecoverable has happened
                          && execState (runMaybeT (checkR nd x)) True    -- we are in a good state according to the recoverable failure flag
-- starting state is True cos initially everything is fine

-- | Checks that we are in a good state according to the recoverable failure flag.
recoveredSuccess
  :: RMonad m => RR m u v -> u -> Bool
recoveredSuccess nd x = execState (runMaybeT (checkR nd x)) True
-- starting state is True cos initially everything is fine

-- | Checks that nothing irrecoverable has happened
justSuccess
  :: RMonad m => RR m u v -> u -> Bool
justSuccess nd x = execState (runMaybeT (checkR nd x)) True
-- starting state is True cos initially everything is fine

-- River Crossing example with Set
-- -----------------------------------------------------------------------------

-- set up:

data Actor = Human | Fox | Chicken | Grain deriving (Show, Eq, Ord) -- ord reflects food chain

chars = S.fromList [Human, Chicken, Fox, Grain]

compatible :: Actor -> Actor -> Bool
compatible Fox     Chicken = False
compatible Chicken Grain   = False
compatible Chicken Fox     = False
compatible Grain   Chicken = False
compatible _       _       = True

data Side = L | R deriving (Show, Eq, Ord)

row :: Side -> Side
row L = R
row R = L

data ProbState = ProbState
  { leftBank  :: Set Actor
  , boat      :: Set Actor
  , rightBank :: Set Actor
  , boatLocation :: Side
  } deriving (Show, Eq, Ord)

-- solution

-- An irrecoverable error
rejectR :: RMonadFail m => RR m a a
rejectR = mkIrrecoverable
          (fail "reject")
          (const False)

compatR :: Set Actor -> RR Set Actor Actor
compatR xs = mkRecoverable
                f
                (\c ->  (all (compatible c) xs || Human `elem` xs) && notElem c xs)
  where
    f
      | Human `elem` xs = chars S.\\ xs -- add anyone new
      | otherwise       = foldl (\n e -> S.filter (compatible e) n) (chars S.\\ xs) xs -- add someone non conflicting

-- should be true
c2R = recoveredSuccess (compatR . S.fromList $ [Chicken]) Human
c3R = recoveredSuccess (compatR . S.fromList $ [Fox]) Grain
c4R = recoveredSuccess (compatR . S.fromList $ [Fox]) Human
c5R = recoveredSuccess (compatR . S.fromList $ [Human, Chicken]) Fox
c6R = recoveredSuccess (compatR . S.fromList $ [Human]) Grain
-- should be false
c7R = recoveredSuccess (compatR . S.fromList $ [Chicken]) Fox
c8R = recoveredSuccess (compatR . S.fromList $ [Fox]) Chicken
c9R = recoveredSuccess (compatR . S.fromList $ [Fox]) Fox
-- generation
c10R = choicesR (compatR . S.fromList $ [Chicken]) == S.singleton Human
c11R = choicesR (compatR . S.fromList $ [Human]) == S.fromList [Chicken, Grain, Fox]

cRallT = and [c2R, c3R, c4R, c5R, c6R]
cRallF = not (c7R || c8R || c9R)
cRallG = c10R && c11R

cRTests = cRallT && cRallF && cRallG

safeSideR
  :: Int -- number of people on the side
  -> RR Set (Set Actor) (Set Actor)
safeSideR 0 = return S.empty
safeSideR n
  | n > 4 = rejectR
  | n < 0 = rejectR
  | otherwise = do
    xs <- comap tailS (safeSideR (n-1))
    -- add a new member that is not already on the side, and is compatible with everyone
    x  <- comap headS (compatR xs) -- produces a set with all four, then always takes the first
    return (S.insert x xs)

-- the interaction between the comap and the monad is what is causing the spin

headS :: Set a -> Maybe a
headS = S.lookupMax

tailS :: Ord a => Set a -> Maybe (Set a)
tailS = Just . S.deleteMax

ss1R = choicesR (safeSideR 0) == return S.empty
ss2R = null $ choicesR (safeSideR 5)
ss3R = not $ ultimateSuccess (safeSideR 5) S.empty
ss4R = choicesR (safeSideR 2) == S.fromList [S.fromList [Chicken, Human], S.fromList [Fox, Human],S.fromList [Grain, Human],S.fromList [Human, Chicken],S.fromList [Grain, Fox]]
ss5R = choicesR (safeSideR 3) == S.fromList [S.fromList [ Fox, Chicken, Human],S.fromList [ Grain, Chicken, Human],S.fromList [ Grain, Fox, Human]]

-- should all be false
ss6R  = ultimateSuccess (safeSideR 2) $ S.fromList []        -- False
ss7R  = ultimateSuccess (safeSideR 2) $ S.fromList [Chicken] -- False
ss8R  = ultimateSuccess (safeSideR 2) $ S.fromList [Grain]   -- False
ss9R  = ultimateSuccess (safeSideR 2) $ S.fromList [Fox]     -- False
ss10R = ultimateSuccess (safeSideR 2) $ S.fromList [Human]   -- False
ss11R = recoveredSuccess (safeSideR 2) $ S.fromList [Grain, Chicken, Human]
ss12R = ultimateSuccess (safeSideR 2) $ S.fromList [Fox, Grain, Chicken]
-- should be true:
ss13R  = recoveredSuccess (safeSideR 1) $ S.fromList [Grain] -- True
ss14R  = recoveredSuccess (safeSideR 2) $ S.fromList [Human, Chicken] -- True
ss14R' = recoveredSuccess (safeSideR 2) $ S.fromList [Chicken, Human] -- True
ss15R  = recoveredSuccess (safeSideR 2) $ S.fromList [Fox, Grain]     -- True
ss16R  = recoveredSuccess (safeSideR 3) $ S.fromList [Human, Grain, Fox] -- True
-- Should be false
ss17R = recoveredSuccess (safeSideR 2) $ S.fromList [Chicken, Grain] -- False

allssR = and [ss1R, ss2R, ss3R, ss4R, ss5R]
      && not (or [ss6R, ss7R, ss8R, ss9R, ss10R])
      && not ss11R && not ss12R
      && and [ss13R, ss14R, ss14R', ss15R, ss16R]
      && not ss17R

-- both should be true
problemR1 = recoveredSuccess (safeSideR 3) $ S.fromList [Human, Grain, Chicken]  -- true
problemR1' = recoveredSuccess (safeSideR 3) $ S.fromList [Grain, Chicken, Human] -- true

problemsR = problemR1 && problemR1'

-- A valid state only has one of each actor, and four in total, the boat has a
-- max capacity of 2, and if anyone is on the boat, the human must be one of them
validState :: ProbState -> Bool
validState ps =  length as == 4                                 -- 4 actors
              && length as' == 4                                -- one of each
              && S.size (boat ps) <= 2                          -- boat in capacity
              && (S.null (boat ps) || S.member Human (boat ps)) -- boat mzero, or human on boat
  where
    as  = S.toList (leftBank ps) ++ S.toList (rightBank ps) ++ S.toList (boat ps)
    as' = nub as

vs1 = not $ validState (ProbState S.empty S.empty S.empty R)
vs2 = not $ validState (ProbState S.empty (S.fromList [Human, Fox, Chicken, Grain]) S.empty R)
vs3 = not $ validState (ProbState (S.singleton Human) (S.singleton Fox) (S.fromList [Chicken, Grain]) R)
vs4 = validState (ProbState (S.fromList [Human, Fox, Chicken, Grain]) S.empty S.empty R)
vs5 = validState (ProbState (S.fromList [Human, Fox]) S.empty (S.fromList [Chicken, Grain]) R)
vs6 = validState (ProbState S.empty (S.fromList [Human, Fox]) (S.fromList [Chicken, Grain]) R)

vs = and [vs1, vs2, vs3, vs4, vs5, vs6]

validStates :: Set ProbState
validStates = S.fromList . filter validState $ validStates' [Human, Fox, Grain, Chicken]
  where
    validStates' :: [Actor] -> [ProbState]
    validStates' []     = [ProbState S.empty S.empty S.empty R]
    validStates' (a:as) =  ((\ps -> ps {leftBank = a `S.insert` leftBank ps}) <$> validStates' as)
                        ++ ((\ps -> ps {rightBank = a `S.insert` rightBank ps}) <$> validStates' as)
                        ++ ((\ps -> ps {boat = a `S.insert` boat ps}) <$> validStates' as)

vss = all validState validStates

-- a possible state
validStateRR :: RR Set ProbState ProbState
validStateRR = mkIrrecoverable
          validStates
          validState

vsNDR = choicesR validStateRR

vsNDR1 = all validState (choicesR validStateRR)
vsNDR2 = not $ ultimateSuccess validStateRR (ProbState S.empty S.empty S.empty R)
vsNDR3 = not $ ultimateSuccess validStateRR (ProbState S.empty (S.fromList [Human, Fox, Chicken, Grain]) S.empty R)
vsNDR4 = not $ ultimateSuccess validStateRR (ProbState (S.singleton Human) (S.singleton Fox) (S.fromList [Chicken, Grain]) R)
vsNDR5 = ultimateSuccess validStateRR (ProbState (S.fromList [Human, Fox, Chicken, Grain]) S.empty S.empty R)
vsNDR6 = ultimateSuccess validStateRR (ProbState (S.fromList [Human, Fox]) S.empty (S.fromList [Chicken, Grain]) R)
vsNDR7 = ultimateSuccess validStateRR (ProbState S.empty (S.fromList [Human, Fox]) (S.fromList [Chicken, Grain]) R)

vsNDRs = and [vsNDR1, vsNDR2, vsNDR3, vsNDR4, vsNDR5, vsNDR6, vsNDR7]

-- valid and reachable
reachableStates :: ProbState -> Set ProbState
reachableStates ps@(ProbState l b r s)
  = S.fromList . filter validState $
      -- move boat
       [ps {boatLocation = row s} | not (null b)]
      -- unload boat (everyone gets off)
    ++ [ps {boat = S.empty, leftBank  = b `S.union` l} | s == L, not (null b)] -- left
    ++ [ps {boat = S.empty, rightBank = b `S.union` r} | s == R, not (null b)] -- right
      -- load boat (just human)
    ++ [ps {boat = S.singleton Human, leftBank  = S.delete Human l} | s == L, Human `S.member` l] -- left
    ++ [ps {boat = S.singleton Human, rightBank = S.delete Human r} | s == R, Human `S.member` r] -- right
      -- load boat (human and a friend)
    ++ [ps {boat = S.fromList [Human, la], leftBank  = S.delete la (S.delete Human l)} | s == L, Human `S.member` l, la <- S.toList l] -- left
    ++ [ps {boat = S.fromList [Human, ra], rightBank = S.delete ra (S.delete Human r)} | s == R, Human `S.member` r, ra <- S.toList r] -- right

rs1 = reachableStates (ProbState (S.fromList [Fox, Grain]) (S.singleton Human) (S.singleton Chicken) L) -- sail or unload human
rs2 = reachableStates (ProbState (S.fromList [Fox, Chicken,Human]) S.empty (S.singleton Grain) L) -- load human with Fox Chicken or alone

reachableStateNDR :: ProbState -> RR Set ProbState ProbState
reachableStateNDR current
  = mkIrrecoverable
      (reachableStates current)
      (`elem` reachableStates current)

-- a safe reachable and valid state
-- safeSide should be okay to not know about setness because safety depends on
-- who is there and not on how many are there, so i think the conversions are fine
-- and that it is not worth burdening safeSide with this extra knowledge that order doesnt matter
safeState :: ProbState -> RR Set ProbState ProbState
safeState current = do
  (ProbState l b r s) <- reachableStateNDR current
  let
    l'f ps
      | l == leftBank ps = Just l
      | otherwise = Nothing
    r'f ps
      | r == rightBank ps = Just r
      | otherwise = Nothing
  l' <- comap l'f (safeSideR (S.size l))
  r' <- comap r'f (safeSideR (S.size r))
  case (l == l', r == r') of
    (True, True) -> return (ProbState l b r s)
    _            -> mzeroR

-- journey gen:
-- (seeing if we can generate step by step the solution path)
-- NOTE:- generates lots of duplicates (used to be permutations caused by the way we create the possibilities in safeSide)
startState = ProbState (S.fromList [Human, Chicken, Grain, Fox]) S.empty S.empty L
j1 = choicesR (safeState startState) -- load boat with human and chicken
j2 = choicesR (safeState (S.findMax j1))  -- cross river or unload
-- focussing on unload (solution) path, so when crossing
j3 = choicesR (safeState (S.findMax j2)) -- cross again, or unload
-- .. seems to be going okay

-- check dir:
-- good move (should be true)
sst1  = ultimateSuccess (safeState startState) (ProbState (S.fromList [Fox,Grain]) (S.fromList [Chicken, Human]) S.empty L) -- true
sst1' = recoveredSuccess (safeState startState) (ProbState (S.fromList [Fox,Grain]) (S.fromList [Chicken, Human]) S.empty L) -- true
-- unsafe (should be false and id expect false, false)
sst2  = ultimateSuccess (safeState startState) (ProbState (S.fromList [Fox, Chicken, Grain]) (S.fromList [Human]) S.empty L) -- false
sst2' = recoveredSuccess (safeState startState) (ProbState (S.fromList [Fox, Chicken, Grain]) (S.fromList [Human]) S.empty L) -- false
-- unreachable (should be false and id expect false true)
sst3  = ultimateSuccess (safeState startState) (ProbState (S.fromList [Fox, Chicken, Grain, Human]) S.empty S.empty R) -- false
sst3' = recoveredSuccess (safeState startState) (ProbState (S.fromList [Fox, Chicken, Grain, Human]) S.empty S.empty R) -- true
-- unreachable and unsafe (should be false and id expect false false)
sst4  = ultimateSuccess (safeState startState) (ProbState (S.fromList [Grain, Human]) S.empty (S.fromList [Fox, Chicken]) R) -- false
sst4' = recoveredSuccess (safeState startState) (ProbState (S.fromList [Grain, Human]) S.empty (S.fromList [Fox, Chicken]) R) -- true

complete :: ProbState -> Bool
complete = (==) endState

endState :: ProbState
endState = ProbState S.empty S.empty (S.fromList [Human, Fox, Chicken, Grain]) R

-- finds the solution to the puzzle with no repeated states
riverCrossingPuzzle :: RR Set [ProbState] [ProbState]
riverCrossingPuzzle = riverCrossingPuzzle' S.empty startState
  where
    riverCrossingPuzzle'
      :: Set ProbState -- states that have been
      -> ProbState   -- current state
      -> RR Set [ProbState] [ProbState]
    riverCrossingPuzzle' ss s = do
      x <- comap headM (safeState s)
      case complete x of
        True -> return [x]
        False -> case x `S.member` (S.insert s ss) of
            True -> mzeroR -- we are not allowing repeated states
            False -> do
              xs <- comap tailM (riverCrossingPuzzle' (S.insert s ss) x)
              return (x:xs)

solution =
              -- lhs                             -- boat                        -- rhs                                 -- side
  [ ProbState (S.fromList [Fox,Grain] )          (S.fromList [Human,Chicken])  (S.fromList [])                         L
  , ProbState (S.fromList [Fox,Grain] )          (S.fromList [Human,Chicken])  (S.fromList [])                         R
  , ProbState (S.fromList [Fox,Grain] )          (S.fromList [])               (S.fromList [Human,Chicken])            R
  , ProbState (S.fromList [Fox,Grain] )          (S.fromList [Human])          (S.fromList [Chicken])                  R
  , ProbState (S.fromList [Fox,Grain] )          (S.fromList [Human])          (S.fromList [Chicken])                  L
  , ProbState (S.fromList [Human,Fox,Grain])     (S.fromList [])               (S.fromList [Chicken])                  L
  , ProbState (S.fromList [Grain])               (S.fromList [Human,Fox])      (S.fromList [Chicken])                  L
  , ProbState (S.fromList [Grain])               (S.fromList [Human,Fox])      (S.fromList [Chicken])                  R
  , ProbState (S.fromList [Grain])               (S.fromList [])               (S.fromList [Human,Fox,Chicken])        R
  , ProbState (S.fromList [Grain])               (S.fromList [Human,Chicken])  (S.fromList [Fox])                      R
  , ProbState (S.fromList [Grain])               (S.fromList [Human,Chicken])  (S.fromList [Fox])                      L
  , ProbState (S.fromList [Human,Chicken,Grain]) (S.fromList [])               (S.fromList [Fox])                      L
  , ProbState (S.fromList [Chicken])             (S.fromList [Human,Grain])    (S.fromList [Fox])                      L
  , ProbState (S.fromList [Chicken])             (S.fromList [Human,Grain])    (S.fromList [Fox])                      R
  , ProbState (S.fromList [Chicken])             (S.fromList [])               (S.fromList [Human,Fox,Grain])          R
  , ProbState (S.fromList [Chicken])             (S.fromList [Human])          (S.fromList [Fox,Grain])                R
  , ProbState (S.fromList [Chicken])             (S.fromList [Human])          (S.fromList [Fox,Grain])                L
  , ProbState (S.fromList [Human,Chicken])       (S.fromList [])               (S.fromList [Fox,Grain])                L
  , ProbState (S.fromList [])                    (S.fromList [Human,Chicken])  (S.fromList [Fox,Grain])                L
  , ProbState (S.fromList [])                    (S.fromList [Human,Chicken])  (S.fromList [Fox,Grain])                R
  , ProbState (S.fromList [])                    (S.fromList [])               (S.fromList [Human,Fox,Chicken,Grain])  R]
solution' =
  [ProbState {leftBank = S.fromList [Fox,Grain], boat = S.fromList [Human,Chicken], rightBank = S.fromList [], boatLocation = L}
  ,ProbState {leftBank = S.fromList [Fox,Grain], boat = S.fromList [Human,Chicken], rightBank = S.fromList [], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Fox,Grain], boat = S.fromList [], rightBank = S.fromList [Human,Chicken], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Fox,Grain], boat = S.fromList [Human], rightBank = S.fromList [Chicken], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Fox,Grain], boat = S.fromList [Human], rightBank = S.fromList [Chicken], boatLocation = L}
  ,ProbState {leftBank = S.fromList [Human,Fox,Grain], boat = S.fromList [], rightBank = S.fromList [Chicken], boatLocation = L}
  ,ProbState {leftBank = S.fromList [Fox], boat = S.fromList [Human,Grain], rightBank = S.fromList [Chicken], boatLocation = L}
  ,ProbState {leftBank = S.fromList [Fox], boat = S.fromList [Human,Grain], rightBank = S.fromList [Chicken], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Fox], boat = S.fromList [], rightBank = S.fromList [Human,Chicken,Grain], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Fox], boat = S.fromList [Human,Chicken], rightBank = S.fromList [Grain], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Fox], boat = S.fromList [Human,Chicken], rightBank = S.fromList [Grain], boatLocation = L}
  ,ProbState {leftBank = S.fromList [Human,Fox,Chicken], boat = S.fromList [], rightBank = S.fromList [Grain], boatLocation = L}
  ,ProbState {leftBank = S.fromList [Chicken], boat = S.fromList [Human,Fox], rightBank = S.fromList [Grain], boatLocation = L}
  ,ProbState {leftBank = S.fromList [Chicken], boat = S.fromList [Human,Fox], rightBank = S.fromList [Grain], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Chicken], boat = S.fromList [], rightBank = S.fromList [Human,Fox,Grain], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Chicken], boat = S.fromList [Human], rightBank = S.fromList [Fox,Grain], boatLocation = R}
  ,ProbState {leftBank = S.fromList [Chicken], boat = S.fromList [Human], rightBank = S.fromList [Fox,Grain], boatLocation = L}
  ,ProbState {leftBank = S.fromList [Human,Chicken], boat = S.fromList [], rightBank = S.fromList [Fox,Grain], boatLocation = L}
  ,ProbState {leftBank = S.fromList [], boat = S.fromList [Human,Chicken], rightBank = S.fromList [Fox,Grain], boatLocation = L}
  ,ProbState {leftBank = S.fromList [], boat = S.fromList [Human,Chicken], rightBank = S.fromList [Fox,Grain], boatLocation = R}
  ,ProbState {leftBank = S.fromList [], boat = S.fromList [], rightBank = S.fromList [Human,Fox,Chicken,Grain], boatLocation = R}]

notSolution =
              -- lhs                             -- boat                        -- rhs                                 -- side
  [ ProbState (S.fromList [Fox,Grain] )          (S.fromList [Human,Chicken])  (S.fromList [])                         L
  , ProbState (S.fromList [Fox,Grain] )          (S.fromList [Human,Chicken])  (S.fromList [])                         R
  -- extra sail
  , ProbState (S.fromList [Fox,Grain] )          (S.fromList [Human,Chicken])  (S.fromList [])                         L
  , ProbState (S.fromList [Fox,Grain] )          (S.fromList [Human,Chicken])  (S.fromList [])                         R]
  ++ drop 2 solution

rc1 = choicesR riverCrossingPuzzle == S.fromList [solution, solution']
-- should be true
rc2 = ultimateSuccess riverCrossingPuzzle solution
rc3 = ultimateSuccess riverCrossingPuzzle solution'
-- should be false
rc4 = ultimateSuccess riverCrossingPuzzle []
rc5 = ultimateSuccess riverCrossingPuzzle [ProbState (S.fromList []) (S.fromList []) (S.fromList [Human,Fox,Chicken,Grain]) R]
rc6 = ultimateSuccess riverCrossingPuzzle (tail solution)
rc7 = ultimateSuccess riverCrossingPuzzle notSolution

rcTests = rc2 && rc3 && not (or [rc4, rc5, rc6, rc7])
