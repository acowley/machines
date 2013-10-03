{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Machine.Type
-- Copyright   :  (C) 2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  rank-2, GADTs
--
----------------------------------------------------------------------------
module Data.Machine.Type
  (
  -- * Machines
    MachineT(..)
  , Step(..)
  , Machine
  , runT_
  , runT
  , run
  , runMachine
  , encased
  , awaitStep

  -- ** Building machines from plans
  , construct
  , repeatedly
  , before
--  , sink

  -- * Reshaping machines
  , fit
  , pass

  , stopped

  -- * Applicative Machines
  , Appliance(..)
  ) where

import Control.Applicative
import Control.Category
import Control.Monad (liftM)
import Data.Foldable
import Data.Functor.Identity
import Data.Machine.Plan
import Data.Monoid
import Data.Pointed
import Prelude hiding ((.),id)

-------------------------------------------------------------------------------
-- Transduction Machines
-------------------------------------------------------------------------------

-- | This is the base functor for a 'Machine' or 'MachineT'.
--
-- Note: A 'Machine' is usually constructed from 'Plan', so it does not need to be CPS'd.
data Step k o r
  = Stop
  | Yield o r
  | forall t. Await (t -> r) (k t) r

instance Functor (Step k o) where
  fmap _ Stop = Stop
  fmap f (Yield o k) = Yield o (f k)
  fmap f (Await g kg fg) = Await (f . g) kg (f fg)

-- | A 'MachineT' reads from a number of inputs and may yield results before stopping
-- with monadic side-effects.
newtype MachineT m k o = MachineT { runMachineT :: m (Step k o (MachineT m k o)) }

-- | A 'Machine' reads from a number of inputs and may yield results before stopping.
--
-- A 'Machine' can be used as a @'MachineT' m@ for any @'Monad' m@.
type Machine k o = forall m. Monad m => MachineT m k o

-- | @'runMachine' = 'runIdentity' . 'runMachineT'@
runMachine :: MachineT Identity k o -> Step k o (MachineT Identity k o)
runMachine = runIdentity . runMachineT

-- | Pack a 'Step' of a 'Machine' into a 'Machine'.
encased :: Monad m => Step k o (MachineT m k o) -> MachineT m k o
encased = MachineT . return

-- | Build an 'Await' step given a continuation that provides
-- subsequent steps. @awaitStep f sel ff k@ is like applying the
-- 'Await' constructor directly, but the continuation @k@ is used to
-- continue the machine. 
-- 
-- @awaitStep f sel ff k = Await (k . f) sel (k ff)@
awaitStep :: (a -> d) -> k' a -> d -> (d -> r) -> Step k' b r
awaitStep f sel ff k = Await (k . f) sel (k ff)

instance Monad m => Functor (MachineT m k) where
  fmap f (MachineT m) = MachineT (liftM f' m) where
    f' (Yield o xs)    = Yield (f o) (f <$> xs)
    f' (Await k kir e) = Await (fmap f . k) kir (f <$> e)
    f' Stop            = Stop

instance Monad m => Pointed (MachineT m k) where
  point = repeatedly . yield

-- | An input type that supports merging requests from multiple machines.
class Appliance k where
  applied :: Monad m => MachineT m k (a -> b) -> MachineT m k a -> MachineT m k b

instance (Monad m, Appliance k) => Applicative (MachineT m k) where
  pure = point
  (<*>) = applied

instance Monad m => Monoid (MachineT m k o) where
  mempty = stopped
  ma `mappend` mb = MachineT $ runMachineT ma >>= \u -> case u of
    Stop -> runMachineT mb
    Yield o k -> return . Yield o $ k <> mb
    Await f fk ff -> return $ Await ((<> mb) . f) fk (ff <> mb)

{-
-- TODO

instance Appliance (Is i) where
  applied = appliedTo (Just mempty) (Just mempty) id (flip id) where

-- applied
appliedTo
  :: Maybe (Seq i)
  -> Maybe (i -> MachineT m (Is i) b, MachineT m (Is i) b)
  -> Either (Seq a) (Seq b)
  -> (a -> b -> c)
  -> (b -> a -> c)
  -> MachineT m (Is i) a
  -> MachineT m (Is i) b
  -> MachineT m (Is i) c
appliedTo mis blocking ss f g m n = MachineT $ runMachineT m >>= \v -> case v of
  Stop -> return Stop
  Yield a k -> case ss of
    Left as ->
    Right bs -> case viewl bs of
      b :< bs' -> return $ Yield (f a b) (appliedTo mis bs' f g m n)
      EmptyL   -> runMachine $ appliedTo mis blocking (singleton a) g f n m
  Await ak Refl e -> case mis of
    Nothing -> runMachine $ appliedTo Nothing blocking bs f g e n
    Just is -> case viewl is of
      i :< is' -> runMachine $ appliedTo (Just is') blocking bs f g (ak i) m
      EmptyL -> case blocking of
        Just (bk, be) ->
        Nothing -> runMachine $ appliedTo mis (Just (ak, e))
        | blocking  -> return $ Await (\i -> appliedTo (Just (singleton i)) False f g (ak i) n) Refl $
        | otherwise ->
-}

-- | Stop feeding input into model, taking only the effects.
runT_ :: Monad m => MachineT m k b -> m ()
runT_ m = runMachineT m >>= \v -> case v of
  Stop        -> return ()
  Yield _ k   -> runT_ k
  Await _ _ e -> runT_ e

-- | Stop feeding input into model and extract an answer
runT :: Monad m => MachineT m k b -> m [b]
runT (MachineT m) = m >>= \v -> case v of
  Stop        -> return []
  Yield o k   -> liftM (o:) (runT k)
  Await _ _ e -> runT e

-- | Run a pure machine and extract an answer.
run :: MachineT Identity k b -> [b]
run = runIdentity . runT

-- | This permits toList to be used on a Machine.
instance (m ~ Identity) => Foldable (MachineT m k) where
  foldMap f (MachineT (Identity m)) = go m where
    go Stop = mempty
    go (Yield o k) = f o `mappend` foldMap f k
    go (Await _ _ fg) = foldMap f fg

-- |
-- Connect different kinds of machines.
--
-- @'fit' 'id' = 'id'@
fit :: Monad m => (forall a. k a -> k' a) -> MachineT m k o -> MachineT m k' o
fit f (MachineT m) = MachineT (liftM f' m) where
  f' (Yield o k)     = Yield o (fit f k)
  f' Stop            = Stop
  f' (Await g kir h) = Await (fit f . g) (f kir) (fit f h)

-- | Compile a machine to a model.
construct :: Monad m => PlanT k o m a -> MachineT m k o
construct m = MachineT $ runPlanT m
  (const (return Stop))
  (\o k -> return (Yield o (MachineT k)))
  (\f k g -> return (Await (MachineT . f) k (MachineT g)))
  (return Stop)

-- | Generates a model that runs a machine until it stops, then start it up again.
--
-- @'repeatedly' m = 'construct' ('Control.Monad.forever' m)@
repeatedly :: Monad m => PlanT k o m a -> MachineT m k o
repeatedly m = r where
  r = MachineT $ runPlanT m
    (const (runMachineT r))
    (\o k -> return (Yield o (MachineT k)))
    (\f k g -> return (Await (MachineT . f) k (MachineT g)))
    (return Stop)

-- | @before m p@ builds and evaluates a machine based on @p@ until it
-- stops, then yields answers according to @m@.
before :: Monad m => MachineT m k o -> PlanT k o m a -> MachineT m k o
before (MachineT n) m = MachineT $ runPlanT m
  (const n)
  (\o k -> return (Yield o (MachineT k)))
  (\f k g -> return (Await (MachineT . f) k (MachineT g)))
  (return Stop)

-- | Given a handle, ignore all other inputs and just stream input from that handle.
--
-- @
-- 'pass' 'id' :: 'Data.Machine.Process.Process' a a
-- 'pass' 'Data.Machine.Tee.L'  :: 'Data.Machine.Tee.Tee' a b a
-- 'pass' 'Data.Machine.Tee.R'  :: 'Data.Machine.Tee.Tee' a b b
-- 'pass' 'Data.Machine.Wye.X'  :: 'Data.Machine.Wye.Wye' a b a
-- 'pass' 'Data.Machine.Wye.Y'  :: 'Data.Machine.Wye.Wye' a b b
-- 'pass' 'Data.Machine.Wye.Z'  :: 'Data.Machine.Wye.Wye' a b (Either a b)
-- @
pass :: k o -> Machine k o
pass k = repeatedly $ do
  a <- awaits k
  yield a

-- | This is a stopped 'Machine'
stopped :: Machine k b
stopped = encased Stop

-------------------------------------------------------------------------------
-- Sink
-------------------------------------------------------------------------------

{-
-- |
-- A Sink in this model is a 'Data.Machine.Process.Process'
-- (or 'Data.Machine.Tee.Tee', etc) that produces a single answer.
--
-- \"Is that your final answer?\"
sink :: Monad m => (forall o. PlanT k o m a) -> MachineT m k a
sink m = runPlanT m (\a -> Yield a Stop) id (Await id) Stop
-}
