{-# LANGUAGE FlexibleContexts, GADTs, RankNTypes #-}
module Data.Machine.Concurrent.AsyncStep where
import Control.Concurrent.Async.Lifted (Async, async, wait)
import Control.Monad.Trans.Control (MonadBaseControl, StM)
import Data.Machine

type MachineStep m k o = Step k o (MachineT m k o)
type AsyncStep m k o = Async (StM m (MachineStep m k o))

asyncRun :: MonadBaseControl IO m => MachineT m k o -> m (AsyncStep m k o)
asyncRun = async . runMachineT

-- | Satisfy a downstream Await by blocking on an upstream step.
stepAsync :: MonadBaseControl IO m
           => (forall c. k c -> k' c)
           -> AsyncStep m k a'
           -> (a' -> d)
           -> d
           -> d
           -> (AsyncStep m k a' -> d -> MachineT m k' b)
           -> MachineT m k' b
stepAsync sel src f def prev go = MachineT $ wait src >>= \u -> case u of
  Stop -> go' stopped def
  Yield a k -> go' k (f a)
  Await g kg fg -> return $ awaitStep g (sel kg) fg (MachineT . flip go' prev)
  where go' k d = asyncRun k >>= runMachineT . flip go d

-- | @asyncEncased f x@ launches @x@ and provides the resulting
-- 'AsyncStep' to @f@. Turn a function on 'AsyncStep' to a funciton on
-- 'MachineT'.
asyncEncased :: MonadBaseControl IO m
             => (AsyncStep m k1 o1 -> MachineT m k o)
             -> MachineT m k1 o1
             -> MachineT m k o
asyncEncased f x = MachineT $ asyncRun x >>= runMachineT . f

-- | Similar to 'awaitStep', but for continuations that want their inputs
-- to be run asynchronously.
asyncAwait :: MonadBaseControl IO m
           => (a -> MachineT m k o)
           -> k' a
           -> MachineT m k o
           -> (AsyncStep m k o -> MachineT m k1 o1)
           -> m (Step k' b (MachineT m k1 o1))
asyncAwait f sel ff = return . awaitStep f sel ff . asyncEncased
