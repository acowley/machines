{-# LANGUAGE FlexibleContexts, GADTs, TupleSections #-}
module Data.Machine.Concurrent.Scatter (scatter) where
import Control.Concurrent.Async (Async, waitAny)
import Control.Monad ((>=>))
import Control.Monad.Base (liftBase)
import Control.Monad.Trans.Control (MonadBaseControl, restoreM, StM)
import Data.Machine
import Data.Machine.Concurrent.AsyncStep

holes :: [a] -> [[a]]
holes = go id
  where go _ [] = []
        go x (y:ys) = x ys : go (x . (y:)) ys

diff :: [a] -> [(a,[a])]
diff xs = zip xs (holes xs)

waitAnyHole :: MonadBaseControl IO m => [(Async (StM m a), [b])] -> m (a, [b])
waitAnyHole xs = do (_,(s,b)) <- liftBase $ waitAny xs'
                    fmap (,b) (restoreM s)
  where xs' = map (\(a,b) -> fmap (,b) a) xs

-- | Produces values from whichever source 'MachineT' yields
-- first. This operation may also be viewed as a /gather/ operation in
-- that all values produced by the given machines are interleaved when
-- fed downstream.
--
-- Some examples of more specific useful types @scatter@ may be used
-- at,
-- 
-- @
-- scatter :: [ProcessT m a b] -> ProcessT m a b
-- scatter :: [SourceT m a] -> SourceT m a
-- @
--
-- The former may be used to stream data through a collection of
-- worker 'Process'es, the latter may be used to intersperse values
-- from a collection of sources.
scatter :: MonadBaseControl IO m => [MachineT m k o] -> MachineT m k o
scatter [] = stopped
scatter sinks = MachineT $ mapM asyncRun sinks
                 >>= waitAnyHole . diff
                 >>= uncurry go
  where go :: MonadBaseControl IO m
           => MachineStep m k o
           -> [AsyncStep m k o]
           -> m (MachineStep m k o)
        go Stop [] = return Stop
        go Stop sinks' = waitAnyHole (diff sinks') >>= uncurry go
        go (Yield o k) sinks' = 
          asyncRun k >>= return . Yield o . MachineT . goWait . (:sinks')
        go (Await f fk ff) sinks' =
          asyncAwait f fk ff (MachineT . goWait . (:sinks'))
        goWait :: MonadBaseControl IO m
               => [AsyncStep m k o]
               -> m (MachineStep m k o)
        goWait = waitAnyHole . diff >=> uncurry go
