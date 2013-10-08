{-# LANGUAGE FlexibleContexts, GADTs, TupleSections #-}
-- | Routing for splitting and merging processing pipelines.
module Data.Machine.Concurrent.Scatter (scatter, splitEnds) where
import Control.Concurrent.Async (Async, waitAny)
import Control.Concurrent.Async.Lifted (waitEither, wait)
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

-- | Connect two processes to the downstream tails of a 'Machine' that
-- produces 'Either's. The two downstream consumers are run
-- concurrently when possible. When one downstream consumer stops, the
-- other is allowed to run until it stops or the upstream source
-- yields a value the remaining consumer can not handle.
--
-- @splitEnds source sinkL sinkR@ produces a topology like this,
--
-- @
--                                 sinkL
--                                /      \
--                              a          \
--                             /            \
--    source -- Either a b -->                -- r -->
--                             \            /
--                               b         /
--                                \      /
--                                 sinkR 
-- @
splitEnds :: MonadBaseControl IO m
          => MachineT m k (Either a b)
          -> ProcessT m a r -> ProcessT m b r
          -> MachineT m k r
splitEnds m snkL snkR = MachineT $ do al <- asyncRun snkL
                                      ar <- asyncRun snkR
                                      go m al ar
  where go src al ar = waitEither al ar >>= go' src al ar
        go' src al ar step = case step of
          Left Stop -> wait ar >>= runMachineT . rightOnly src . encased
          Right Stop -> wait al >>= runMachineT . leftOnly src . encased

          Left (Yield o k) -> 
            return . Yield o . MachineT $ asyncRun k >>= flip (go src) ar
          Right (Yield o k) ->
            return . Yield o . MachineT $ asyncRun k >>= go src al

          Left (Await f Refl ff) -> runMachineT src >>= \u -> case u of
            Stop -> asyncRun ff >>= flip (go stopped) ar
            Yield (Left x) k -> asyncRun (f x) >>= flip (go k) ar
            Yield (Right _) _ -> wait ar >>= go' (encased u) al ar . Right
            Await uf uk uu -> 
              return $ awaitStep uf uk uu (\s -> MachineT $ go s al ar)
          Right (Await g Refl gg) -> runMachineT src >>= \u -> case u of
            Stop -> asyncRun gg >>= go stopped al
            Yield (Left _) _ -> wait al >>= go' (encased u) al ar . Left
            Yield (Right y) k -> asyncRun (g y) >>= go k al
            Await uf uk uu ->
              return $ awaitStep uf uk uu (\s -> MachineT $ go s al ar)

-- | We have a sink for the Left output of a source, so we want to
-- keep running it as long as upstream does not yield a Right which we
-- can not handle.
leftOnly :: Monad m
         => MachineT m k (Either a b)
         -> ProcessT m a r
         -> MachineT m k r
leftOnly src snk = MachineT $ runMachineT snk >>= \v -> case v of
  Stop -> return Stop
  Yield o k -> return . Yield o $ leftOnly src k
  Await f Refl ff -> runMachineT src >>= \u -> case u of
    Stop -> runMachineT $ leftOnly stopped ff
    Yield (Left x) k -> runMachineT $ leftOnly k (f x)
    Yield (Right _) _ -> runMachineT $ leftOnly (encased u) ff
    Await uf uk uu -> 
      return $ awaitStep uf uk uu (flip leftOnly (encased v))

-- | We have a sink for the Right output of a source, so we want to
-- keep running it as long as upstream does not yield a Left which we
-- can not handle.
rightOnly :: Monad m
          => MachineT m k (Either a b)
          -> ProcessT m b r
          -> MachineT m k r
rightOnly src snk = MachineT $ runMachineT snk >>= \v -> case v of
  Stop -> return Stop
  Yield o k -> return . Yield o $ rightOnly src k
  Await g Refl gg -> runMachineT src >>= \u -> case u of
    Stop -> runMachineT $ rightOnly stopped gg
    Yield (Left _) _ -> runMachineT $ rightOnly (encased u) gg
    Yield (Right y) k -> runMachineT $ rightOnly k (g y)
    Await uf uk uu ->
      return $ awaitStep uf uk uu (flip rightOnly (encased v))
