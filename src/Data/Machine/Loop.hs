{-# LANGUAGE GADTs, RankNTypes #-}
-- | A loop construct wherein a process with two inputs and two
-- outputs has one output wired back into an input via an intermediate
-- process. See 'loop' for information.
module Data.Machine.Loop (Loop(..), Looped, LoopedT, loop, (~@),
                          request, upstream, feedbackLoop, foldLoop) where
import Control.Monad ((>=>))
import Data.Machine

-- | The input descriptor for a 'Looped' or 'LoopedT'. The type @Loop
-- a b c@ drives a process that can accept values of type @c@ from
-- upstream, or issue requests of type @a@ to a feedback loop that
-- responds with values of type @b@.
data Loop a b c d where
  Request  :: a -> Loop a b c b
  Upstream :: Loop a b c c

-- | Make a request of a looped-in source.
request :: a -> Plan (Loop a b c) d b
request = awaits . Request

-- | Await a value from an upstream source.
upstream :: Plan (Loop a b c) d c
upstream = awaits Upstream

-- | A 'Machine' that can read from an upstream source or make
-- requests of a 'Process' tied into a feedback loop.
type Looped a b c d = Machine (Loop a b c) d

-- | A 'MachineT' that can read from an upstream source or make
-- requests of a 'ProcessT' tied into a feedback loop.
type LoopedT m a b c d = MachineT m (Loop a b c) d

-- | Repeatedly feed a value to a process until it yields or stops.
feedRep :: Monad m => a -> ProcessT m a b -> m (Maybe (b, ProcessT m a b))
feedRep x = runMachineT >=> go
  where go Stop = return Nothing
        go (Await g Refl _) = runMachineT (g x) >>= go
        go (Yield o k) = return $ Just (o, k)

-- | Operator syntax for 'loop'.
(~@) :: Monad m => ProcessT m a b -> LoopedT m a b c d -> ProcessT m c d
(~@) = loop
infixl 8 ~@

-- | @loop feedback sink@ feeds upstream values into @sink@ while
-- allowing @sink@ to make requests of @feedback@ whose output is
-- routed back into @sink@.
-- 
-- @
--            |----feedback <-----|
--            |                   |
--            |     |--------|    |
--            |-->  |  sink  |----|
--  upstream ---->  |        |------> downstream
--                  |--------|
-- @
loop :: Monad m => ProcessT m a b -> LoopedT m a b c d -> ProcessT m c d
loop feedback snk = MachineT $ runMachineT snk >>= \d -> case d of
  Stop -> return Stop
  Yield o k -> return $ Yield o (loop feedback k)
  Await f (Request x) ff -> feedRep x feedback >>= \u -> case u of
    Nothing -> runMachineT $ loop stopped ff
    Just (o, k) -> runMachineT $ loop k (f o)
  Await f Upstream ff -> return $ awaitStep f Refl ff (loop feedback)

-- | Run a process whose yielded 'Left' values are converted into
-- 'Requests' in a 'Looped' that result in switching to a new process,
-- and whose 'Right' values are yielded.
feedbackLoop :: Monad m
             => ProcessT m a (Either s b)
             -> LoopedT m s (ProcessT m a (Either s b)) a b
feedbackLoop p = MachineT $ runMachineT p >>= \u -> case u of
  Stop -> return Stop
  Yield (Left s) _ -> return $ Await feedbackLoop (Request s) stopped
  Yield (Right o) k -> return . Yield o $ feedbackLoop k
  Await f Refl ff -> return $ Await (feedbackLoop . f) Upstream (feedbackLoop ff)

-- | Fold a 'ProcessT' that generates handler processes from a seed
-- value over an input stream. A seed value is used to produce a
-- process that handles some amount of input before yielding a
-- 'Left'-tagged new seed that is used to produce a new consumer.
foldLoop :: Monad m => ProcessT m s (ProcessT m a (Either s b)) -> s -> ProcessT m a b
foldLoop f z = f ~@ (encased $ Await feedbackLoop (Request z) stopped)
