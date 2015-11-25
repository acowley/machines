{-# LANGUAGE GADTs #-}
-- | Provide a notion of fanout wherein a single input is passed to
-- several consumers.
module Data.Machine.Fanout (fanout, fanoutSteps) where
import Control.Applicative
import Control.Arrow
import Control.Monad (foldM, (<=<))
import Data.Machine
import Data.Maybe (catMaybes, maybeToList)
import Data.Monoid
import Data.Profunctor.Unsafe ((#.))
import Data.Semigroup (Semigroup(sconcat))
import Data.List.NonEmpty (NonEmpty((:|)))
import Prelude

-- | Feed a value to a 'ProcessT' at an 'Await' 'Step'. If the
-- 'ProcessT' is awaiting a value, then its next step is
-- returned. Otherwise, the original process is returned.
feed :: Monad m => a -> ProcessT m a b -> m (Step (Is a) b (ProcessT m a b))
feed x m = runMachineT m >>= \v ->
            case v of
              Await f Refl _ -> runMachineT (f x)
              s -> return s

-- | Like 'Data.List.mapAccumL' but with a monadic accumulating
-- function.
mapAccumLM :: (Functor m, Monad m)
           => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM f z = fmap (second ($ [])) . foldM aux (z,id)
  where aux (acc,ys) x = second ((. ys) . (:)) <$> f acc x

-- | Exhaust a sequence of all successive 'Yield' steps taken by a
-- 'MachineT'. Returns the list of yielded values and the next
-- (non-Yield) step of the machine.
flushYields :: Monad m
            => Step k o (MachineT m k o) -> m ([o], Maybe (MachineT m k o))
flushYields = go id
  where go rs (Yield o s) = runMachineT s >>= go ((o:) . rs)
        go rs Stop = return (rs [], Nothing)
        go rs s = return (rs [], Just $ encased s)

-- Helper for 'fanout' that produces the 'Await' to be shared by every
-- process.
fanoutGo :: (Functor m, Monad m, Semigroup r)
         => [ProcessT m a r] -> ProcessT m a r
fanoutGo [] = encased Stop
fanoutGo xs = encased $ Await (MachineT #. aux) Refl (encased Stop)
  where aux y = do (rs,xs') <- mapM (feed y) xs >>= mapAccumLM yields []
                   let nxt = fanoutGo $ catMaybes xs'
                   case rs of
                     [] -> runMachineT nxt
                     (r:rs') -> return $ Yield (sconcat $ r :| rs') nxt
        yields rs Stop = return (rs,Nothing)
        yields rs y@Yield{} = first (++ rs) <$> flushYields y
        yields rs a@Await{} = return (rs, Just $ encased a)

-- | Flushes all the ready-to-go 'Yield's from each of a list of
-- 'MachineT's. Returns all the available outputs and all the machines
-- that are yet to stop.
flushAll :: (Functor m, Monad m) => [MachineT m k o] -> m ([o], [MachineT m k o])
flushAll = fmap concatFlushes . mapM (flushYields <=< runMachineT)
  where concatFlushes = mconcat . map (fmap maybeToList)

-- | Share inputs with each of a list of processes in lockstep. Any
-- values yielded by the processes are combined into a single yield
-- from the composite process.
fanout :: (Monad m, Semigroup r) => [ProcessT m a r] -> ProcessT m a r
fanout = MachineT . (aux <=< flushAll)
  where aux ([], procs) = runMachineT $ fanoutGo procs
        aux (o:os, procs) = return $ Yield (sconcat $ o :| os) (fanoutGo procs)

-- Helper for 'fanoutSteps'
fanoutStepsGo :: (Functor m, Monad m, Monoid r)
              => [ProcessT m a r] -> ProcessT m a r
fanoutStepsGo [] = encased Stop
fanoutStepsGo xs = encased $ Await (MachineT . aux) Refl (encased Stop)
  where aux y = do (rs,xs') <- mapM (feed y) xs >>= mapAccumLM yields []
                   let nxt = fanoutStepsGo $ catMaybes xs'
                   if null rs
                   then return $ Yield mempty nxt
                   else return $ Yield (mconcat rs) nxt
        yields rs Stop = return (rs,Nothing)
        yields rs y@Yield{} = first (++rs) <$> flushYields y
        yields rs a@Await{} = return (rs, Just $ encased a)

-- | Share inputs with each of a list of processes in lockstep. If
-- none of the processes yields a value, the composite process will
-- itself yield 'mempty'. The idea is to provide a handle on steps
-- only executed for their side effects. For instance, if you want to
-- run a collection of 'ProcessT's that await but don't yield some
-- number of times, you can use 'fanOutSteps . map (fmap (const ()))'
-- followed by a 'taking' process.
fanoutSteps :: (Functor m, Monad m, Monoid r)
            => [ProcessT m a r] -> ProcessT m a r
fanoutSteps = MachineT . (aux <=< flushAll)
  where aux ([], procs) = runMachineT $ fanoutStepsGo procs
        aux (os@(_:_), procs) = return
                              $ Yield (mconcat os) (fanoutStepsGo procs)
