{-# LANGUAGE GADTs, RankNTypes #-}
-- | In lieu of identifying a single \"best\" @Profunctor@ instance
-- for 'Process'es, we provide profunctor-like tools for performing
-- such operations with additional 'Monoid' constraints. The 'Monoid'
-- instances determine how to combine 'Process'es that yield at
-- different rates. For instance, suppose we have
--
-- @ 
-- p :: Process a b
-- 
-- q :: Process (a,c) (b,c)
-- q = firstP p
-- @
--
-- With arrows or strong profunctors, this operation would feed the
-- first component of any @(a,c)@ input to the arrow or the
-- profunctor, and pass the second component through unchanged. 
--
-- But with machines, if @p@ yields multiple values for every input,
-- then we must decide what to do. If @p@'s output is in the list
-- monoid, then we will yield a list of @b@'s paired with each
-- @c@. Specifically, the list we yield will contain all @b@'s yielded
-- by @p@ subsequent to the @await@ that provided the @c@ and prior to
-- the next time @p@ awaits.
--
-- Similarly, one can use the 'First' monoid to discard values yielded
-- by @p@ after to the first value yielded following a satisfied
-- 'await'. One can use an arithmetic monoid, e.g. 'Sum', to sum all
-- the values @p@ yields in response to an @a@ before it awaits again.
--
-- In this way, we /exhaust/ @p@'s output for any particular input,
-- @a@, and pair all that output with the @c@ that came along with the
-- @a@. The 'Monoid' constraints give us the elasticity to combine
-- machines that yield at different rates relative to their inputs.
module Data.Machine.Profunctor (
  -- * Profunctor-like
  dimapP, lmapP, rmapP,
  
  -- * Strong-like
  firstP, secondP, splitP, fanoutP,

  -- * Choice-like
  leftP, rightP,

  -- * Loop-like
  loopP
  ) where
import Data.Machine.Is
import Data.Machine.Process
import Data.Machine.Type
import Data.Monoid
import Data.Tuple (swap)

-- * Profunctoriality

dimapP :: Monad m => (a -> b) -> (c -> d) -> ProcessT m b c -> ProcessT m a d
dimapP f g m = MachineT $ runMachineT m >>= \v -> case v of
  Stop -> return Stop
  Yield o k -> return . Yield (g o) $ dimapP f g k
  Await h Refl hh ->
    return $ awaitStep (h . f) Refl hh $ dimapP f g

lmapP :: Monad m => (a -> b) -> ProcessT m b c -> ProcessT m a c
lmapP f = dimapP f id

rmapP :: Monad m => (b -> c) -> ProcessT m a b -> ProcessT m a c
rmapP g = dimapP id g

-- Consecutive yields are folded into a single yield.
-- foldYields :: (Monad m, Monoid a) => MachineT m k a -> MachineT m k a
-- foldYields m = MachineT $ runMachineT m >>= go Nothing
--   where go Nothing Stop = return Stop
--         go (Just acc) Stop = return $ Yield acc stopped
--         go acc (Yield o k) = runMachineT k >>= go (acc <> Just o)
--         go Nothing awStep = runMachineT . foldYields $ encased awStep
--         go (Just acc) awStep = return $ Yield acc (foldYields $ encased awStep)

-- * Strength-like

-- Each @c@ induces a new epoch in the first components. The first
-- step is vaguer: in @firstP p@, if @p@ yields before ever awaiting,
-- those yields are monoidally combined with the yields after the
-- first @await@. Subsequent @yields@ are monoidally combined with the
-- second component associated with the value that precipitated the
-- @yields@. Thus each yielded pair @(b,c)@ contains a @b@ that was
-- yielded after the await that produced @c@.

-- | Send the first component of the input through the argument
-- process. Copy the rest unchanged to the output.
firstP :: (Monad m, Monoid b) => ProcessT m a b -> ProcessT m (a,c) (b,c)
firstP = MachineT . go0 Nothing -- . foldYields
  where go0 :: (Monad m , Monoid b)
            => Maybe b -> ProcessT m a b
            -> m (Step (Is (a,c)) (b,c) (ProcessT m (a,c) (b,c)))
        go0 acc m = runMachineT m >>= \v -> case v of
          Stop -> case acc of
                    Nothing -> return Stop
                    Just acc' -> return $
                      Await (\(_,c) -> encased $ Yield (acc',c) stopped)
                            Refl
                            stopped
          Yield o k -> go0 (acc <> Just o) k
          Await f Refl ff -> 
            return $ Await (\(a,c) -> MachineT $ go1 acc c (f a))
                           Refl
                           (firstP ff)
        go1 :: (Monad m , Monoid b)
            => Maybe b -> c -> ProcessT m a b
            -> m (Step (Is (a,c)) (b,c) (ProcessT m (a,c) (b,c)))
        go1 Nothing latch m = runMachineT m >>= \v -> case v of
          Stop -> return Stop
          Yield o k -> go1 (Just o) latch k
          Await f Refl ff -> return $
            Await (\(a,c) -> MachineT $ go1 Nothing c (f a))
                  Refl
                  (MachineT $ go0 Nothing ff)
        go1 (Just acc) latch m = runMachineT m >>= \v -> case v of
          Stop -> undefined
          Yield o k -> go1 (Just (acc <> o)) latch k
          Await f Refl ff -> return $
            Yield (acc,latch) 
                  (encased $ Await (\(a,c) -> MachineT $ go1 mempty c (f a))
                                   Refl
                                   (MachineT $ go0 mempty ff))

-- | Send the second component of the input through the argument
-- process. Copy the rest unchanged to the output.
secondP :: (Monad m, Monoid b) => ProcessT m a b -> ProcessT m (c,a) (c,b)
secondP = dimapP swap swap . firstP

-- | Similar to 'Control.Arrow.***': splits the input between two
-- processes and combines their output.
splitP :: (Monad m, Monoid b, Monoid b')
       => ProcessT m a b -> ProcessT m a' b' -> ProcessT m (a,a') (b,b')
splitP ma0 mb0 = MachineT $ go0 Nothing Nothing ma0 mb0
  where go0 :: (Monad m, Monoid b, Monoid b')
            => Maybe b -> Maybe b'
            -> ProcessT m a b -> ProcessT m a' b'
            -> m (Step (Is (a,a')) (b,b') (ProcessT m (a,a') (b,b')))
        go0 accL accR ma mb = runMachineT ma >>= \u -> case u of
          Stop -> case accL of 
                    Nothing -> return Stop
                    _ -> go1 accL accR (const stopped) stopped mb
          Yield o k -> go0 (accL <> Just o) accR k mb
          Await f Refl ff -> go1 accL accR f ff mb
        go1 :: (Monad m, Monoid b, Monoid b')
            => Maybe b -> Maybe b'
            -> (a -> ProcessT m a b) -> ProcessT m a b
            -> ProcessT m a' b'
            -> m (Step (Is (a,a')) (b,b') (ProcessT m (a,a') (b,b')))  
        go1 accL accR f ff m = runMachineT m >>= \u -> case u of
          Stop -> case accR of
                    Nothing -> return Stop
                    _ -> go2 accL accR f ff (const stopped) stopped
          Yield o k -> go1 accL (accR <> Just o) f ff k
          Await g Refl gg -> go2 accL accR f ff g gg
        go2 :: (Monad m, Monoid b, Monoid b')
            => Maybe b -> Maybe b'
            -> (a -> ProcessT m a b) -> ProcessT m a b
            -> (a' -> ProcessT m a' b') -> ProcessT m a' b'
            -> m (Step (Is (a,a')) (b,b') (ProcessT m (a,a') (b,b')))  
        go2 (Just accL) (Just accR) f ff g gg =
          return . Yield (accL,accR) . encased $
          Await (\(x,y) -> MachineT $ go0 Nothing Nothing (f x) (g y))
                Refl
                (MachineT $ go0 (Just accL) (Just accR) ff gg)
        go2 accL accR f ff g gg = return $
          Await (\(x,y) -> MachineT $ go0 accL accR (f x) (g y))
                Refl
                (MachineT $ go0 accL accR ff gg)

-- | Similar to 'Control.Arrow.&&&': sends the input to both argument
-- processes and combines their outputs.
fanoutP :: (Monad m, Monoid b, Monoid b')
        => ProcessT m a b -> ProcessT m a b' -> ProcessT m a (b,b')
fanoutP ma0 mb0 = MachineT $ go1 Nothing Nothing ma0 mb0
  where go1 :: (Monad m, Monoid b, Monoid b')
            => Maybe b -> Maybe b'
            -> ProcessT m a b -> ProcessT m a b'
            -> m (Step (Is a) (b,b') (ProcessT m a (b,b')))
        go1 accL accR ma mb = runMachineT ma >>= \v -> case v of
          Stop -> case accL of
                    Nothing -> return Stop
                    _ -> go2 accL accR (const stopped) stopped mb
          Yield o k -> go1 (accL <> Just o) accR k mb
          Await f Refl ff -> go2 accL accR f ff mb
        go2 :: (Monad m, Monoid b, Monoid b')
            => Maybe b -> Maybe b'
            -> (a -> ProcessT m a b) -> ProcessT m a b
            -> ProcessT m a b'
            -> m (Step (Is a) (b,b') (ProcessT m a (b,b')))
        go2 accL accR f ff mb = runMachineT mb >>= \v -> case v of
          Stop -> case accR of
                    Nothing -> return Stop
                    _ -> goB accL accR f ff (const stopped) stopped
          Yield o k -> go2 accL (accR <> Just o) f ff k
          Await g Refl gg -> goB accL accR f ff g gg
        goB :: (Monad m, Monoid b, Monoid b')
            => Maybe b -> Maybe b'
            -> (a -> ProcessT m a b) -> ProcessT m a b
            -> (a -> ProcessT m a b') -> ProcessT m a b'
            -> m (Step (Is a) (b,b') (ProcessT m a (b,b')))
        goB (Just accL) (Just accR) f ff g gg =
          return . Yield (accL,accR) . encased $
          Await (\x -> fanoutP (f x) (g x))
                Refl
                (fanoutP ff gg)
        goB accL accR f ff g gg = return $
          Await (\x -> MachineT $ go1 accL accR (f x) (g x))
                Refl
                (MachineT $ go1 accL accR ff gg)

-- * Choice-like

-- | Feed 'Left'-tagged inputs to the argument process, passing the
-- rest through unchanged to the output.
leftP :: Monad m => ProcessT m a b -> ProcessT m (Either a c) (Either b c)
leftP m = MachineT $ runMachineT m >>= \v -> case v of
  Stop -> return Stop
  Yield o k -> return $ Yield (Left o) (leftP k)
  Await f Refl ff -> return $
    Await (\u -> case u of
                   Left x -> leftP (f x)
                   Right y -> encased $ Yield (Right y) (leftP $ encased v))
          Refl
          (leftP ff)

-- | Feed 'Right'-tagged inputs to the argument process, passing the
-- rest through unchagned to the output.
rightP :: Monad m => ProcessT m a b -> ProcessT m (Either c a) (Either c b)
rightP m = MachineT $ runMachineT m >>= \v -> case v of
  Stop -> return Stop
  Yield o k -> return $ Yield (Right o) (rightP k)
  Await f Refl ff -> return $
    Await (\u -> case u of
                   Left x -> encased $ Yield (Left x) (rightP $ encased v)
                   Right y -> rightP (f y))
          Refl
          (rightP ff)

-- | Feed an output back as an input. Requires a seed value to get
-- things started.
loopP :: Monad m => c -> ProcessT m (a,c) (b,c) -> ProcessT m a b
loopP z m = MachineT $ runMachineT m >>= \v -> case v of
  Stop -> return Stop
  Yield (o,z') k -> return . Yield o $ loopP z' k
  Await f Refl ff -> return $
    Await (\x -> loopP z (f (x,z)))
          Refl
          (loopP z ff)
