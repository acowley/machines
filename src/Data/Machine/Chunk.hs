{-# LANGUAGE GADTs, RankNTypes #-}
-- | Working with user-defined chunks of input.
module Data.Machine.Chunk 
  ( -- * Breaking into chunks
    chunk, chunked, oneChunk,
    -- * Common chunks
    listChunk,
    -- * Folding over chunks
    foldChunks,
    -- * Auxiliary functions
    drainedLeft, drainCap, loopUnread
  ) where
import Control.Applicative
import Data.List (findIndex)
import qualified Data.Foldable as F
import Data.Machine
import Data.Machine.Loop
import Data.Machine.Unread
import Data.Traversable (traverse)

-- | Break an input stream into chunk streams on the boundaries
-- indicated by the given function which returns a prefix of elements
-- before a break, and a suffix of elements after a break. Every
-- prefix is passed to a 'ProcessT' until it yields a 'Left', at which
-- point the current chunk is drained, and the 'Left' value is used as
-- a seed by the looped-in 'ProcessT' to create a new 'ProcessT' to
-- handle the next chunk.
foldChunks :: Monad m
           => (a -> (a', Maybe a))
           -> ProcessT m s (ProcessT m a' (Either s b))
           -> s
           -> ProcessT m a b
foldChunks br f z = f ~@ loopUnread br z

-- | Fuses chunking, unread buffers, and looped processes.
loopUnread :: Monad m
           => (a -> (a', Maybe a))
           -> s
           -> LoopedT m s (ProcessT m a' (Either s b)) a b
loopUnread br s = encased $ Await go (Request s) stopped
  where go ma = unreadableSwitchTo prependLoop
                                   (\Refl -> Upstream)
                                   (stitch <$> oneChunk br ~> drainedLeft ma)
        stitch (Left s') = Left $ loopUnread br s'
        stitch (Right x) = Right x

-- | Send the elements of a 'F.Foldable' to a downstream 'LoopedT'.
prependLoop :: (Monad m, F.Foldable t)
            => t c -> LoopedT m a b c d -> LoopedT m a b c d
prependLoop xs' = go $ F.toList xs'
  where go [] m = m
        go q@(x:xs) m = MachineT $ runMachineT m >>= \u -> case u of
          Stop -> return Stop
          Yield o k -> return . Yield o $ prependLoop q k
          Await f Upstream _ -> runMachineT $ prependLoop xs (f x)
          Await f r ff -> 
            return $ Await (prependLoop q . f) r (prependLoop q ff)

-- | Use a predicate to divide a list into a prefix of elements that
-- do not satisfy the predicate, and a suffix that starts with a
-- satisfying element.
listChunk :: (a -> Bool) -> [a] -> ([a], Maybe [a])
listChunk f xs = case findIndex f xs of
                   Nothing -> (xs, Nothing)
                   Just i -> (take i xs, Just $ drop i xs)

-- | Drain upstream then yield the given value.
drainCap :: b -> Process a b
drainCap r = construct go
  where go = (await >> go) <|> yield r

-- | The first 'Left' yielded drains upstream.
drainedLeft :: Monad m => ProcessT m a (Either s b) -> ProcessT m a (Either s b)
drainedLeft snk = MachineT $ runMachineT snk >>= \v -> case v of
  Stop -> runMachineT $ repeatedly await
  Yield (Left r) _ -> runMachineT $ drainCap (Left r)
  Yield (Right x) k -> return $ Yield (Right x) (drainedLeft k)
  Await f Refl ff -> return $ awaitStep f Refl ff drainedLeft

-- | Break an input stream on the boundaries indicated the given
-- function, and feed the first such chunk downstream, while unreading
-- any leftovers before stopping.
oneChunk :: (a -> (b, Maybe a)) -> Machine (Unread a) b
oneChunk f = repeatedly $ do (h,t) <- f <$> awaits Read
                             yield h
                             traverse (\t' -> unread t' *> stop) t

-- | Break an input stream on the boundaries indicated by the given
-- function. No value pushed downstream will cross chunk boundaries.
chunk :: (a -> (b, Maybe a)) -> Machine (Unread a) b
chunk f = repeatedly $ do (h,t) <- f <$> awaits Read
                          maybe (return ()) unread t
                          yield h

-- | Don't yield a value that crosses the chunk boundary indicated by
-- the given function.
chunked :: (a -> (a, Maybe a)) -> Process a a
chunked = (~<> stopped) . chunk
