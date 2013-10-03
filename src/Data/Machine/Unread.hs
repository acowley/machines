{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Machine.Unread
-- Copyright   :  (C) 2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs
--
----------------------------------------------------------------------------
module Data.Machine.Unread
  ( Unread(..)
  , peek
  , peekMaybe
  , unread
  , (~<>)
  , unreadable
  , unreadableTo
  , unreadableSwitch
  , unreadableSwitchTo
  , processWhile
  ) where
import Control.Applicative ((<|>), (*>))
import Data.Machine
import Data.Sequence ((|>), viewl, ViewL(..))
import qualified Data.Sequence as S

import qualified Data.Foldable as F

-- | This is a simple process type that knows how to push back input.
data Unread a r where
  Unread :: a -> Unread a ()
  Read   :: Unread a a
  
-- | Peek at the next value in the input stream without consuming it
peek :: Plan (Unread a) b a
peek = do
  a <- awaits Read
  awaits (Unread a)
  return a

-- | Peek at the next value in the stream without consuming it. If the
-- input stream has stopped, returns 'Nothing'.
peekMaybe :: Plan (Unread a) b (Maybe a)
peekMaybe = do a <- awaits Read
               unread a
               return (Just a)
            <|> return Nothing

-- | Push back into the input stream
unread :: a -> Plan (Unread a) b ()
unread a = awaits (Unread a)

-- | Run a machine with a push-back buffer. When it stops, any
-- leftovers are drained downstream to a 'ProcessT' that takes over.
-- 
-- The operator symbol is designed to be evocative of both the
-- monoidal operation, '<>', between machines, wherein one machine
-- picks up where another stops, and regular piping of values between
-- 'Process'es, '~>', that feeds values downstream one at a
-- time. Here we are monoidally combining two machines, but also
-- feeding leftover values downstream.
(~<>) :: Monad m => MachineT m (Unread a) b -> ProcessT m a b -> ProcessT m a b
ma ~<> mb = unreadable ma mb

infixr 8 ~<>

-- | Provide a machine with push-back. When it completes, any
-- leftovers are drained downstream before behavior switches to the
-- 'MachineT' given as the last argument. The first two arguments
-- provide a mechanism for the downstream input language to masquerade
-- as 'Is'. Specifically, a method to feed leftover values to the new
-- behavior, and a method to issue upstream requests when the unread
-- cache is empty.
unreadableTo
  :: Monad m
  => (forall t. F.Foldable t => t a -> MachineT m k b -> MachineT m k b)
  -> (forall c. Is a c -> k c)
  -> MachineT m (Unread a) b
  -> MachineT m k b
  -> MachineT m k b
unreadableTo prep refl firstMe thenYou = go S.empty firstMe
  where go q ma = MachineT $ runMachineT ma >>= \v -> case v of
          Stop -> runMachineT $ prep q thenYou
          Yield o k -> return . Yield o $ go q k
          Await f Read ff -> 
            case viewl q of
              EmptyL -> return $ Await (\a -> go q (f a)) (refl Refl) (go q ff)
              u :< q' -> runMachineT $ go q' (f u)
          Await f (Unread u) _ -> runMachineT $ go (q |> u) (f ())

-- | Provide a machine with push-back. When it completes, any
-- leftovers are drained downstream before behavior switches to the
-- 'Process' given as the second argument.
unreadable :: Monad m
           => MachineT m (Unread a) b -> ProcessT m a b -> ProcessT m a b
unreadable = unreadableTo ((~>) . prepended) id

-- | Provide a switching machine with push-back. The user provides a
-- handler for yielded values allows for switching to a new
-- 'ProcessT'. When switching to the new 'ProcessT', any leftovers are
-- drained downstream to the new process. The first two arguments
-- provide a mechanism for the downstream input language to masquerade
-- as 'Is'. Specifically, a method to feed leftover values to the new
-- behavior, and a method to issue upstream requests when the unread
-- cache is empty.
unreadableSwitchTo
  :: Monad m
  => (forall t. F.Foldable t => t a -> MachineT m k b -> MachineT m k b)
  -> (forall c. Is a c -> k c)
  -> MachineT m (Unread a) (Either (MachineT m k b) b)
  -> MachineT m k b
unreadableSwitchTo prep refl ma0 = go S.empty ma0
  where go q ma = MachineT $ runMachineT ma >>= \v -> case v of
          Stop -> return Stop
          Yield (Left k) _ -> runMachineT $ prep q k
          Yield (Right o) k -> return . Yield o $ go q k
          Await f Read ff -> 
            case viewl q of
              EmptyL -> return $ Await (\a -> go q (f a)) (refl Refl) (go q ff)
              u :< q' -> runMachineT $ go q' (f u)
          Await f (Unread u) _ -> runMachineT $ go (q |> u) (f ())

-- | Provide a switching machine with push-back. The user provides a
-- handler for yielded values allows for switching to a new
-- 'ProcessT'. When switching to the new 'ProcessT', any leftovers are
-- drained downstream to the new process.
unreadableSwitch :: Monad m
                 => MachineT m (Unread a) (Either (ProcessT m a b) b)
                 -> ProcessT m a b
unreadableSwitch = unreadableSwitchTo ((~>) . prepended) id

{-
-- TODO: Is this worth having?

-- | Support push-back from downstream. All values pushed back are
-- joined through the binary 'Monoid' operation and fed back
-- downstream at the next await.
--
-- @unreadMonoid isEmpty sink@ implements @sink@'s unread buffer using
-- the given @isEmpty@ predicate to determine when the unread cache is
-- empty.
unreadMonoid :: forall a b m. (Monoid a, Monad m)
             => (a -> Bool) -> MachineT m (Unread a) b -> ProcessT m a b
unreadMonoid isEmpty = go mempty
  where go :: a -> MachineT m (Unread a) b -> ProcessT m a b
        go q ma = MachineT $ runMachineT ma >>= \v -> case v of
          Stop -> return Stop
          Yield o k -> return . Yield o $ go q k
          Await f Read ff
            | isEmpty q -> return $ awaitStep f Refl ff (go q)
            | otherwise -> runMachineT $ go mempty (f q)
          Await f (Unread u) _ -> runMachineT $ go (q <> u) (f ())
-}

-- | Echo values as long the predicate holds true of each element. The
-- first value that does not satisfy the predicate is pushed back into
-- the unread cache.
processWhile :: (o -> Bool) -> Machine (Unread o) o
processWhile f = construct go
  where go = do x <- awaits Read
                if f x
                then yield x >> go
                else unread x *> stop
