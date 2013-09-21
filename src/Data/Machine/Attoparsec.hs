{-# LANGUAGE RankNTypes, TupleSections #-}
-- | Build machines that apply parsers to input streams.
module Data.Machine.Attoparsec where
import Control.Applicative
import Data.Attoparsec.Types
import Data.Machine
import Data.Machine.Unread
import Data.Monoid

-- | Run a parser against an input stream. Errors are yielded as
-- 'Left' values, successful parse results are tagged with 'Right'.
parse :: Monoid t
      => (t -> IResult t a)
      -> Plan (Unread t) (Either String a) ()
parse p = 
  do x <-Just <$> awaits Read <|> pure Nothing
     let (x',nxt) = maybe (mempty, stop) (, return ()) x
     case p x' of
       Fail leftover _ err -> unread leftover >> yield (Left err) >> nxt
       Partial k -> parse k
       Done leftover r -> unread leftover >> yield (Right r) >> nxt

-- | Parse input until the parser fails or yields a successful
-- parse. Errors cause the machine to stop, but are not yielded.
parseOnce_ :: (Monad m, Monoid t)
           => (t -> IResult t c) -> MachineT m (Unread t) c
parseOnce_ p = repeatedly (parse p) ~> construct aux
  where aux = await >>= either (const stop) (\x -> yield x *> stop)

-- | Parse input until the parser fails or yields a successful
-- parse. Errors are yielded as 'Left' values.
parseOnce :: (Monad m, Monoid t)
          => (t -> IResult t c) -> MachineT m (Unread t) (Either String c)
parseOnce p = repeatedly (parse p) ~> construct aux
  where aux = await >>= \x -> yield x *> stop

-- | Repeatedly run a parser over a stream yielding all succesful
-- parses.
parses :: Monoid t => (t -> IResult t a) -> Process t a
parses p = (repeatedly (parse p) ~<> stopped) ~> yieldRights
