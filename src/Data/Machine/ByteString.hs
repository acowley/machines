{-# LANGUAGE RankNTypes #-}
module Data.Machine.ByteString where
import Control.Applicative
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy.Char8 as BCL
import Data.Machine
import Data.Machine.Chunk
import Data.Machine.Unread
import System.IO (openFile, IOMode(..), hClose)

-- | @bsSourceChunks n file@ produces 'BS.ByteString' chunks of size @n@
-- bytes from @file@.
bsSourceChunks :: MonadIO m => Int -> FilePath -> SourceT m BS.ByteString
bsSourceChunks n f = construct $ 
             do h <- liftIO $ openFile f ReadMode
                let go = do bs <- liftIO $ BS.hGet h n
                            if BS.null bs
                            then liftIO (hClose h) >> stop
                            else yield bs >> go
                go

-- | @bsSource file@ produces @64KB@ 'BS.ByteString' chunks from
-- @file@. If you want control over how much is read in each chunk,
-- see 'bsSourceChunks'.
bsSource :: MonadIO m => FilePath -> SourceT m BS.ByteString
bsSource = bsSourceChunks (64 * 1024)

-- | Provide entire lines downstream. If lines can be very long, then
-- this can exhaust memory! If that is a concern, consider using
-- 'Data.Machine.Chunk.foldChunks' for your line-handling needs.
entireLine :: Process BC.ByteString BC.ByteString
entireLine = construct $ go BCL.empty
  where go acc = do acc' <- BCL.append acc . BCL.fromStrict <$> await
                    let lns = BCL.lines acc'
                    mapM_ (yield . BCL.toStrict) $ init lns
                    go (last lns)

-- | Break a 'BS.ByteString' into chunks of the given length.
bsChunks :: Int -> Machine (Unread BS.ByteString) BS.ByteString
bsChunks n = chunk f
  where f bs = let (h,t) = BS.splitAt n bs
               in (h, if BS.null t then Nothing else Just t)

-- | Function that breaks a 'BC.ByteString' on newline characters
-- (@'\\n'@). Returns a prefix of the input before any newline
-- character, and a suffix starting after the first newline character.
lineBreaker :: BC.ByteString -> (BC.ByteString, Maybe BC.ByteString)
lineBreaker x = case BC.findIndex (== '\n') x of
                    Nothing -> (x, Nothing)
                    Just i -> (BC.take i x, Just $ BC.drop (i+1) x)
