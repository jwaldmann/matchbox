module MB.Solver where

import qualified MB.Options as O

import qualified Satchmo.SAT.Mini
import qualified Boolector

import System.Random
import System.Directory
import System.Posix.Time
import System.IO
import Control.Monad ( when )
import Control.Monad.Trans ( liftIO )
import Data.List ( intersperse )
import Data.Maybe ( isJust )

class Monad m => Solver m  where
    solve :: O.Options -> m (m a) -> IO (Maybe a)
    
instance Solver Satchmo.SAT.Mini.SAT where
    solve opts = Satchmo.SAT.Mini.solve

instance Solver Boolector.Boolector where
    solve opts action = Boolector.withBoolectorAsync $ do
      decoder <- action
      start <- liftIO $ System.Posix.Time.epochTime
      return $ do
        result <- decoder
        finish <- liftIO $ System.Posix.Time.epochTime
        case O.dump_boolector opts of
          O.Never -> return ()
          O.Above threshold ->  do
            let status = True
            let needed = finish - start
            when (needed >= fromIntegral threshold) $ do
              off <- liftIO $ randomRIO (1000, 9999 :: Int)
              let dir = concat $ intersperse "/"
                    [ "dump", show status , show needed ]
                  fname = dir ++ "/" ++ show start ++ "-" ++ show off ++ ".smt2"
              liftIO $ createDirectoryIfMissing True dir    
              liftIO $ hPutStrLn stderr $ unwords [ "boolector smt2 dump to", fname ]
              Boolector.dumpSmt2 fname
        return result

      

    
