module MB.Solver where

import qualified MB.Options as O

import qualified Satchmo.SAT.Mini
import qualified Boolector

import System.Random
import System.Posix.Time
import System.IO
import Control.Monad ( when )
import Control.Monad.Trans ( liftIO )

class Monad m => Solver m  where
    solve :: O.Options -> m (m a) -> IO (Maybe a)
    
instance Solver Satchmo.SAT.Mini.SAT where
    solve opts = Satchmo.SAT.Mini.solve

instance Solver Boolector.Boolector where
    solve opts action = Boolector.withBoolectorAsync $ do
      decoder <- action
      when (O.dump_boolector opts) $ do
        sec <- liftIO $ System.Posix.Time.epochTime
        off <- liftIO $ randomRIO (1000, 9999 :: Int)
        let fname = concat ["dump", "-", show sec, "-", show off, ".smt2" ]
        Boolector.dumpSmt2 fname
        liftIO $ hPutStrLn stderr $ unwords [ "boolector smt2 dump to", fname ]
      return decoder
      

    
