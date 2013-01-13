-- | simplified Matchbox Termination Prover

import MB.Options
import MB.Natural

import qualified TPDB.DP
import TPDB.Input ( get_trs )

import System.Environment
import System.Console.GetOpt
import Control.Monad ( void )




main = do
   argv <- getArgs
   case getOpt Permute options argv of
       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os
           sys <- get_trs path
           case dp opts of
               False -> void $ handle opts sys
               True  -> void $ handle_dp opts $ TPDB.DP.dp sys
       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "MB" options
