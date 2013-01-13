-- | simplified Matchbox Termination Prover

import MB.Options
import MB.Arctic

import qualified TPDB.DP
import TPDB.Input ( get_trs )

import System.Environment
import System.Console.GetOpt

main = do
   argv <- getArgs
   case getOpt Permute options argv of
       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os
           sys <- get_trs path
           case dp opts of
               False -> handle opts sys
               True -> handle_dp opts $ TPDB.DP.dp sys
       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "MB" options
