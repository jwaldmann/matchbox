-- | simplified Matchbox Termination Prover

{-# language OverloadedStrings #-}

import MB.Options

-- import MB.Strategy

import qualified MB.Natural

import qualified TPDB.DP
import TPDB.Input ( get_trs )
import TPDB.Pretty ( pretty )
import Text.PrettyPrint.HughesPJ
import TPDB.Data

import System.Environment
import System.Console.GetOpt
import Control.Monad ( void )

import Prelude hiding ( iterate )

iterate handle opts d sys0 = do    
    if null $ strict_rules sys0
       then return "no strict rules"
       else do
           x <- handle ( opts { dim = d } ) sys0
           case x of
               Nothing -> iterate handle opts (d+1) sys0
               Just (f, sys1) -> do
                  later <- iterate handle opts 1 sys1
                  return $ pretty sys0 $$ pretty f $$ later

main = do
   argv <- getArgs
   case getOpt Permute options argv of
       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os
           sys <- get_trs path
           out <- case dp opts of
               False -> iterate MB.Natural.handle    opts 1 $            sys
               True  -> iterate MB.Natural.handle_dp opts 1 $ TPDB.DP.dp sys
           print $ vcat
                 [ "YES"
                 , "input" <+> pretty sys
                 , "proof" <+> out 
                 ]
       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "MB" options
