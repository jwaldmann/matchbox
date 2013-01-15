-- | simplified Matchbox Termination Prover

{-# language OverloadedStrings #-}

import MB.Options

-- import MB.Strategy

import qualified MB.Additive

import qualified MB.Matrix 
import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Arctic  as A

import qualified TPDB.DP
import TPDB.Input ( get_trs )
import TPDB.Pretty ( pretty )
import Text.PrettyPrint.HughesPJ
import TPDB.Data

import System.Environment
import System.Console.GetOpt
import Control.Monad ( void )

import Prelude hiding ( iterate )


remove handle opts sys0 = 
    if null $ strict_rules sys0
    then return "no strict rules"
    else case MB.Additive.find sys0 of
        Nothing -> iterate handle opts 1 sys0
        Just ( f, sys1 ) -> do
            later <- remove handle opts sys1
            return $ pretty sys0 $$ pretty f $$ later

iterate handle opts d sys0 = do    
    if null $ strict_rules sys0
       then return "no strict rules"
       else do
           x <- handle ( opts { dim = d } ) sys0
           case x of
               Nothing -> iterate handle opts (d+1) sys0
               Just (f, sys1) -> do
                  later <- remove handle opts sys1
                  return $ pretty sys0 $$ pretty f $$ later

main = do
   argv <- getArgs
   case getOpt Permute options argv of
       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os
           sys <- get_trs path
           out <- case dp opts of
               False -> 
                   remove 
                     (MB.Matrix.handle  
                     I.binary_fixed I.direct  )
                     opts $            sys
               True  -> 
                   remove 
                     (MB.Matrix.handle_dp 
                     -- I.binary_fixed I.direct
                     A.unary_fixed A.direct
                     )
                     opts $ TPDB.DP.dp sys
           print $ vcat
                 [ "YES"
                 , "input" <+> pretty sys
                 , "proof" <+> out 
                 ]
       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "MB" options
