-- | simplified Matchbox Termination Prover

{-# language OverloadedStrings #-}

import MB.Options hiding ( parallel )
import qualified MB.Options as O

-- import MB.Strategy

import qualified MB.Additive

import qualified MB.Matrix 
import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Arctic  as A

import qualified TPDB.DP
import qualified TPDB.Mirror
import TPDB.Input ( get_trs )
import TPDB.Pretty ( pretty )
import Text.PrettyPrint.HughesPJ
import TPDB.Data

import System.Environment
import System.IO
import System.Console.GetOpt
import Control.Monad ( void, forM )
import Control.Concurrent.Async
import Control.Concurrent.STM
import Control.Concurrent.STM.TVar (modifyTVar)
import Data.Maybe (isJust, fromMaybe)
import Prelude hiding ( iterate )


remove handle opts sys0 = 
    if null $ strict_rules sys0
    then return "no strict rules"
    else case MB.Additive.find sys0 of
        Nothing -> case O.parallel opts of
            False -> iterate  handle opts 1 sys0
            True  -> parallel handle opts 1 sys0
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

parallel handle opts _ sys0 = do
    running <- atomically $ newTVar ( dim opts )
    result <- atomically $ newTVar Nothing
    pids <- forM [ 1 .. dim opts ] $ \ d -> async $ do
        x <- handle ( opts { dim = d } ) sys0
        atomically $ modifyTVar running pred
        case x of 
            Nothing -> return ()
            Just (f, sys1) -> atomically $ do
                    writeTVar result x
    out <- atomically $ do
        u <- readTVar running
        r <- readTVar result
        check $ 0 == u || isJust r
        return r
    forM pids $ \ pid -> async $ cancel pid
    case out of
        Just (f, sys1) -> do
            later <- remove handle opts sys1
            return $ pretty sys0 $$ pretty f $$ later 

main = do
   hSetBuffering stdout LineBuffering
   hSetBuffering stderr LineBuffering
   argv <- getArgs
   case getOpt Permute options argv of
       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os
           sys0 <- get_trs path

           let sys = case O.mirror opts of
                   True -> fromMaybe sys0 $ TPDB.Mirror.mirror sys0
                   False -> sys0

           out <- case dp opts of
               False -> 
                   remove 
                     (MB.Matrix.handle  
                     -- I.binary_fixed_plain I.direct  
                     I.binary_fixed I.direct  
                     )
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
