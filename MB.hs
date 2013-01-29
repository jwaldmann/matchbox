-- | simplified Matchbox Termination Prover

{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

import MB.Options hiding ( parallel, dp )
import qualified MB.Options as O

import MB.Strategy
import qualified Control.Concurrent.Combine as C
import qualified Control.Concurrent.Combine.Action as A

import qualified MB.Additive

import qualified MB.Matrix 
import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Arctic  as A

import qualified TPDB.DP
import qualified TPDB.Mirror
import TPDB.Input ( get_trs )
import TPDB.Pretty ( pretty, Pretty )
import Text.PrettyPrint.HughesPJ
import TPDB.Data

import System.Environment
import System.IO
import System.Console.GetOpt
import Control.Monad ( void, forM )

import Data.Maybe (isJust, fromMaybe)
import Prelude hiding ( iterate )

transform_dp = transformer
      ( \ sys -> return $ TPDB.DP.dp sys ) 
      ( \ sys proof -> vcat [ "DP transform"
                            , nest 4 proof ] )
transform_mirror = transformer
      ( \ sys -> TPDB.Mirror.mirror sys )
      ( \ sys proof -> vcat [ "Mirror transform"
                            , nest 4 proof ] )

simplex :: (Pretty v, Pretty s, Ord s, Ord v)
        => C.Lifter (TRS v s) (TRS v s) Doc
simplex = remover "additive" 
    $ \ sys -> do
         let out = MB.Additive.find sys 
         return out

matrix_natural_full opts = 
      remover "matrix_natural_full"
    $ MB.Matrix.handle I.binary_fixed I.direct opts
                 
matrix_arctic_dp opts = 
      remover "matrix_arctic_dp"
    $ MB.Matrix.handle_dp A.unary_fixed A.direct opts
                 
cmatrix opts = 
    ( if O.parallel opts
      then C.parallel else C.sequential ) $ do
          d <- [ 1 .. dim opts ]
          return $ matrix_natural_full 
                 ( opts { dim = d } ) 

cmatrix_dp opts = 
    ( if O.parallel opts
      then C.parallel else C.sequential ) $ do
          d <- [ 1 .. dim opts ]
          return $ matrix_arctic_dp
                 ( opts { dim = d } ) 

simplexed cont 
    = C.orelse no_strict_rules 
    $ C.apply ( C.orelse simplex cont )
    $ simplexed cont

repeated cont
    = C.orelse no_strict_rules 
    $ C.apply cont
    $ repeated cont


direct opts =  simplexed 
       -- repeated
       $ cmatrix opts 

dp opts = 
      C.apply transform_dp 
    -- $ repeated 
    $ simplexed 
    $ cmatrix_dp opts 



main = do
   hSetBuffering stdout LineBuffering
   hSetBuffering stderr LineBuffering
   argv <- getArgs
   case getOpt Permute options argv of

       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os

           sys <- get_trs path

           let strategy = 
                 ( case O.mirror opts of
                     False -> id
                     True -> C.apply transform_mirror
                 )
                 $ case O.dp opts of
                   False -> direct opts
                   True  -> dp opts

           A.run ( strategy sys ) >>= \ x -> case x of
               Nothing -> print $ text "MAYBE"
               Just out -> print $ vcat
                 [ "YES" , out ]

       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "mb" options




