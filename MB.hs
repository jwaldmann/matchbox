-- | simplified Matchbox Termination Prover

{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

import MB.Options hiding ( parallel, dp )
import qualified MB.Options as O

import MB.Strategy
import qualified Control.Concurrent.Combine as C
import qualified Control.Concurrent.Combine.Action as A

import qualified MB.Additive

import qualified Compress.DP 
import qualified Compress.Common as CC
import qualified Compress.PaperIter as CPI

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
import Data.Hashable

transform_dp = transformer
      ( \ sys -> return $ TPDB.DP.dp sys ) 
      ( \ sys proof -> vcat [ "DP transform"
                            , nest 4 proof ] )

comp :: ( Show v, Pretty v, Ord v
        , Show s, Pretty s, Ord s, Hashable s
        )
     => TRS v s 
     -> TRS v (CC.Sym s)
comp sys = let (_, csys) = CPI.compress $ rules sys
           in  RS { rules = CC.roots csys 
                         , separate = separate sys 
                         }

transform_mirror = transformer
      ( \ sys -> TPDB.Mirror.mirror sys )
      ( \ sys proof -> vcat [ "Mirror transform"
                            , nest 4 proof ] )

simplex :: (Pretty v, Pretty s, Ord s, Ord v)
        => Bool -- ^ prove top termination?
        -> C.Lifter (TRS v s) (TRS v s) Doc
simplex top = remover "additive" 
    $ \ sys -> do
         let out = MB.Additive.find top sys 
         return out

matrix_natural_full opts = 
      remover "matrix_natural_full"
    $ MB.Matrix.handle I.binary_fixed I.direct opts
                 
matrix_arctic_dp opts = 
      remover "matrix_arctic_dp"
    $ MB.Matrix.handle_dp A.unary_fixed A.direct opts
                 
matrix_arctic_hack_dp opts = 
    remover "matrix_arctic_hack_dp" $ \ sys -> 
    let t = CC.Trees
          { CC.roots = rules $ Compress.DP.dp 
                     $ comp sys
          , CC.extras = []
          }
    in  MB.Matrix.handle_dp_continue
        A.unary_fixed A.direct opts 
           undefined -- (TPDB.DP.dp sys ) 
           undefined -- t
                 
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

cmatrix_hack_dp opts = 
    ( if O.parallel opts
      then C.parallel else C.sequential ) $ do
          d <- [ 1 .. dim opts ]
          return $ matrix_arctic_hack_dp
                 ( opts { dim = d } ) 

simplexed top cont 
    = C.orelse no_strict_rules 
    $ C.apply ( C.orelse (simplex top) cont )
    $ simplexed top cont

repeated cont
    = C.orelse no_strict_rules 
    $ C.apply cont
    $ repeated cont


direct opts =  simplexed False 
       $ cmatrix opts 

dp opts = case O.compression opts of
       Hack_DP -> hack_dp opts 
       _ -> plain_dp opts

plain_dp opts = 
      C.apply transform_dp
    $ simplexed True
    $ cmatrix_dp opts

hack_dp opts = undefined
{-
      C.apply transform_dp_compress
    $ simplexed True
    $ cmatrix_hack_dp opts
-}

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




