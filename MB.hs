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
import qualified Compress.Simple as CS
import qualified Compress.PaperIter as CPI
import qualified Compress.Paper as CP

import qualified MB.Matrix 
import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Arctic  as A
import Satchmo.SMT.Dictionary (Domain(..))

import qualified TPDB.DP
import qualified TPDB.Mirror
import TPDB.Input ( get_trs )

import Text.PrettyPrint.HughesPJ
import TPDB.Pretty ( pretty, Pretty )

import TPDB.Data

import qualified MB.Proof as P

-- import Text.XML.HaXml.ByteStringPP ( document )
-- import qualified Data.ByteString.Lazy.Char8 as DBS

import Text.PrettyPrint.Leijen 
       ( displayIO, renderCompact)
import HaXml.Pretty ( document )

import System.Environment
import System.IO
import System.Console.GetOpt
import Control.Monad ( void, forM )

import Data.Maybe (isJust, fromMaybe)
import Prelude hiding ( iterate )
import Data.Hashable
import Debug.Trace

transform_dp = transformer
      ( \ sys -> do
          return $ Compress.DP.dp sys ) 
      ( \ sys proof -> 
          P.Proof { P.input = CC.expand_all_trs sys
                  , P.claim = P.Top_Termination
                  , P.reason = P.DP_Transform proof 
                  } )

transform_mirror = transformer
      ( \ sys -> TPDB.Mirror.mirror sys )
      ( \ sys proof ->
          P.Proof { P.input = sys
                  , P.claim = P.Termination
                  , P.reason = P.Mirror_Transform proof 
                  } )

transformer_neutral = transformer
     ( \ sys -> return sys )
     ( \ sys proof -> proof )

compressor_fromtop = transformer
    ( \ sys ->  return $ Compress.DP.fromtop sys )
    ( \ sys proof -> P.Proof
         { P.input = CC.expand_all_trs sys
         , P.claim = P.Top_Termination
         , P.reason = 
              P.Equivalent "compress_fromtop" proof
         } )

compressor :: ( Hashable s, Pretty s, Ord s, Show s
              , Ord v, Pretty v, Show v)
           => Compression
           -> C.Lifter (TRS v s) (TRS v (CC.Sym s)) 
               (P.Proof v s)
compressor c = transformer 
    ( \ sys -> let (cost, rs) = ( case c of
                       O.None -> CS.nocompress 
                       O.Simple -> CS.compress 
                       O.Paper -> CP.compress CP.Simple
                       O.PaperIter -> CP.compress CP.Iterative
                     ) $ rules sys
               in  return $ RS { rules = CC.roots rs
                               , separate = separate sys }
    )
    ( \ sys proof -> P.Proof
         { P.input = sys
         , P.claim = P.Termination
         , P.reason = 
              P.Equivalent (text $ show c) proof
         } )

simplex :: (Pretty v, Pretty s, Ord s, Ord v)
        => Bool -- ^ prove top termination?
        -> C.Lifter (TRS v s) (TRS v s) (P.Proof v s)
simplex top = remover_natural "additive" id
    $ \ sys -> return $ do
         (f,sys') <- MB.Additive.find top sys 
         return ( P.Interpretation
             { P.dimension = 1
             , P.domain = Int
             , P.mapping = f
             } , sys' )

simplex_compress :: (Pretty v, Pretty s, Ord s, Ord v)
        => Bool -- ^ prove top termination?
        -> C.Lifter (TRS v (CC.Sym s)) (TRS v (CC.Sym s))
             (P.Proof v s)
simplex_compress top = 
       remover_natural "additive" CC.expand_all_trs
    $ \ sys -> return $ do
         (f,sys') <- MB.Additive.find_compress top sys 
         return ( P.Interpretation
             { P.dimension = 1
             , P.domain = Int
             , P.mapping = f
             } , sys' )

matrix_natural_full opts = 
      remover_natural "matrix_natural_full" 
                      CC.expand_all_trs
    $ MB.Matrix.handle I.binary_fixed I.direct opts
                 
matrix_arctic_dp opts = 
      remover_arctic "matrix_arctic_dp" CC.expand_all_trs
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

apply f k = \ sys -> do m <- f sys ; m k

simplexed_compress top cont 
    = C.orelse (no_strict_rules top CC.expand_all_trs)
    $ apply ( C.orelse (simplex_compress top) cont )
    $ simplexed_compress top cont

direct opts =  
      apply (compressor $  O.compression opts )
    $ simplexed_compress False 
    $ cmatrix opts 


dp opts = 
      apply (compressor $  O.compression opts )
    $ apply transform_dp
    $ apply (case O.fromtop opts of
         True  -> compressor_fromtop
         False -> transformer_neutral 
      )
    $ simplexed_compress True
    $ cmatrix_dp opts

main = do
   hSetBuffering stdout LineBuffering
   hSetBuffering stderr LineBuffering
   argv <- getArgs
   case getOpt Permute options argv of

       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os

           sys <- get_trs path

           let m = case O.mirror opts of
                     False -> id
                     True -> -- apply transform_mirror 
                         \ strat  -> C.parallel
                             [ strat
                             , apply transform_mirror strat
                             ]

           let emit x = case x of
                   Nothing -> print $ text "MAYBE"
                   Just out -> do
                        putStrLn "YES"
                        case O.cpf opts of
                            True -> 
                              -- DBS.putStrLn 
                              displayIO stdout
                              $ renderCompact
                              $ document 
                              $ P.tox $ P.rtoc out
                            False -> print $ pretty out  

           case O.dp opts of
             False -> A.run ( m ( direct opts ) sys ) >>= emit
             True  -> A.run ( m ( dp     opts ) sys ) >>= emit

       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "mb" options




