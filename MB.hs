-- | simplified Matchbox Termination Prover

{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

import MB.Options hiding ( parallel, dp )
import qualified MB.Options as O

import MB.Strategy
import qualified Control.Concurrent.Combine as C
import qualified Control.Concurrent.Combine.Action as A

import qualified MB.Additive

import qualified MB.Lock

import qualified Compress.DP 
import qualified Compress.Common as CC
import qualified Compress.Simple as CS
import qualified Compress.PaperIter as CPI
import qualified Compress.Paper as CP

import qualified MB.Label.SLPO 

import qualified MB.Matrix 
import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Arctic  as A
import Satchmo.SMT.Dictionary (Domain(..))

import qualified TPDB.DP
import qualified TPDB.Mirror
import TPDB.Input ( get_trs )

import TPDB.Pretty 

import TPDB.Data

import qualified MB.Proof as P

-- import Text.XML.HaXml.ByteStringPP ( document )
-- import qualified Data.ByteString.Lazy.Char8 as DBS


import TPDB.Xml.Pretty ( document )

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

compressor_fromtop 
    :: (Pretty v, Ord v, Ord s, Hashable s, Pretty s ) 
    => Transformer v (CC.Sym s) (CC.Sym s) s
compressor_fromtop = transformer
    ( \ sys ->  return $ Compress.DP.simple_fromtop sys )
    ( \ sys proof -> P.Proof
         { P.input = CC.expand_all_trs sys
         , P.claim = P.Top_Termination
         , P.reason = 
              P.Equivalent "compress_fromtop" proof
         } )

compressor_naive
    :: (Pretty v, Ord v, Ord s, Hashable s, Pretty s ) 
    => Transformer v (CC.Sym s) (CC.Sym s) s
compressor_naive = transformer
    ( \ sys -> do
        let sys0 = CC.expand_all_trs sys
            (_, rs1) = CP.compress CP.Iterative 
                     $ rules sys0
        return -- $ Compress.DP.lift_marks_trs
               $ RS { rules = CC.roots rs1 
                    , separate = separate sys
                    } )
    ( \ sys proof -> P.Proof
         { P.input = CC.expand_all_trs sys
         , P.claim = P.Top_Termination
         , P.reason = 
              P.Equivalent "compress_naive" proof
         } )

type Transformer  v s t u = 
    C.Lifter (TRS v s) (TRS v t) (P.Proof v u)

compressor :: ( Hashable s, Pretty s, Ord s, Show s
              , Ord v, Pretty v, Show v)
           => Compression
           -> Transformer v s (CC.Sym s) s
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
        -> Transformer v s s s
simplex top = remover_natural "additive" id
    $ \ sys -> return $ do
         (f,sys') <- MB.Additive.find top sys 
         return ( P.Interpretation
             { P.dimension = 1
             , P.domain = Int
             , P.mapping = f
             } , sys' )

simplex_compress :: (Pretty v, Pretty s, Ord s, Ord v)
        => MB.Lock.Lock
        -> Bool -- ^ prove top termination?
        -> Transformer v (CC.Sym s)(CC.Sym s) s
simplex_compress lock top = 
       remover_natural "additive" CC.expand_all_trs
    $ \ sys -> MB.Lock.exclusive lock $ return $ do
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
                 
matrix_natural_dp opts = 
      remover_natural "matrix_natural_dp" 
                      CC.expand_all_trs
    $ MB.Matrix.handle_dp I.binary_fixed I.direct opts
                 
matrix_arctic_dp opts = 
      remover_arctic "matrix_arctic_dp" CC.expand_all_trs
    $ MB.Matrix.handle_dp A.unary_fixed A.direct opts
                 

cmatrix opts = 
    ( if O.parallel opts
      then C.parallel else C.sequential ) $ do
          d <- [ 1 .. dim opts ]
          return $ matrix_natural_full 
                 ( opts { dim = d } ) 

cmatrix_dp opts ma = 
    ( if O.parallel opts
      then C.parallel else C.sequential ) $ do
          d <- [ 1 .. dim opts ]
          return $ ma $ opts { dim = d } 

apply f k = \ sys -> do m <- f sys ; m k

simplexed_compress lock top cont 
    = C.orelse (no_strict_rules top CC.expand_all_trs)
    $ apply ( C.orelse (simplex_compress lock top) cont )
    $ simplexed_compress lock top cont

label_remove_unlabel opts = ( if O.parallel opts then C.parallel else C.sequential ) $ do
    let (m,i) = maybe (0,1) id $ O.label opts
    m <- [ 0 .. m ]
    let opts' = opts { O.label = Just (m, min m i) }
    return $ remover_label "label/remove/unlabel" CC.expand_all_trs
           $ MB.Label.SLPO.handle opts'


direct lock opts =  
      apply (compressor $  O.compression opts )
    $ simplexed_compress lock False 
    $ case label opts of
          Nothing -> cmatrix opts 
          Just l  -> label_remove_unlabel opts


dp     lock opts = 
      apply (compressor $  O.compression opts )
    $ apply transform_dp
    $ apply (case O.naive opts of
         True  -> compressor_naive
         False -> transformer_neutral 
      )
    $ apply (case O.fromtop opts of
         True  -> compressor_fromtop
         False -> transformer_neutral 
      )
    $ simplexed_compress lock True
    $ case label opts of
          Nothing ->  C.parallel [ 
                 cmatrix_dp ( opts ) matrix_arctic_dp
                 -- cmatrix_dp ( opts ) matrix_natural_dp
                 ]
          Just l  -> label_remove_unlabel opts

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

           lock <- MB.Lock.create
           case O.dp opts of
             False -> A.run ( m ( direct lock opts ) sys ) >>= emit
             True  -> A.run ( m ( dp     lock opts ) sys ) >>= emit

       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "mb" options




