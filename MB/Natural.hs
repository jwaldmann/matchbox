{-# language NoMonomorphismRestriction #-}
{-# language OverloadedStrings #-}

module MB.Natural where

import TPDB.Data
import TPDB.Pretty

import qualified MB.Options as O
import qualified MB.Matrix 

import MB.Proof
import qualified MB.Proof as P

import qualified Compress.Common as CC

import qualified SMT.Boolector.Natural.Binary as B  
import qualified SMT.Satchmo.Natural as SN

-- import qualified SMT.Satchmo.Integer as SI
import qualified SMT.Satchmo.Integer.Native as SI

import qualified SMT.Boolector.Integer as BI
import qualified SMT.Satchmo.Natural.Interval as SNI
import qualified SMT.Satchmo.Natural.Guarded as SNG

import qualified SMT.Semiring.Integer ()

import SMT.Dictionary (Domain(..))
import qualified SMT.Plain.Integer as SPI

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe

import Data.Hashable
import Control.Monad (when)

matrix_natural_direct opts dim bits = original_matrix_natural_direct
      ( opts{  O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dependency_pairs = False })


matrix_natural_dp opts dim bits = original_matrix_natural_dp 
      ( opts{  O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dependency_pairs = True })

original_matrix_natural_direct opts =
    remover_natural ( case O.mode opts of
                         O.Termination -> P.Termination
                         O.Complexity {} -> P.Termination -- FIXME
                         O.Cycle_Termination -> P.Cycle_Termination
                    )
       ("matrix_natural_direct" :: Doc) CC.expand_all_trs
  $ case O.solver opts of
         O.Satchmo -> MB.Matrix.handle SI.dict SPI.direct opts
         O.Boolector -> MB.Matrix.handle BI.dict SPI.direct opts

original_matrix_natural_dp opts = 
      remover_natural P.Top_Termination ( "matrix_natural_dp" :: Doc ) CC.expand_all_trs
    $ case O.solver opts of
        O.Boolector ->
          MB.Matrix.handle_dp BI.dict SPI.direct opts
        O.Satchmo   -> case O.encoding opts of
          O.Binary -> MB.Matrix.handle_dp SI.dict SPI.direct opts
          O.Interval_Plain ->
              MB.Matrix.handle_dp SNI.dict_plain SPI.direct opts
          O.Interval_Fibs ->
              MB.Matrix.handle_dp SNI.dict_fibs SPI.direct opts
          O.Interval_Twos ->
              MB.Matrix.handle_dp SNI.dict_twos SPI.direct opts
          O.Interval_Threes ->
              MB.Matrix.handle_dp SNI.dict_threes SPI.direct opts
              
        O.Satchmo_Guarded -> MB.Matrix.handle_dp SNG.dict SPI.direct opts

remover_natural clm msg unpack h  sys = do
    let usable = filter ( not . strict ) $ rules $ unpack sys
    out <- h sys
    return $ case out of 
        Nothing -> Nothing
        Just (m, sys') -> do
            when (length ( rules sys) == length (rules sys')) 
                 $ error "huh"
            return ( sys'
                   , \ out ->  
               Proof 
               { input = unpack sys
               , claim = clm
               , reason = Matrix_Interpretation_Natural m (Just usable) out
               }
                   )




