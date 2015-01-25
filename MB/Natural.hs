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
import qualified SMT.Satchmo.Natural as SI
import qualified SMT.Satchmo.Natural.Interval as SII
import qualified SMT.Satchmo.Natural.Guarded as SIG

import qualified SMT.Semiring.Integer ()

import SMT.Dictionary (Domain(..))
import qualified SMT.Plain.Integer as SPI

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe

import Data.Hashable
import Control.Monad (when)


matrix_natural_direct opts dim bits = original_matrix_natural_direct
      ( opts{  O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dp = False })


matrix_natural_dp opts dim bits = original_matrix_natural_dp 
      ( opts{  O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dp = True })

original_matrix_natural_direct opts =
    remover_natural ("matrix_natural_direct" :: Doc) CC.expand_all_trs
  $ MB.Matrix.handle SI.dict SPI.direct opts

original_matrix_natural_dp opts = 
      remover_natural ( "matrix_natural_dp" :: Doc ) CC.expand_all_trs
    $ case O.solver opts of
        O.Boolector -> MB.Matrix.handle_dp B.dict SPI.direct opts
        O.Satchmo   -> case O.encoding opts of
          O.Binary -> MB.Matrix.handle_dp SI.dict SPI.direct opts
          O.Interval_Plain ->
              MB.Matrix.handle_dp SII.dict_plain SPI.direct opts
          O.Interval_Fibs ->
              MB.Matrix.handle_dp SII.dict_fibs SPI.direct opts
          O.Interval_Twos ->
              MB.Matrix.handle_dp SII.dict_twos SPI.direct opts
          O.Interval_Threes ->
              MB.Matrix.handle_dp SII.dict_threes SPI.direct opts
              
        O.Satchmo_Guarded -> MB.Matrix.handle_dp SIG.dict SPI.direct opts

remover_natural msg unpack h  sys = do
    let usable = filter ( not . strict ) $ rules $ unpack sys
    out <- h sys
    return $ case out of 
        Nothing -> Nothing
        Just (m, sys') -> do
            when (length ( rules sys) == length (rules sys')) 
                 $ error "huh"
            return ( sys'
                   , \ out ->  
                   -- "Arctic" <+> vcat [ "sys:" <+> pretty sys , pretty m, out ]
               Proof 
               { input = unpack sys
               , claim = Top_Termination
               , reason = Matrix_Interpretation_Natural m (Just usable) out
               }
                   )




