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

-- import qualified SMT.Boolector.Natural.Binary  as N
import qualified SMT.Satchmo.Integer as N

import qualified SMT.Semiring.Integer ()

import SMT.Dictionary (Domain(..))
import qualified SMT.Plain.Integer as SI

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe

import Data.Hashable
import Control.Monad (when)


-- matrix_arctic_dp :: Int -> Int -> TRS v c -> Work (TRS v x) Doc
matrix_natural_dp dim bits = original_matrix_natural_dp
      ( O.options0 { O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dp = True })

original_matrix_natural_dp opts = 
      remover_natural ( "matrix_natural_dp" :: Doc ) CC.expand_all_trs
    $ MB.Matrix.handle_dp
       N.dict -- Boolector
       -- SI.binary_fixed -- Satchmo
       SI.direct opts

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




