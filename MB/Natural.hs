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
import qualified SMT.Satchmo.Integer as S
import qualified SMT.Satchmo.Integer.Guarded as SG

import qualified SMT.Semiring.Integer ()

import SMT.Dictionary (Domain(..))
import qualified SMT.Plain.Integer as SI

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe

import Data.Hashable
import Control.Monad (when)


-- matrix_arctic_dp :: Int -> Int -> TRS v c -> Work (TRS v x) Doc
matrix_natural_dp opts dim bits = original_matrix_natural_dp
      ( -- O.options0
        opts{  O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dp = True })

original_matrix_natural_dp opts = 
      remover_natural ( "matrix_natural_dp" :: Doc ) CC.expand_all_trs
    $ case O.solver opts of
        O.Boolector -> MB.Matrix.handle_dp B.dict SI.direct opts
        O.Satchmo   -> MB.Matrix.handle_dp S.dict SI.direct opts
        O.Satchmo_Guarded -> MB.Matrix.handle_dp SG.dict SI.direct opts

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




