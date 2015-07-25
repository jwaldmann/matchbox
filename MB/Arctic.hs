{-# language NoMonomorphismRestriction #-}
{-# language OverloadedStrings #-}

module MB.Arctic where

import TPDB.Data
import TPDB.Pretty

import qualified MB.Options as O
import qualified MB.Matrix 

import MB.Proof
import qualified MB.Proof as P

import qualified Compress.Common as CC

import qualified SMT.Satchmo.Arctic.Unary  as SAU
import qualified SMT.Satchmo.Arctic.Interval  as SAI

import qualified SMT.Boolector.Arctic.Binary  as BAB
import qualified SMT.Boolector.Arctic.Unary   as BAU

import qualified SMT.Plain.Arctic  as SA
-- import qualified SMT.Arctic  as SA
import SMT.Dictionary (Domain(..))


import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe

import Data.Hashable
import Control.Monad (when)

matrix_arctic_direct opts dim bits = original_matrix_arctic_direct
      ( opts { O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dependency_pairs = False })

original_matrix_arctic_direct opts = 
      remover_arctic (case O.mode opts of
                         O.Termination -> P.Termination
                         O.Cycle_Termination -> P.Cycle_Termination
                     )
      ( "matrix_arctic_direct" :: Doc ) CC.expand_all_trs
    $ case O.solver opts of
      O.Satchmo -> case O.encoding opts of
         O.Binary -> MB.Matrix.handle ( \ b -> SAU.dict $ 2^(b-1) )  SA.direct opts
         O.Unary  -> MB.Matrix.handle SAU.dict SA.direct opts
         O.Interval_Plain ->
           MB.Matrix.handle SAI.dict_plain SA.direct opts 
         O.Interval_Fibs ->
           MB.Matrix.handle SAI.dict_fibs SA.direct opts 
         O.Interval_Twos ->
           MB.Matrix.handle SAI.dict_twos SA.direct opts 
         O.Interval_Threes ->
           MB.Matrix.handle SAI.dict_threes SA.direct opts 
      O.Boolector -> case O.encoding opts of
         O.Binary -> MB.Matrix.handle BAB.dict SA.direct opts
         O.Unary  -> MB.Matrix.handle BAU.dict SA.direct opts

-- matrix_arctic_dp :: Int -> Int -> TRS v c -> Work (TRS v x) Doc
matrix_arctic_dp opts dim bits = original_matrix_arctic_dp
      ( opts { O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dependency_pairs = True })

original_matrix_arctic_dp opts = 
      remover_arctic Top_Termination ( "matrix_arctic_dp" :: Doc ) CC.expand_all_trs
    $ case O.solver opts of
      O.Satchmo -> case O.encoding opts of
         O.Binary -> MB.Matrix.handle_dp ( \ b -> SAU.dict $ 2^(b-1) )  SA.direct opts
         O.Unary  -> MB.Matrix.handle_dp SAU.dict SA.direct opts
         O.Interval_Plain ->
           MB.Matrix.handle_dp SAI.dict_plain SA.direct opts 
         O.Interval_Fibs ->
           MB.Matrix.handle_dp SAI.dict_fibs SA.direct opts 
         O.Interval_Twos ->
           MB.Matrix.handle_dp SAI.dict_twos SA.direct opts 
         O.Interval_Threes ->
           MB.Matrix.handle_dp SAI.dict_threes SA.direct opts 
      O.Boolector -> case O.encoding opts of
         O.Binary -> MB.Matrix.handle_dp BAB.dict SA.direct opts
         O.Unary  -> MB.Matrix.handle_dp BAU.dict SA.direct opts

remover_arctic clm msg unpack h  sys = do
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
               , claim = claim out
               , reason = Matrix_Interpretation_Arctic m (Just usable) out
               }
                   )




