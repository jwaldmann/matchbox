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

import qualified Satchmo.SMT.Exotic.Arctic  as A
-- import qualified Satchmo.SMT.Exotic.Semiring.Arctic  as SA
import qualified Satchmo.SMT.Arctic  as SA
import Satchmo.SMT.Dictionary (Domain(..))

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe

import Data.Hashable
import Control.Monad (when)


-- matrix_arctic_dp :: Int -> Int -> TRS v c -> Work (TRS v x) Doc
matrix_arctic_dp dim bits = original_matrix_arctic_dp
      ( O.options0 { O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dp = True })

original_matrix_arctic_dp opts = 
      remover_arctic ( "matrix_arctic_dp" :: Doc ) CC.expand_all_trs
    $ MB.Matrix.handle_dp A.dict SA.direct opts


{-
remover_arctic :: ( )
        => Doc
        -> ( TRS v s -> TRS v u )
        -> ( TRS v s -> IO (Maybe (Interpretation u (A.Arctic Integer), TRS v t)))
        -> Lifter (TRS v s) (TRS v t) (Proof v u)
-}

remover_arctic msg unpack h  sys = do
    out <- h sys
    return $ case out of 
        Nothing -> Nothing
        Just (m, sys') -> do
            when (length ( rules sys) == length (rules sys')) 
                 $ error "huh"
            return ( sys'
                   , \ out ->  "Arctic" <+> vcat [ "sys:" <+> pretty sys , pretty m, out ]
                   )


{-
        return $ Proof 
               { input = unpack sys
               , claim = Top_Termination
               , reason = Matrix_Interpretation_Arctic m out
               }
-}

{-
ContT $ \ later -> do
    (m, sys') <- MaybeT $ h sys
    when (length ( rules sys) == length (rules sys')) 
         $ error "huh"
    out <- later sys'
    return $ "Arctic" <+> vcat [ "sys:" <+> pretty sys , pretty m, out ]
-}

{-
        return $ Proof 
               { input = unpack sys
               , claim = Top_Termination
               , reason = Matrix_Interpretation_Arctic m out
               }
-}

