{-# language NoMonomorphismRestriction #-}
{-# language OverloadedStrings #-}

module MB.Arctic where

import TPDB.Data
import TPDB.Pretty

import qualified MB.Options as O
import qualified MB.Matrix 
import MB.Strategy
import MB.Proof
import qualified MB.Proof as P

import qualified Compress.Common as CC

import qualified Satchmo.SMT.Exotic.Arctic  as A
-- import qualified Satchmo.SMT.Exotic.Semiring.Arctic  as SA
import qualified Satchmo.SMT.Arctic  as SA
import Satchmo.SMT.Dictionary (Domain(..))

import Control.Concurrent.Combine.Computer
-- import Control.Concurrent.Combine.Lifter
import qualified Control.Concurrent.Combine as C

import qualified Control.Concurrent.Combine.Action as A
import Data.Hashable
import Control.Monad (when)


matrix_arctic_dp dim bits =
{-  C.apply ( transformer ( \ sys -> return $ smap CC.Orig sys ) 
                        ( \ sys proof -> proof ) )
   $ -}  original_matrix_arctic_dp
      ( O.options0 { O.dim = dim, O.bits = bits, O.compression = O.Simple, O.dp = True })


smap f sys = 
    sys { signature = {- map (fmap f) $ -} signature sys
        , rules = map ( \ u -> u { lhs = fmap f $ lhs u, rhs = fmap f $ rhs u } )
                $ rules sys }
        

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
remover_arctic msg unpack h = \ sys -> do
    (m, sys') <- A.io $ h sys
    when (length ( rules sys) == length (rules sys')) 
         $ error "huh"
    return $ \ k -> do
        out <- k sys'
        return $ "Arctic" <+> vcat [ "sys:" <+> pretty sys , pretty m, out ]
{-
        return $ Proof 
               { input = unpack sys
               , claim = Top_Termination
               , reason = Matrix_Interpretation_Arctic m out
               }
-}

