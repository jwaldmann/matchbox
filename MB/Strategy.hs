{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

module MB.Strategy where

import MB.Proof

import Control.Concurrent.Combine.Computer
import Control.Concurrent.Combine.Lifter
import qualified Control.Concurrent.Combine.Action as A

import TPDB.Data hiding  (Termination)
import TPDB.Plain.Write
import TPDB.Pretty
import Text.PrettyPrint.HughesPJ
import Data.String

type Prover v s = Computer (TRS v s) (Proof v s)


no_strict_rules top unpack = \ sys -> 
    if null $ strict_rules sys
    then return $ Proof 
            { input = unpack sys
            , claim = if top then Top_Termination
                      else Termination
            , reason = No_Strict_Rules }
    else fail "has strict rules"

transformer fore back = \ sys -> do
    case fore sys of
        Nothing -> fail "fore"
        Just sys' -> return $ \ later -> do
            out <- later sys'
            return $ back sys out

{-
remover_natural :: ( PrettyTerm s, Pretty v, Pretty b )
        => Doc
        -> ( TRS v t -> TRS v s )
        -> ( RS v s -> IO (Maybe (b, TRS v t)))
        -> Lifter (TRS v s) (TRS v t) (Proof v s)
-}
remover_natural msg unpack h = \ sys -> do
    (m, sys') <- A.io $ h sys
    return $ \ k -> do
        out <- k sys'
        return $ Proof 
               { input = unpack sys
               , claim = Termination
               , reason = Matrix_Interpretation_Natural m out
               }

remover_arctic msg unpack h = \ sys -> do
    (m, sys') <- A.io $ h sys
    return $ \ k -> do
        out <- k sys'
        return $ Proof 
               { input = unpack sys
               , claim = Top_Termination
               , reason = Matrix_Interpretation_Arctic m out
               }
