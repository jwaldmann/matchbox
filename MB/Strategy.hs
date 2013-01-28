{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

module MB.Strategy where

import Control.Concurrent.Combine.Computer
import Control.Concurrent.Combine.Lifter
import qualified Control.Concurrent.Combine.Action as A

import TPDB.Data
import TPDB.Plain.Write
import TPDB.Pretty
import Text.PrettyPrint.HughesPJ
import Data.String

type Prover v s = Computer (RS v s) Doc

no_strict_rules :: (Pretty v, PrettyTerm s) 
    => Prover v s
no_strict_rules = \ sys -> 
    if null $ strict_rules sys
    then return $ vcat
             [ "system:" <+> pretty sys
             , "has no strict rules => is terminating"
             ]
    else fail "has strict rules"

transformer fore back = \ sys -> do
    case fore sys of
        Nothing -> fail "fore"
        Just sys' -> return $ \ later -> do
            out <- later sys'
            return $ back sys out

remover :: ( PrettyTerm s, Pretty v, Pretty b )
        => Doc
        -> ( RS v s -> IO (Maybe (b, RS v t)))
        -> Lifter (RS v s) (RS v t) Doc 
remover msg h = \ sys -> do
    (m, sys') <- A.io $ h sys
    return $ \ k -> do
        out <- k sys'
        return $ vcat [ "system:" <+> pretty sys
                  , msg <+> pretty m
                  , nest 2 out
                  ]