-- improved main propram, should act as driver for a modular prover, 
-- see https://github.com/apunktbau/co4/issues/82

{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

import           CO4.Test.TermComp2014.Config

import MB.Arctic
import MB.Strategy
import qualified MB.Options as O

import qualified Control.Concurrent.Combine as C
import qualified Control.Concurrent.Combine.Action as A

import qualified Compress.Common as CC

import TPDB.Data ( strict, rules )
import TPDB.Pretty 
import qualified TPDB.Input 
import TPDB.DP.Transform
import TPDB.DP.Usable
import TPDB.DP.Graph

import Control.Monad ( guard, when )
import System.IO

-- https://github.com/apunktbau/co4/issues/81#issuecomment-41269315
type Proof = Doc 

main :: IO ()
main = do
    (config,filePath) <- parseConfig
    trs <- TPDB.Input.get_trs filePath
    out <- A.run ( strategy trs ) 
    case out of
        Just proof -> do
            putStrLn "YES"
            print $ pretty proof    

strategy = C.apply dptransform handle_sccs

-- | on the compressed signatur
matrices_compressed = foldr1 C.orelse 
         [  matrix_arctic_dp 1 8 
         ,  matrix_arctic_dp 2 6 
         , matrix_arctic_dp 3 4
         , matrix_arctic_dp 4 3
         ]

matrices next = 
      C.apply ( compressor O.Paper )
    $ C.apply matrices_compressed
    $ C.apply ( transformer  ( \ sys -> return $ CC.expand_all_trs sys ) ( \ sys p -> p ) )
    $ next


-- | this is the connection to tc/CO4/Test/TermComp2014/Main
semanticlab = \ sys -> do
    (sys', info) <- A.io $ do
        hPutStrLn stderr "send @sys@ to external prover of type  DP -> IO (Maybe (DP, Proof))"        
        return $ Just ( sys, "(dummy implemetation)"  )
    when (length ( rules sys) == length (rules sys')) $ error "huh"
    return $ \ k -> do
        out <- k sys'
        return $ "Sem. Lab." <+> vcat [ "sys:" <+> pretty sys 
                                      , "sys':" <+> pretty sys' 
                                      , info, out ]

handle_sccs = C.orelse nomarkedrules
    $ C.apply ( C.orelse usablerules pass )
    $ committed decompose handle_sccs

    -- $ C.apply ( C.orelse  matrices semanticlab ) 
    $ matrices handle_sccs 

nomarkedrules = \ sys -> 
    if null $ filter strict $ rules sys
    then return $ "has no marked rules"
    else fail "has strict rules"

dptransform = transformer
    ( \ sys -> return $ TPDB.DP.Transform.dp sys )
    ( \ sys proof -> vcat [ "DP transformation", "sys:" <+> pretty sys , "proof:" <+> proof ] )

-- | restrict to usable rules.
-- this transformer fails if all rules are usable
usablerules = transformer
    ( \ sys -> do
          let re = TPDB.DP.Usable.restrict sys 
          guard $ length (rules re) < length (rules sys)
          return re
    )
    ( \ sys proof ->  vcat [ "restrict to Usable rules", "sys:" <+> pretty sys , "proof:" <+> proof ] )

-- | compute EDG, split in components
-- | this transformer fails if the problem IS the single SCC
decompose = transformers
    ( \ sys -> case TPDB.DP.Graph.components sys of
                   [ sys' ] | length (rules sys') == length (rules sys) -> Nothing
                   cs -> return cs )
    ( \ sys proofs -> "SCCs" <+> vcat [ "sys:" <+> pretty sys 
        , "number of SCCs" <+> pretty ( length proofs )
        , "proofs:" <+> vcat proofs ] )

