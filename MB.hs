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

import Control.Monad ( guard )


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

removerules = foldr1 C.orelse 
         [  matrix_arctic_dp 1 8 
         ,  matrix_arctic_dp 2 6 
         , matrix_arctic_dp 3 4
         , matrix_arctic_dp 4 3
         ]

handle_sccs = C.orelse nomarkedrules
    $ C.apply ( C.orelse usablerules pass )
    -- $ C.orelse ( C.apply decompose  handle_sccs )
    $ committed decompose handle_sccs
    $ C.apply ( compressor O.Paper )
    $ C.apply removerules 
    $ C.apply ( transformer  ( \ sys -> return $ CC.expand_all_trs sys ) 
                ( \ sys p -> p ) )
    $ handle_sccs

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

