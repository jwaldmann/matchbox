-- improved main propram, should act as driver for a modular prover, 
-- see https://github.com/apunktbau/co4/issues/82

{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

import           CO4.Test.TermComp2014.Config

import MB.Arctic
import MB.Strategy
import qualified MB.Options as O

import qualified Compress.Common as CC

import TPDB.Data ( strict, rules, TRS )
import TPDB.Pretty 
import qualified TPDB.Input 
import TPDB.DP.Transform
import TPDB.DP.Usable
import TPDB.DP.Graph

import Control.Monad ( guard, when )
import System.IO
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe

-- https://github.com/apunktbau/co4/issues/81#issuecomment-41269315
type Proof = Doc 

main :: IO ()
main = do
    (config,filePath) <- parseConfig
    trs <- TPDB.Input.get_trs filePath
    out <- work strategy trs 
    case out of
        Just proof -> do
            putStrLn "YES"
            print $ pretty proof    

strategy trs = do 
    dp <- dptransform trs ; handle_sccs dp

-- | on the compressed signature
matrices_compressed = foldr1 orelse 
         [  matrix_arctic_dp 1 8 
         ,  matrix_arctic_dp 2 6 
         , matrix_arctic_dp 3 4
         , matrix_arctic_dp 4 3
         ]

matrices =
      andthen  ( compressor O.Paper )
    $ andthen matrices_compressed
    $ transformer  ( \ sys -> return $ CC.expand_all_trs sys ) ( \ sys p -> p ) 



-- | this is the connection to tc/CO4/Test/TermComp2014/Main

semanticlab = \ sys -> ContT $ \ later -> do
    (sys', info) <- MaybeT $ do
        hPutStrLn stderr "send @sys@ to external prover of type  DP -> IO (Maybe (DP, Proof))"        
        return $ Just ( sys, "(dummy implemetation)" :: Doc )
    when (length ( rules sys) == length (rules sys')) $ error "huh"
    later sys'
{-
\ k -> do
        out <- k sys'
        return $ "Sem. Lab." <+> vcat [ "sys:" <+> pretty sys 
                                      , "sys':" <+> pretty sys' 
                                      , info, out ]
-}

handle_sccs = orelse nomarkedrules
    $ andthen ( orelse usablerules pass )
    $ committed decompose handle_sccs
--    $ committed matrices handle_sccs 
--    $ andthen semanticlab  
    $ handle_sccs

nomarkedrules = \ sys -> ContT $ \ later -> do
    MaybeT $ do
        hPutStrLn stderr $ show $ "call: nomarkedrules" <+> pretty sys
        if null $ filter strict $ rules sys
             then return $ Just "has no marked rules"
             else return Nothing

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

