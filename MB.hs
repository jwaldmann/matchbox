-- improved main propram, should act as driver for a modular prover, 
-- see https://github.com/apunktbau/co4/issues/82

{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

import           CO4.Test.TermComp2014.Config

import MB.Arctic
-- import MB.Strategy
import MB.Work
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
        Nothing -> do putStrLn "MAYBE"
        Just proof -> do  putStrLn "YES" ; print $ pretty proof    

strategy = andthen dptransform handle_sccs


-- this creates too much backtracking:
orelse_andthen p q r = orelse (andthen p q) r
-- TODO: the actual semantics we want is:
-- if p succeeds, then enter q (but never return to r)
-- this is similar to Parsec's behaviour
-- (if consume one letter, then must succeed)

handle_sccs  = traced "handle_scc"
    $ orelse nomarkedrules 
    $ andthen ( orelse usablerules pass )
    $ orelse_andthen decompose  handle_sccs
    $ orelse_andthen matrices handle_sccs
    $ const reject

matrices = traced "matrices"
    $ foldr1 orelse 
    $ for [(1,8),(2,6),(3,4),(4,3) ] $ \(dim,bits) -> matrix_arc dim bits

for = flip map

matrix_arc dim bits = 
      traced (unwords [ "matrices", show dim, show bits] )
    $ andthen (compressor O.Paper)
    $ andthen ( matrix_arctic_dp dim bits )
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


nomarkedrules = traced "nomarkedrules" $ \ sys -> do
    assert $ null $ filter strict $ rules sys
    return "has no marked rules"

dptransform = traced "dptransform" $ transformer
    ( \ sys -> return $ TPDB.DP.Transform.dp sys )
    ( \ sys proof -> vcat [ "DP transformation", "sys:" <+> pretty sys , "proof:" <+> proof ] )

-- | restrict to usable rules.
-- this transformer fails if all rules are usable
usablerules = traced "usablerules" $ transformer
    ( \ sys -> do
          let re = TPDB.DP.Usable.restrict sys 
          guard $ length (rules re) < length (rules sys)
          return re
    )
    ( \ sys proof ->  vcat [ "restrict to Usable rules", "sys:" <+> pretty sys , "proof:" <+> proof ] )

-- | compute EDG, split in components
-- | this transformer fails if the problem IS the single SCC
decompose = traced "decompose" $ transformers
    ( \ sys -> case TPDB.DP.Graph.components sys of
                   [ sys' ] | length (rules sys') == length (rules sys) -> Nothing
                   cs -> return cs )
    ( \ sys proofs -> "SCCs" <+> vcat [ "sys:" <+> pretty sys 
        , "number of SCCs" <+> pretty ( length proofs )
        , "proofs:" <+> vcat proofs ] )

