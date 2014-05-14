-- improved main propram, should act as driver for a modular prover, 
-- see https://github.com/apunktbau/co4/issues/82

{-# language OverloadedStrings #-}
{-# language LambdaCase #-}
{-# language NoMonomorphismRestriction #-}

import CO4.Test.TermComp2014.Run (run1)
import CO4.Test.TermComp2014.Config 

import MB.Arctic
import MB.Logic
import qualified MB.Options as O

import qualified Compress.Common as CC
import qualified Compress.Simple as CS
import qualified Compress.PaperIter as CPI
import qualified Compress.Paper as CP

import TPDB.Data ( strict, rules, TRS, RS(..), separate )
import TPDB.Pretty 
import qualified TPDB.Input 
import TPDB.DP.Transform
import TPDB.DP.Usable
import TPDB.DP.Graph
import TPDB.Xml.Pretty ( document )
import Text.PrettyPrint.Leijen.Text (hPutDoc)

import Control.Monad ( guard, when, forM )
import Control.Applicative
import System.IO

import TPDB.CPF.Proof.Util (sortVariables)
import MB.Proof.Outline (outline)

-- https://github.com/apunktbau/co4/issues/81#issuecomment-41269315


import qualified MB.Proof as P

main :: IO ()
main = do
    (config,filePath) <- parseConfig
    trs <- TPDB.Input.get_trs filePath
    out <- run $ handle $ trs { rules = map sortVariables $ rules trs }
    case out of
        Nothing    -> do putStrLn "MAYBE"
        Just proof -> do  
            putStrLn "YES" 
            if outputCPF config
              then do
                displayIO stdout $ renderCompact $ document 
                              $ P.tox $ P.rtoc proof
                hPutStrLn stderr "YES"
                hPutDoc stderr $ pretty proof ; hPutStrLn stderr ""
                hPutStrLn stderr "Proof outline"
                hPutDoc stderr $ outline proof ; hPutStrLn stderr ""
              else do
                hPutDoc stdout $ pretty proof    ; hPutStrLn stdout ""
                hPutStrLn stdout "Proof outline"
                hPutDoc stdout $ outline proof ; hPutStrLn stdout ""

handle sys = do
    let dp = TPDB.DP.Transform.dp sys 
    proof <- handle_scc dp
    return $ P.Proof { P.input =  sys
                  , P.claim = P.Top_Termination
                  , P.reason = P.DP_Transform proof 
                  }

handle_scc  = orelse nomarkedrules 
            $ decomp handle_scc 
            $ orelse_andthen (for_usable_rules matrices) (apply handle_scc) 
            $ orelse_andthen semanticlabs (apply handle_scc)
            $ const reject

apply h =  \ (sys,f) -> do p <- h sys ; return $ f p 

nomarkedrules dp = do
    guard $ null $ filter strict $ rules dp 
    return $ P.Proof 
            { P.input = dp
            , P.claim = P.Top_Termination
            , P.reason = P.No_Strict_Rules 
            }

decomp succ fail sys = 
    let 
        cs = TPDB.DP.Graph.components sys 
        one_large_component = case cs of
            [ Right c ] | length (rules c) == length (rules sys) 
                -> True
            _   -> False
    in if  one_large_component then fail sys else do
        proofs <- forM cs $ \ case 
            Left v -> return $ Left v
            Right c -> Right <$> succ c
        return $ P.Proof { P.input = sys
                     , P.claim = P.Top_Termination
                     , P.reason = P.SCCs proofs
                     }

matrices  =  capture $ foldr1 orelse
    $ map (\(d,b) -> matrix_arc d b) 
         -- [(1,8),(2,6),(3,4),(4,2)]
         [(1,8),(2,4),(3,2)]

for_usable_rules method = \ sys -> do
    let restricted = TPDB.DP.Usable.restrict sys
    -- reduction pair is compatible with usables rules only
    (sys', f) <- method restricted
    -- but reconstruct all rules for returning the result
    let result = sys { rules = filter strict ( rules sys' )
               ++ filter (not . strict) ( rules sys ) }
    return ( result, f )

matrix_arc dim bits sys = do
    let c = O.Paper
        (cost, rs) = ( case c of
                       O.None -> CS.nocompress 
                       O.Simple -> CS.compress 
                       O.Paper -> CP.compress CP.Simple
                       O.PaperIter -> CP.compress CP.Iterative
                     ) $ rules sys
        csys = RS { rules = CC.roots rs
                               , separate = separate sys }
    (csys', f) <- mkWork ( matrix_arctic_dp dim bits ) csys
    let sys' = CC.expand_all_trs csys'
    return ( sys', f )

-- | this is the connection to tc/CO4/Test/TermComp2014/Main

semanticlabs = capture $ foldr1 orelse
    $ map (\(b,n) -> semanticlab $ defaultConfig 
        { modelBitWidth = b
        , useInterpretation = True , usePrecedence = False
        -- , useInterpretation = False , usePrecedence = True
        , numPrecedences = n
        , beVerbose = True 
        }) 
        [  (0,1), (1,1) , (1,2), (2,1), (2,2), (3,1), (3,2), (3,3) ]

semanticlab config = mkWork $ \ sys -> do
    out <- run1 config sys
    return $ case out of
        Nothing -> Nothing
        Just (sys', f) -> Just (sys', \ p -> P.Proof
            { P.input = sys
            , P.claim = P.Top_Termination
            , P.reason = P.Cpf2Cpf (text $ show config) f p
            } )
