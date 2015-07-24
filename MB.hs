-- | improved main program,
-- should act as driver for a modular prover, 
-- see https://github.com/apunktbau/co4/issues/82

{-# language OverloadedStrings #-}
{-# language LambdaCase #-}
{-# language NoMonomorphismRestriction #-}

-- import CO4.Test.TermComp2014.Run (run1)
-- import CO4.Test.TermComp2014.Config 

import MB.Arctic
import MB.Natural
import MB.Logic
import MB.Complexity
import qualified MB.Closure.Enumerate as Clo
import qualified MB.Closure.Option as Clo
import qualified MB.Closure.Data as Clo

import MB.Time
import MB.Proof.Outline (headline)
import qualified MB.Options as O

import qualified Compress.Common as CC
import qualified Compress.Simple as CS
import qualified Compress.PaperIter as CPI
import qualified Compress.Paper as CP

import TPDB.Data ( strict, rules, TRS, RS(..)
  , separate, Identifier, mknullary )
import TPDB.Pretty
import MB.Pretty ((</>))
import qualified TPDB.Input 
import TPDB.DP.Transform
import TPDB.DP.Usable
import TPDB.DP.Graph
import TPDB.Mirror
import qualified TPDB.Convert
import TPDB.Xml.Pretty ( document )
import Text.PrettyPrint.Leijen.Text (hPutDoc)
import qualified Data.Map as M

import Control.Monad ( guard, when, forM, mzero )
import Control.Monad.IO.Class (liftIO)
import Control.Applicative
import System.IO
import Data.Time.Clock

import TPDB.CPF.Proof.Util (sortVariables)
import MB.Proof.Outline (outline)

import GHC.Conc

-- https://github.com/apunktbau/co4/issues/81#issuecomment-41269315


import qualified MB.Proof as P

import qualified MB.Proof.LaTeX as L
import qualified Text.LaTeX.Base as L
import qualified Text.LaTeX.Base.Pretty as L
import qualified Text.PrettyPrint.Free as L (displayIO, renderPretty)

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    hSetBuffering stderr LineBuffering

    (config0,filePath) <- O.parse -- parseConfig

    nc <- GHC.Conc.getNumCapabilities
    let config = config0 { O.cores = case O.cores config0 of
          Just nc -> Just nc ; Nothing -> Just nc
                        }
    
    trs <- TPDB.Input.get_trs filePath

    case O.mode config of
      O.Cycle_Termination -> must_be_srs trs
      _ -> return ()
    
    out <- run $ case O.dependency_pairs config of
      False -> handle_direct config trs
      True -> handle_both config trs      

    case out of
        Nothing    -> do putStrLn "MAYBE"
        Just proof -> do
          case O.mode config of
            O.Complexity {} -> do
              let Just (g, doc) = degree proof
              putStrLn $ "WORST_CASE(?,O(n^" ++ show g ++ "))"
              hPutDoc stdout $ "justification of degree:" </> doc 
              hPutStrLn stdout ""
            _ -> print $ headline proof  
          if O.cpf config
              then do
                displayIO stdout $ renderCompact $ document 
                              $ P.tox $ P.rtoc proof
                hPutStrLn stderr $ show $ headline proof
                hPutDoc stderr $ pretty proof ; hPutStrLn stderr ""
                hPutStrLn stderr "Proof outline"
                hPutDoc stderr $ outline proof ; hPutStrLn stderr ""
              else do
                hPutDoc stdout $ pretty proof    ; hPutStrLn stdout ""
                
                case O.latex config of
                  Nothing -> return ()
                  Just mf -> do
                    hPutStrLn stdout "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"
                    let ltx = L.documentclass [] "article"
                              L.<> L.usepackage [] "amsmath"
                              L.<> L.document ( L.texy proof )
                        doc = L.docLaTeX ltx
                    h <- case mf of
                      Nothing -> return stdout
                      Just f -> do
                        hPutStrLn stdout $ "latex output to: " ++ show f
                        openFile f WriteMode
                    L.displayIO h $ L.renderPretty 0.4 80 doc
                    hFlush h
                    hPutStrLn stdout "\n%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"

                hPutStrLn stdout "Proof outline"
                hPutDoc stdout $ outline proof ; hPutStrLn stdout ""

must_be_srs trs = case TPDB.Convert.trs2srs trs of
  Just _ -> return ()
  Nothing -> error "for cycle termination, input must be SRS"
        

handle_both config sys = case TPDB.Mirror.mirror sys of
     Nothing -> handle_dp config sys
     Just sys' ->
       let Just nc = O.cores config
           config2 = config { O.cores = Just $ max 1 $ div nc 2 }
       in  parallel_or0 
         [ handle_dp config2 sys
         , do p <- handle_dp config2 sys' 
              return $ P.Proof { P.input = sys
                     , P.claim = P.Termination
                     , P.reason = P.Mirror_Transform p 
                     }
         ]

handle_direct conf = case O.direction conf of
  O.Yeah -> handle_direct_yeah conf
  O.Noh  -> handle_direct_noh conf
  O.Both -> orelse nostrictrules
    $ andthen0 ( capture $ parallel_or
                 [ \ x -> Right <$> matrices_direct conf x
                 , \ x -> Left  <$> handle_direct_noh conf x
                 ] )
    $ \ x -> case x of
                 Left p -> return p
                 Right q -> apply (handle_direct conf) q



handle_direct_noh conf sys = 
    case TPDB.Convert.trs2srs sys of
      Nothing -> mzero
      Just srs -> do
        let ((fore,back), rules) = Clo.fromSRS_withmap srs
            f i = mknullary [ fore M.! i ]
            doc = text $ unwords $ words $ show $ pretty fore
            certs = do
              c <- Clo.enumerate Clo.Both Nothing rules
              Clo.loop_certificates c ++
                case O.mode conf of
                  O.Cycle_Termination -> Clo.cycle_loop_certificates c 
                  _ -> []
        search_start <- liftIO getCurrentTime          
        case certs of
          [] -> mzero
          c : _ -> do
            search_end <- liftIO getCurrentTime
            let t = Time { start = search_start
                         , end = search_end
                         }
            let clm = case O.mode conf of
                 O.Termination -> P.Non_Termination
                 O.Cycle_Termination -> P.Cycle_Non_Termination
            return $ P.Proof
             { P.input = sys
             , P.claim = clm
             , P.reason = P.Equivalent (  "rename letters" <+> doc )
                          $ P.Proof
                          { P.input = fmap (fmap f) sys
                          , P.claim = clm
                          , P.reason = P.Nonterminating
                              $ c { Clo.time = Just t }
                          }
             }


handle_direct_yeah config = orelse nostrictrules
    $ andthen0 ( matrices_direct config )
    $ apply ( handle_direct config )
  
handle_dp config sys = do
    let dp = TPDB.DP.Transform.dp sys 
    proof <- handle_scc config dp
    return $ P.Proof { P.input =  sys
                  , P.claim = P.Top_Termination
                  , P.reason = P.DP_Transform proof 
                  }

fuse opts = case O.usable_rules opts of
  True -> for_usable_rules
  False -> id

handle_scc config  = orelse nomarkedrules 
            $ decomp (handle_scc config)

            -- $ andthen0 ( parallel_or [ for_usable_rules matrices , semanticlabs ])
            $ andthen0 (fuse config $ matrices_dp config) 
            $  apply (handle_scc config)

--            $ orelse_andthen (for_usable_rules matrices) (apply handle_scc) 
--            $ orelse_andthen semanticlabs (apply handle_scc)
--             $ const reject

apply h =  \ (sys,f) -> do p <- h sys ; return $ f p 

nomarkedrules dp = do
    guard $ null $ filter strict $ rules dp 
    return $ P.Proof 
            { P.input = dp
            , P.claim = P.Top_Termination
            , P.reason = P.No_Strict_Rules 
            }

nostrictrules dp = do
    guard $ null $ filter strict $ rules dp 
    return $ P.Proof 
            { P.input = dp
            , P.claim = P.Termination
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


matrices_direct config =
  let Just nc = O.cores config in
  capture $ bounded_parallel_or nc $ do
      d <- [ 1 .. ]
      c <- [ 0 .. O.constraints config ]
      let b = O.bits config
      do
          guard$ O.use_arctic config
          return $ matrix_arc_direct ( config { O.constraints = 0 } ) d b 
        ++ do
          guard $ O.use_natural config
          c <- [ 0 .. O.constraints config ]
          return $ matrix_nat_direct ( config { O.constraints = c}) d b 

      
parameters config = do
  dc <- [1 .. ]
  c <- [ {- 0 .. -} O.constraints config ]
  let d = dc -- - c
  guard $ d > 0
  return ( d, c, O.bits config )

matrices_dp config = 
  let Just nc = O.cores config in
  capture $ bounded_parallel_or nc $ do
      let b = O.bits config
      d <- [1 .. ]
      do
          guard$ O.use_arctic config
          return $ matrix_arc_dp ( config { O.constraints = 0 } ) d b 
        ++ do
          guard $ O.use_natural config
          c <- [ 0 .. O.constraints config ]
          return $ matrix_nat_dp ( config { O.constraints = c}) d b 



for_usable_rules method = \ sys -> do
    let restricted = TPDB.DP.Usable.restrict sys
    -- reduction pair is compatible with usables rules only
    (sys', f) <- method restricted
    -- but reconstruct all rules for returning the result
    let result = sys { rules = filter strict ( rules sys' )
               ++ filter (not . strict) ( rules sys ) }
    return ( result, f )

matrix_arc_dp config dim bits sys = do
    let c = O.Paper
        (cost, rs) = ( case c of
                       O.None -> CS.nocompress 
                       O.Simple -> CS.compress 
                       O.Paper -> CP.compress CP.Simple
                       O.PaperIter -> CP.compress CP.Iterative
                     ) $ rules sys
        csys = RS { rules = CC.roots rs
                               , separate = separate sys }
    (csys', f) <- mkWork ( matrix_arctic_dp config dim bits ) csys
    let sys' = CC.expand_all_trs csys'
    return ( sys', f )

matrix_arc_direct config dim bits sys = do
    let c = O.Paper
        (cost, rs) = ( case c of
                       O.None -> CS.nocompress 
                       O.Simple -> CS.compress 
                       O.Paper -> CP.compress CP.Simple
                       O.PaperIter -> CP.compress CP.Iterative
                     ) $ rules sys
        csys = RS { rules = CC.roots rs
                               , separate = separate sys }
    (csys', f) <- mkWork ( matrix_arctic_direct config dim bits ) csys
    let sys' = CC.expand_all_trs csys'
    return ( sys', f )

matrix_nat_direct config dim bits sys = do
    let c = O.Paper
        (cost, rs) = ( case c of
                       O.None -> CS.nocompress 
                       O.Simple -> CS.compress 
                       O.Paper -> CP.compress CP.Simple
                       O.PaperIter -> CP.compress CP.Iterative
                     ) $ rules sys
        csys = RS { rules = CC.roots rs
                               , separate = separate sys }
    (csys', f) <- mkWork ( matrix_natural_direct config dim bits ) csys
    let sys' = CC.expand_all_trs csys'
    return ( sys', f )
    

matrix_nat_dp config dim bits sys = do
    let c = O.Paper
        (cost, rs) = ( case c of
                       O.None -> CS.nocompress 
                       O.Simple -> CS.compress 
                       O.Paper -> CP.compress CP.Simple
                       O.PaperIter -> CP.compress CP.Iterative
                     ) $ rules sys
        csys = RS { rules = CC.roots rs
                               , separate = separate sys }
    (csys', f) <- mkWork ( matrix_natural_dp config dim bits ) csys
    let sys' = CC.expand_all_trs csys'
    return ( sys', f )

-- | this is the connection to tc/CO4/Test/TermComp2014/Main

{-

semanticlabs = capture $ foldr1 orelse
    $ map (\(b,n) -> semanticlab $ defaultConfig 
        { modelBitWidth = b
        , useInterpretation = True , usePrecedence = False
        -- , useInterpretation = False , usePrecedence = True
        , numPrecedences = n
        , numPatterns = succ b
        , beVerbose = True 
        }) 
      $ do b <- [0 .. ] ; n <- [ 1 .. 2 ^ b ] ; return (b,n)

semanticlab config = mkWork $ \ sys -> do
    out <- run1 config sys
    return $ case out of
        Nothing -> Nothing
        Just (sys', f) -> Just (sys', \ p -> P.Proof
            { P.input = sys
            , P.claim = P.Top_Termination
            , P.reason = P.Cpf2Cpf (text $ show config) f p
            } )

-}
