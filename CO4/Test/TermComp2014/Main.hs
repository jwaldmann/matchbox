{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

import           Prelude hiding (lex,lookup,length,iterate)
import           Control.Monad (forM_)
import           Control.Exception (assert)
import           System.Exit (exitSuccess, exitFailure)
import qualified Satchmo.Core.Decode 
import           CO4 hiding (Config)
import           CO4.Prelude
import           CO4.Test.TermComp2014.Util 
  (SymbolMap,parseTrs,assignments,dpProblem,intermediates,removeMarkedUntagged,hasMarkedRule,ungroupTrs)
import           CO4.Test.TermComp2014.PPrint
import           CO4.Test.TermComp2014.Allocators (allocator)
import           CO4.Test.TermComp2014.Standalone
import           CO4.Test.TermComp2014.Config

$( compileFile [Cache, Dump "/tmp/tc", ImportPrelude] "tc/CO4/Test/TermComp2014/Standalone.hs" )

main :: IO ()
main = do
  (config,filePath) <- parseConfig
  resultFile' config filePath

resultFile :: Int -> Int -> Int -> Int -> FilePath -> IO ()
resultFile mBW numPrecs numPats pBW = 
  resultFile' $ defaultConfig { modelBitWidth            = mBW
                              , numPrecedences           = numPrecs
                              , numPatterns              = numPats
                              , precedenceDomainBitWidth = pBW
                              }

resultFile' :: Config -> FilePath -> IO ()
resultFile' config filePath = do
  (trs, symbolMap) <- parseTrs filePath

  putStrLn $ "Configuration:" 
  putStrLn $ show config

  putStrLn $ "Parsed:" 
  putStrLn $ pprintUnlabeledTrs symbolMap trs

  putStrLn $ "DP-TRS:"
  putStrLn $ pprintDPTrs (const "") symbolMap (dpProblem trs)

  putStrLn $ "Symbol Map:"
  putStrLn $ show symbolMap

  iterate symbolMap 1 config (dpProblem trs) >>= \case
    False -> putStrLn "don't know" >> exitFailure
    True  -> putStrLn "terminates" >> exitSuccess

iterate :: SymbolMap -> Int -> Config -> DPTrs () -> IO Bool
iterate symbolMap i config dp = 
  let sigmas    = assignments (modelBitWidth config) dp
      parameter = (dp, sigmas)
      alloc     = allocator config dp
  in do
    putStrLn $ "\n## " ++ show i ++ ". Iteration ##########################\n"
    putStrLn $ "TRS:"
    putStrLn $ pprintDPTrs (const "") symbolMap dp

    case hasMarkedRule dp of
      False -> return True
      _     -> solveAndTestP parameter alloc encConstraint constraint
       >>= \case
             Nothing -> return False
             Just (Proof model orders) -> assert (not $ null delete) $ 
               do putStrLn $ "Model:"
                  putStrLn $ pprintModel pprintMarkedSymbol symbolMap model

                  putStrLn $ "Labeled Trs:"
                  putStrLn $ pprintDPTrs pprintLabel symbolMap $ ungroupTrs labeledTrs

                  forM_ (zip [1..] orders ) $ \ (i,(usable,order)) -> do
                   case order of
                    LinearInt int -> do
                      putStrLn $ show i ++ ". Linear Interpretation:"
                      putStrLn $ pprintLinearInt pprintMarkedSymbol pprintLabel symbolMap int

                    FilterAndPrec filter precedence -> do
                      putStrLn $ show i ++ ". Argument Filter:"
                      putStrLn $ pprintArgFilter pprintMarkedSymbol pprintLabel symbolMap filter

                      putStrLn $ show i ++ ". Filtered Trs:"
                      putStrLn $ pprintDPTrs pprintLabel symbolMap 
                               $ filterArgumentsDPTrs filter 
                               $ ungroupTrs labeledTrs

                      putStrLn $ show i ++ ". Precedence:"
                      putStrLn $ pprintPrecedence pprintMarkedSymbol pprintLabel symbolMap precedence

                  putStrLn $ "\nDeleted:"
                  putStrLn $ unlines $ map (pprintDPRule (const "") symbolMap) delete

                  -- FIXME: print information about intermediates
                  forM_ ints $ \ int -> do
                      putStrLn $ "\nIntermediate system:"
                      putStrLn $ pprintTaggedDPTrs pprintLabel symbolMap int

                  iterate symbolMap (i+1) config dp'
               where
                 ints = intermediates dp labeledTrs orders
                 (dp', delete) = removeMarkedUntagged dp $ last ints

                 (labeledTrs,True) = makeLabeledTrs model dp sigmas
