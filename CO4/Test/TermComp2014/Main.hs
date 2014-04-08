{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

import           Prelude hiding (lex,lookup,length,iterate)
import           Control.Monad (forM_)
import           Control.Exception (assert)
import           System.Exit (exitSuccess, exitFailure)
import qualified Satchmo.Core.Decode 
import           CO4 hiding (Config)
import           CO4.Prelude
import           CO4.Test.TermComp2014.Util 
  (SymbolMap,parseTrs,assignments,dpProblem,dpToTrs,removeStrongDecreasingRules,hasMarkedRule)
import           CO4.Test.TermComp2014.PPrint
import           CO4.Test.TermComp2014.Allocators (allocator)
import           CO4.Test.TermComp2014.Standalone
import           CO4.Test.TermComp2014.Config

$( compileFile [Cache,ImportPrelude] "tc/CO4/Test/TermComp2014/Standalone.hs" )

main :: IO ()
main = do
  (config,filePath) <- parseConfig
  resultFile' config filePath

resultFile :: Int -> Int -> Int -> FilePath -> IO ()
resultFile modelBitWidth numPrecedences numPatterns = 
  resultFile' $ Config modelBitWidth numPrecedences numPatterns

resultFile' :: Config -> FilePath -> IO ()
resultFile' config filePath = do
  (trs, symbolMap) <- parseTrs filePath

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
  let sigmas    = assignments (modelBitWidth config) $ dpToTrs dp
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
             Just (model,filterAndPrecedences) -> assert (not $ null delete) $ 
               do putStrLn $ "Model:"
                  putStrLn $ pprintModel pprintMarkedSymbol symbolMap model

                  putStrLn $ "Labeled Trs:"
                  putStrLn $ pprintDPTrs pprintLabel symbolMap labeledTrs

                  forM_ (zip [1..] filterAndPrecedences) $ \(i,(filter,precedence)) -> do

                    putStrLn $ show i ++ ". Argument Filter:"
                    putStrLn $ pprintArgFilter pprintMarkedSymbol symbolMap filter

                    putStrLn $ show i ++ ". Filtered Trs:"
                    putStrLn $ pprintDPTrs pprintLabel symbolMap 
                             $ filterArgumentsDPTrs filter labeledTrs

                    putStrLn $ show i ++ ". Precedence:"
                    putStrLn $ pprintPrecedence pprintMarkedSymbol pprintLabel symbolMap precedence

                  putStrLn $ "\nDeleted:"
                  putStrLn $ unlines $ map (pprintDPRule (const "") symbolMap) delete

                  iterate symbolMap (i+1) config dp'
               where
                 (dp', delete) = removeStrongDecreasingRules dp labeledTrs filterAndPrecedences

                 labeledTrs = makeLabeledTrs model dp sigmas
