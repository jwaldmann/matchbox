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
import           CO4.Test.TermComp2014.PPrint
import           CO4.Test.TermComp2014.Allocators (allocator)
import           CO4.Test.TermComp2014.Standalone
import           CO4.Test.TermComp2014.Config

$( compileFile [Cache, ImportPrelude] "tc/CO4/Test/TermComp2014/Standalone.hs" )

main :: IO ()
main = do
  (config,filePath) <- parseConfig
  runFile config filePath

runFile :: Config -> FilePath -> IO ()
runFile config filePath = do
  (trs, symbolMap) <- parseTrs filePath

  putStrLn $ "Configuration:" 
  putStrLn $ show config

  putStrLn $ "Parsed:" 
  putStrLn $ pprintUnlabeledTrs symbolMap trs

  if not (isValidTrs trs)
    then putStrLn "invalid trs" >> exitFailure
    else do
      putStrLn $ "DP-TRS:"
      putStrLn $ pprintDPTrs (const "") symbolMap (dpProblem trs)

      putStrLn $ "Symbol Map:"
      putStrLn $ show symbolMap

      runN symbolMap config (dpProblem trs) >>= \case
        False -> putStrLn "don't know" >> exitFailure
        True  -> putStrLn "terminates" >> exitSuccess

runN :: SymbolMap -> Config -> DPTrs () -> IO Bool
runN symbolMap config dp = run1 symbolMap config dp >>= \case 
  Left dp' -> runN symbolMap config dp'
  Right r  -> return r

run1 :: SymbolMap -> Config -> DPTrs () -> IO (Either (DPTrs ()) Bool)
run1 symbolMap config dp =
  let sigmas    = assignments (modelBitWidth config) dp
      parameter = (dp, sigmas)
      alloc     = allocator config dp
  in do
    putStrLn $ "\n#######################################\n"
    putStrLn $ "TRS:"
    putStrLn $ pprintDPTrs (const "") symbolMap dp

    case hasMarkedRule dp of
      False -> return $ Right True
      _     -> solveAndTestP parameter alloc encConstraint constraint
       >>= \case
             Nothing -> return $ Right False
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

                  return $ Left dp'
               where
                 ints = intermediates dp labeledTrs orders
                 (dp', delete) = removeMarkedUntagged dp $ last ints

                 (labeledTrs,True) = makeLabeledTrs model dp sigmas
