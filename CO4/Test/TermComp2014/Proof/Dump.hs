{-# LANGUAGE StandaloneDeriving #-}
module CO4.Test.TermComp2014.Proof.Dump where

import Prelude hiding (print)
import Control.Monad (forM_)
import System.IO (hPutStrLn,stderr)
import CO4.Test.TermComp2014.PPrint
import CO4.Test.TermComp2014.Standalone
import CO4.Test.TermComp2014.Util
import CO4.Test.TermComp2014.Config

dumpTrs :: Config -> SymbolMap -> UnlabeledTrs -> IO ()
dumpTrs config symbolMap dp = do
  print $ "Configuration:" 
  print $ show config

  print $ "Trs:"
  print $ pprintUnlabeledTrs symbolMap dp

  print $ "Symbol Map:"
  print $ show symbolMap

dump :: Config -> SymbolMap -> UnlabeledTrs -> Proof -> IO ()
dump config symbolMap dp (Proof model orders) = do
  print $ "\n#######################################\n"

  print $ "Model:"
  print $ pprintModel pprintSymbolWithMark symbolMap model

  print $ "Labeled Trs:"
  print $ pprintLabeledTrs pprintLabel symbolMap $ ungroupTrs labeledTrs

  forM_ (zip [1..] orders ) $ \ (i,(_,order)) -> do
   case order of
    LinearInt int -> do
      print $ show i ++ ". Linear Interpretation:"
      print $ pprintLinearInt pprintSymbolWithMark pprintLabel symbolMap int

    FilterAndPrec filter precedence -> do
      print $ show i ++ ". Argument Filter:"
      print $ pprintArgFilter pprintSymbolWithMark pprintLabel symbolMap filter

      print $ show i ++ ". Filtered Trs:"
      print $ pprintLabeledTrs pprintLabel symbolMap 
            $ filterArgumentsLabeledTrs filter 
            $ ungroupTrs labeledTrs

      print $ show i ++ ". Precedence:"
      print $ pprintPrecedence pprintSymbolWithMark pprintLabel symbolMap precedence

  print $ "\nDeleted:"
  print $ unlines $ map (pprintUnlabeledRule symbolMap) delete

  -- FIXME: print information about intermediates
  forM_ ints $ \ int -> do
      print $ "\nIntermediate system:"
      print $ pprintTaggedLabeledTrs pprintLabel symbolMap int

  where
   ints              = intermediates dp labeledTrs orders
   (_, delete)       = removeMarkedUntagged dp $ last ints
   (labeledTrs,True) = makeLabeledTrs model dp $ modelValues $ modelBitWidth config

print :: String -> IO ()
print = hPutStrLn stderr
