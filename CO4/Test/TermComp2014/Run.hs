{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module CO4.Test.TermComp2014.Run where

import           Control.Monad (when)
import           System.IO (hPutStrLn,stderr)
import qualified TPDB.Data as TPDB
import qualified TPDB.DP   as TPDB
import           TPDB.Pretty 
import qualified Satchmo.Core.Decode 
import           CO4 hiding (Config)
import           CO4.Prelude
import           CO4.Test.TermComp2014.Util 
import           CO4.Test.TermComp2014.Allocators (allocator)
import           CO4.Test.TermComp2014.Standalone 
import           CO4.Test.TermComp2014.Config
import           CO4.Test.TermComp2014.Proof.Dump (dumpTrs,dump)

$( compileFile [Cache, ImportPrelude] "tc/CO4/Test/TermComp2014/Standalone.hs" )

runN :: Config -> TPDB.TRS TPDB.Identifier (TPDB.Marked TPDB.Identifier) -> IO (Maybe Doc)
runN config trs =
  if not (isValidTrs dp)
  then hPutStrLn stderr "invalid trs" >> return Nothing
  else goDP dp
  where
    (dp, symbolMap) = fromTPDBTrs trs

    goDP dp = case hasMarkedRule dp of
      False -> return $ Just $ text "empty"
      True  -> run1' symbolMap config dp >>= \case
        Nothing              -> return Nothing
        Just (dp', _, proof) -> goDP dp' >>= return . fmap proof

{-
run1 :: 
     => Config -> TPDB.TRS v (Marked c) -> IO (Maybe (TPDB.TRS v (Marked c), Doc -> Doc))
     -}
run1 :: Config -> TPDB.TRS TPDB.Identifier (TPDB.Marked TPDB.Identifier) 
     -> IO (Maybe (TPDB.TRS TPDB.Identifier (TPDB.Marked TPDB.Identifier), Doc -> Doc))
run1 config trs = do
  let (dp@(Trs rules), symbolMap) = fromTPDBTrs trs

  run1' symbolMap config dp >>= \case
    Nothing -> return Nothing
    Just (_, delete, proof) ->
      let trs' = trs { TPDB.rules = do
                         (original, transformed) <- zip (TPDB.rules trs) rules
                         if transformed `elem` delete
                           then []
                           else return original
                 }
      in
        return $ Just (trs', proof)

run1' :: SymbolMap -> Config -> DPTrs () -> IO (Maybe (DPTrs (), [DPRule ()], Doc -> Doc))
run1' symbolMap config dp = 
  let sigmas    = assignments (modelBitWidth config) dp
      parameter = (dp, sigmas)
      alloc     = allocator config dp
  in do
    when (beVerbose config) $ dumpTrs config symbolMap dp 

    solveAndTestP parameter alloc encConstraint constraint
      >>= \case Nothing -> return Nothing
                Just proof@(Proof model orders) -> 
                  let (labeledTrs,True) = makeLabeledTrs model dp sigmas
                      ints              = intermediates dp labeledTrs orders
                      (dp',delete)      = removeMarkedUntagged dp $ last ints
                  in do
                    when (beVerbose $ config) $ dump config symbolMap dp proof
                    return $ Just (dp', delete, \p -> vcat [text (show proof), p])
