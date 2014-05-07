{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# language OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module CO4.Test.TermComp2014.Run where

import           Control.Monad (when)
import           System.IO (hPutStrLn,stderr)
import qualified TPDB.Data as T
import qualified TPDB.DP   as T
import qualified TPDB.CPF.Proof.Type as T
import qualified TPDB.CPF.Proof.Util as T
import qualified Satchmo.Core.Decode 
import           CO4 hiding (Config)
import           CO4.Prelude
import           CO4.Test.TermComp2014.Util 
import           CO4.Test.TermComp2014.Allocators (allocator)
import           CO4.Test.TermComp2014.Standalone 
import           CO4.Test.TermComp2014.Config
import           CO4.Test.TermComp2014.Proof.Dump (dumpTrs,dump)
import           CO4.Test.TermComp2014.Proof.CPF (toCpfProof)

$( compileFile [Cache, ImportPrelude] "tc/CO4/Test/TermComp2014/Standalone.hs" )

runN :: Config -> T.TRS T.Identifier T.Identifier -> IO (Maybe T.Proof)
runN config trs =
  if not (isValidTrs dp)
  then hPutStrLn stderr "invalid trs" >> return Nothing
  else goDP dp >>= return . fmap ( T.TrsTerminationProof 
                                 . T.DpTrans (T.DPS tpdbStrictRules) True )
  where
    tpdbDp          = T.dp trs
    tpdbStrictRules = filter T.strict $ toTPDBRules symbolMap (const . T.fromMarkedIdentifier) dp
    (dp, symbolMap) = fromTPDBTrs tpdbDp

    goDP dp = case hasMarkedRule dp of
      False -> return $ Just T.PIsEmpty
      True  -> run1' symbolMap config dp >>= \case
        Nothing              -> return Nothing
        Just (dp', _, proof) -> goDP dp' >>= return . fmap proof

run1 :: Config -> T.TRS T.Identifier (T.Marked T.Identifier) 
     -> IO (Maybe (T.TRS T.Identifier (T.Marked T.Identifier), T.DpProof -> T.DpProof ))
run1 config trs = do
  let (dp@(Trs rules), symbolMap) = fromTPDBTrs trs

  run1' symbolMap config dp >>= \case
    Nothing -> return Nothing
    Just (_, delete, proof) ->
      let trs' = trs { T.rules = do
                         (original, transformed) <- zip (T.rules trs) rules
                         if transformed `elem` delete
                           then []
                           else return original
                 }
      in
        return $ Just (trs', proof)

run1' :: SymbolMap -> Config -> DPTrs () 
      -> IO (Maybe (DPTrs (), [DPRule ()], T.DpProof -> T.DpProof ))
run1' symbolMap config dp = 
  let mValues   = modelValues $ modelBitWidth config
      parameter = (dp, mValues)
      alloc     = allocator config dp
  in do
    when (beVerbose config) $ dumpTrs config symbolMap dp 

    solveAndTestP parameter alloc encConstraint constraint
      >>= \case Nothing -> return Nothing
                Just proof@(Proof model orders) -> 
                  let (labeledTrs,True) = makeLabeledTrs model dp mValues
                      ints              = intermediates dp labeledTrs orders
                      (dp',delete)      = removeMarkedUntagged dp $ last ints
                  in do
                    when (beVerbose $ config) $ dump config symbolMap dp proof
                    return $ Just (dp', delete,  
                      toCpfProof symbolMap parameter proof
                      )
                       {-
                       vcat [ -- "input:" <+> pretty dp
                            -- , "symbolMap:" <+> pretty (M.toList $ M.mapKeys value symbolMap)
                               text $ show proof
                            ])
                            -}
