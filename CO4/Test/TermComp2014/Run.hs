{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# language OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module CO4.Test.TermComp2014.Run where

import qualified TPDB.Data as TPDB
import qualified TPDB.DP   as TPDB
import TPDB.Pretty 
import qualified Satchmo.Core.Decode 
import           CO4 hiding (Config)
import           CO4.Prelude
import           CO4.Test.TermComp2014.Util 
import           CO4.Test.TermComp2014.Allocators (allocator)
import           CO4.Test.TermComp2014.Standalone 
import           CO4.Test.TermComp2014.Config
import System.IO
import Data.Maybe (catMaybes)
import qualified Data.Map as M

$( compileFile [Cache, ImportPrelude] "tc/CO4/Test/TermComp2014/Standalone.hs" )

{-
run1 :: 
     => Config -> TPDB.TRS v (Marked c) -> IO (Maybe (TPDB.TRS v (Marked c), Doc -> Doc))
     -}
run1 :: Config -> TPDB.TRS TPDB.Identifier (TPDB.Marked TPDB.Identifier) 
     -> IO (Maybe (TPDB.TRS TPDB.Identifier (TPDB.Marked TPDB.Identifier), Doc -> Doc))
run1 config trs = do
  hPutStrLn stderr $ show $ pretty trs

  let (dp@(Trs rules), symbolMap) = transformTrs trs
      sigmas    = assignments (modelBitWidth config) dp
      parameter = (dp, sigmas)
      alloc     = allocator config dp

  hPutStrLn stderr $ show dp

  solveAndTestP parameter alloc encConstraint constraint
       >>= \case
             Nothing -> return Nothing
             Just proof@(Proof model orders) -> 
               let (labeledTrs,True) = makeLabeledTrs model dp sigmas
                   ints = intermediates dp labeledTrs orders
                   (dp', delete) = removeMarkedUntagged dp $ last ints

                   trs' = trs {TPDB.rules = do
                            (or,tr) <- zip (TPDB.rules trs) rules
                            if tr `elem` delete
                              then []
                              else return or
                          }
               in do
                hPutStrLn stderr $ show proof
                return $ Just (trs', \p -> 
                       vcat [ "input:" <+> pretty trs
                            , "symbolMap:" <+> 
                              pretty (M.toList $ M.mapKeys value symbolMap)
                            , text $ show proof
                            , p
                            ])

