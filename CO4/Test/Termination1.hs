{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- module CO4.Test.WCB where
module Main where

import           Language.Haskell.TH (runIO)
import qualified Satchmo.Core.SAT.Minisat
import qualified Satchmo.Core.Decode 
import           CO4
import           CO4.Prelude
import           CO4.PreludeNat
import           CO4.Util (toBinary,fromBinary)

import qualified Data.Map as M
import Control.Monad ( void, forM )

import System.Environment (getArgs)
import System.IO

$( [d| constraint k u = case u of
            False -> k
            True  -> constraint (not k) False
   |] >>= compile [ ImportPrelude, Profile, Cache ] )

main = solveAndTestP False uBool
        encConstraint constraint >>= print

    
