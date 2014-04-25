{-# language NoMonomorphismRestriction #-}

module MB.Strategy where

import qualified MB.Proof as P
import qualified Control.Concurrent.Combine as C
import qualified Control.Concurrent.Combine.Lifter as L
import qualified Control.Concurrent.Combine.Action as A

import TPDB.Data
import TPDB.Pretty

import qualified Compress.Common as CC
import qualified Compress.Simple as CS
import qualified Compress.PaperIter as CPI
import qualified Compress.Paper as CP

import qualified MB.Options as O

import Data.Hashable

transformer fore back = \ sys -> do
    case fore sys of
        Nothing -> fail "fore"
        Just sys' -> return $ \ later -> do
            out <- later sys'
            return $ back sys out

-- | apply the continuation to each sub-result
transformers fore back = \ sys -> do
    case fore sys of
        Nothing -> fail "fore"
        Just syss' -> return $ \ later -> do
            outs <- mapM later syss'
            return $ back sys outs

-- like C.orelse ( C.apply foo bar ) baz
-- but if foo is successful, then no backtrack
committed :: L.Lifter a b r -> C.Computer b r -> C.Computer a r -> C.Computer a r
committed foo bar baz = \ sys -> A.Action $ do
    out <- A.run $ foo sys
    case out of
         Just eatcont -> A.run $ eatcont bar
         Nothing -> A.run $ baz sys

{-
\ sys -> do
    mk <- foo sys
    case mk of
        Nothing -> baz sys
        Just k -> k bar
-}

pass = transformer ( \ sys -> return sys ) ( \ sys proof -> proof )

compressor c = transformer 
    ( \ sys -> let (cost, rs) = ( case c of
                       O.None -> CS.nocompress 
                       O.Simple -> CS.compress 
                       O.Paper -> CP.compress CP.Simple
                       O.PaperIter -> CP.compress CP.Iterative
                     ) $ rules sys
               in  return $ RS { rules = CC.roots rs
                               , separate = separate sys }
    )
    ( \ sys proof -> proof )
{-
    ( \ sys proof -> P.Proof
         { P.input = sys
         , P.claim = P.Termination
         , P.reason = 
              P.Equivalent (text $ show c) proof
         } )
-}

