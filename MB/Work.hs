{-# language NoMonomorphismRestriction #-}
{-# language StandaloneDeriving #-}
{-# language ScopedTypeVariables #-}

module MB.Work where

import qualified MB.Proof as P
import qualified Control.Concurrent.Combine as C
import qualified Control.Concurrent.Combine.Lifter as L
import qualified Control.Concurrent.Combine.Action as A

import Control.Monad.Trans
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe
import Control.Applicative

import TPDB.Data
import TPDB.Pretty

import qualified Compress.Common as CC
import qualified Compress.Simple as CS
import qualified Compress.PaperIter as CPI
import qualified Compress.Paper as CP

import qualified MB.Options as O
import System.IO
import Data.Hashable

type Work a r =  ContT r (MaybeT IO) a 

work :: (a -> Work b b) ->  a -> IO (Maybe b)
work w x = runMaybeT $ runContT (w x) return

assert :: Bool -> Work () r
assert f = if f then return () else reject 

reject = ContT $ \ later -> MaybeT $ return Nothing

traced s w = \ x -> do liftIO $ hPutStrLn stderr s ; w x

andthen :: (a -> Work b r) -> ( b -> Work c r ) -> ( a -> Work c r )
andthen p q = \ x -> p x >>= q

orelse :: (a -> Work b r) -> (a -> Work b r) -> ( a -> Work b r )
orelse p q = \  x -> ContT $ \ later -> MaybeT $ do
    out <- runMaybeT $ runContT ( p x ) later
    case out of 
        Nothing -> runMaybeT $ runContT  ( q x ) later
        Just res -> return out

committed :: (a -> Work b r) -> (b -> Work c r) -> (a -> Work c r) -> (a -> Work c r)
committed foo bar baz = orelse (andthen foo bar) baz


        
transformer :: (a -> Maybe b) -> (a -> r ->  r)
            -> a -> Work b r 
transformer fore back = \ sys -> ContT $ \ later -> 
    case fore sys of
        Nothing -> fail "fore"
        Just sys' -> do 
            out <- later sys'
            return $ back sys out

-- | apply the continuation to each sub-result
transformers :: (a -> Maybe [b]) -> (a -> [r] ->  r)
            -> a -> Work b r 
transformers fore back = \ sys -> ContT $ \ later -> 
    case fore sys of
        Nothing -> fail "fore"
        Just syss' ->  do
            outs <- mapM later syss'
            return $ back sys outs


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

