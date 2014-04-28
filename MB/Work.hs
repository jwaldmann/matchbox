{-# language NoMonomorphismRestriction #-}
{-# language StandaloneDeriving #-}
{-# language ScopedTypeVariables #-}

module MB.Work where


import Control.Monad.Trans
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Maybe
import Control.Applicative

import System.IO

type Work a r =  ContT r (MaybeT IO) a 

mkWork f = \ x -> ContT $ \ later -> do
    (y, g) <- MaybeT $ f x
    out <- later y
    return $ g out

work :: (a -> Work b b) ->  a -> IO (Maybe b)
work w x = runMaybeT $ runContT (w x) return

assert :: Bool -> Work () r
assert f = if f then return () else reject 

reject = ContT $ \ later -> MaybeT $ return Nothing

traced s w = \ x -> do liftIO $ hPutStrLn stderr s ; w x

getC p = ContT $ \ k -> runContT (p k) k
withC p k = \ x -> ContT $ \ k' -> runContT (p x) k

andthen :: (a -> Work b r) -> ( b -> Work c r ) -> ( a -> Work c r )
andthen p q = \ x -> p x >>= q

orelse :: (a -> Work b r) -> (a -> Work b r) -> ( a -> Work b r )
orelse p q = \  x -> ContT $ \ later -> MaybeT $ do
    out <- runMaybeT $ runContT ( p x ) later
    case out of 
        Nothing -> runMaybeT $ runContT  ( q x ) later
        Just res -> return out

-- this creates too much backtracking:
-- orelse_andthen p q r = orelse (andthen p q) r

-- TODO: the actual semantics we want is:
-- if p succeeds, then enter q (but never return to r)
-- this is similar to Parsec's behaviour
-- (if consume one letter, then must succeed)

orelse_andthen :: (a -> Work b r) -> (b -> Work c r) -> (a -> Work c r) -> (a -> Work c r)
orelse_andthen p q r = \ x -> getC $ \ top -> 
    orelse (andthen p (withC q top)) r x
        
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





