{-# language NoMonomorphismRestriction #-}

module MB.Logic where 

import Control.Monad.Logic
import Control.Applicative 

import Control.Concurrent.Async as CCA
import Control.Concurrent.Chan
import Control.Exception.Base ( finally )
import System.IO

run r = do
    out <- observeManyT 1 r
    return $ case out of
        [] ->  Nothing
        x : _ -> Just x

work w x = do
    out <- observeManyT 1 $ w x
    return $ case out of
        [] ->  Nothing
        (x,f) : _ -> Just $ f x

traced s w = \ x -> do liftIO $ hPutStrLn stderr s ; w x

mkWork :: (a -> IO (Maybe b)) -> (a -> LogicT IO b)
mkWork f = \ x -> LogicT $ \ succ fail -> do
    out <- f x
    case out of
        Nothing -> fail
        Just y -> succ y fail

success = \ x -> return (x, id)

andthen0 p q x = p x >>= q

andthen p q = \ x -> do 
    (y,f) <- p x ; (z, g) <- q y ; return (z, f . g)

orelse p q = \ x -> do mplus (p x) (q x)

sequential_or ps = foldl1 orelse ps

-- | start processes in parallel.
-- the first one that completes successfully
-- will give the overall result, and cancel the others.
-- FIXME: this is (1) ugly, and (2) most probably wrong
-- (what happens if such a group is cancelled?
-- will it cancel all its members? I don't think so)
parallel_or0 ps = LogicT $ \ succ fail -> do
    ch <- newChan
    as <- forM ps $ \ p -> async $ do 
         m <- runLogicT p
               ( \ r f -> return $ Just r) (return Nothing)
         writeChan ch m
    let work k = if k <= 0 
                 then return Nothing
                 else do r <- readChan ch
                         case r of
                             Nothing -> work (k-1)
                             Just x ->  return $ Just x
    m <- (work $ length as) `finally` (forM_ as cancel) 
    case m of Nothing -> fail ; Just x -> succ x fail

parallel_or ps = \ x -> parallel_or0 $ map ( \ p -> p x ) ps

capture p =  \ x -> once ( p x)

orelse_andthen p q r = \ x -> ifte (p x) q (r x)

reject = mzero

multi p = \ xs -> do
    yfs <- forM xs p
    return ( map fst yfs
           , \ ps -> zipWith ($) (map snd yfs) ps
           )

transformer fore back = mkWork $ \ sys -> return $
     case fore sys of
         Nothing   -> Nothing
         Just sys' -> Just ( sys' , back sys )
