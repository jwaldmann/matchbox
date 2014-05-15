{-# language NoMonomorphismRestriction #-}
{-# language ScopedTypeVariables #-}
{-# language LambdaCase #-}

module MB.Logic where 

import Control.Monad.Logic
import Control.Applicative 
import Data.Maybe ( isJust )

import Control.Concurrent.Async as CCA
import Control.Concurrent.STM
import Control.Concurrent.Chan
import Control.Exception
import System.IO

run :: LogicT IO b -> IO (Maybe b)
run r = Control.Exception.handle ( \ (e :: SomeException) -> do
          hPutStrLn stderr $ unwords [ "###############", "caught", show e ]
          return Nothing  )
      $ runLogicT r ( \ x _ -> return $ Just x ) ( return Nothing ) -- observeManyT 1 r


work :: (a -> LogicT IO (b, b -> c)) -> a -> IO (Maybe c)
work w x = run $ do (x,f) <- w x ; return $ f x

traced s w = \ x -> do liftIO $ hPutStrLn stderr s ; w x

mkWork :: (a -> IO (Maybe b)) -> (a -> LogicT IO b)
mkWork p x = mkWork0 $ p x

mkWork0 :: IO (Maybe b) -> LogicT IO b
mkWork0 w = LogicT $ \ succ fail -> w >>= \ case
        Nothing -> fail
        Just y -> succ y fail

success = \ x -> return (x, id)

andthen0 p q x = p x >>= q

andthen p q = \ x -> do 
    (y,f) <- p x ; (z, g) <- q y ; return (z, f . g)

orelse p q = \ x -> do mplus (p x) (q x)

sequential_or ps = foldl1 orelse ps

parallel_or :: [ a -> LogicT IO b ] -> a -> LogicT IO b
parallel_or ps = \ x -> parallel_or0 $ map ( \ p -> p x ) ps

parallel_or0 = 
   -- parallel_or0_Chan
   parallel_or0_STM

-- | start processes in parallel.
-- the first one that completes successfully
-- will give the overall result, and cancel the others.
-- FIXME: this is (1) ugly, and (2) most probably wrong
-- (what happens if such a group is cancelled?
-- will it cancel all its members? I don't think so)
parallel_or0_Chan ps = mkWork0 $ do
    ch <- newChan
    as <- forM ps $ \ p -> async $ do 
         m <- run p -- runLogicT p ( \ r f -> return $ Just r) (return Nothing)
         writeChan ch m
    let work k = if k <= 0 
                 then return Nothing
                 else do r <- readChan ch
                         case r of
                             Nothing -> work (k-1)
                             Just x ->  return $ Just x
    (work $ length as) `finally` (forM_ as cancel) 

parallel_or0_STM :: [ LogicT IO b ] -> LogicT IO b
parallel_or0_STM ps = mkWork0 $ do
    asyncs :: [ Async (Maybe b) ] <- mapM async $ map run ps
    m <- waitAnyCatchCancelFilter isJust asyncs
    case m of
        Just (_, Right (Just x)) -> return $ Just x ; _ -> return Nothing

waitAnyCatchCancelFilter :: (a -> Bool) -> [Async a] -> IO (Maybe (Async a, Either SomeException a))
waitAnyCatchCancelFilter p asyncs = 
    waitAnyCatchFilter p asyncs `finally` mapM_ ( async . cancel ) asyncs 

waitAnyCatchFilter :: (a -> Bool) -> [Async a] -> IO (Maybe (Async a, Either SomeException a))
waitAnyCatchFilter p asyncs = atomically $ do
    running <- newTVar $ length asyncs
    foldr orElse ( do r <- readTVar running ; if r > 0 then retry else return Nothing ) 
      $ map (\a -> do 
        r <- waitCatchSTM a
        modifyTVar' running pred
        case r of Right x | p x -> return $ Just (a,r) ; _ -> retry 
      ) asyncs


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
