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

success = \ x -> return (x, id)

traced s w = \ x -> do liftIO $ hPutStrLn stderr s ; w x

mkWork :: (a -> IO (Maybe b)) -> (a -> LogicT IO b)
mkWork p x = mkWork0 $ p x

mkWork0 :: IO (Maybe b) -> LogicT IO b
mkWork0 w = LogicT $ \ succ fail -> w >>= \ case
        Nothing -> fail
        Just y -> succ y fail


andthen0 p q x = p x >>= q

andthen p q = \ x -> do 
    (y,f) <- p x ; (z, g) <- q y ; return (z, f . g)

orelse p q = \ x -> do mplus (p x) (q x)

sequential_or ps = foldr1 orelse ps


-- | run at most b of the computations concurrently,
-- starting them in order they appear in the list. 
-- when any of them returns a result x,
-- kill the others, and return x to the caller.
-- WARNING: @ps@ possibly is a lazy infinite list
bounded_parallel_or b ps = \ x ->
  bounded_parallel_or0 b $ map ( \ p -> p x ) ps

-- | WARNING: @as@ possibly is a lazy infinite list
bounded_parallel_or0 b as = mkWork0 $ do
  hPutStrLn stderr "--------------- bp start"
  let worker [] [] = return Nothing
      worker running waiting = do
        hPutStrLn stderr $ unwords
          [ "---------------- bp.worker", "running:", show (length running)  ]
        hFlush stderr
        (a,r) <- waitAnyCatch running
        case r of
          Right (Just x) -> return (Just x)
              `finally` forM_ running (async . cancel)
          _-> case waiting of
              [] -> worker (filter (/= a) running) []
              w:aiting -> do
                hPutStrLn stderr "-------------- start next process from queue"
                b <- async $ run w
                worker (b : filter (/= a) running) aiting
  let (canrun, mustwait) = splitAt b as
  hPutStrLn stderr "--------------- bp start processes"
  asyncs <- forM canrun ( async . run )
  hPutStrLn stderr $ "--------------- bp processes started: " ++ show (length asyncs)
  worker asyncs mustwait

-- | run the computations concurrently.
-- when any of them returns a result x,
-- kill the others, and return x to the caller.
parallel_or :: [ a -> LogicT IO b ] -> a -> LogicT IO b
parallel_or ps = \ x -> parallel_or0 $ map ( \ p -> p x ) ps

parallel_or0 :: [ LogicT IO b ] -> LogicT IO b
parallel_or0 ps = mkWork0 $ do
    asyncs <- forM ps ( async . run )
    m <- waitAnyCatchCancelFilter isJust asyncs
    case m of
        Just (_, Right (Just x)) -> return $ Just x
        _ -> return Nothing

waitAnyCatchCancelFilter
  :: (a -> Bool)
  -> [Async a]
  -> IO (Maybe (Async a, Either SomeException a))
waitAnyCatchCancelFilter p asyncs = 
    waitAnyCatchFilter p asyncs `finally` mapM_ (async . cancel) asyncs 

waitAnyCatchFilter
  :: (a -> Bool)
  -> [Async a]
  -> IO (Maybe (Async a, Either SomeException a))     
waitAnyCatchFilter p as = case as of
  [] -> return Nothing
  _ -> do
    let verbose = False
        trace ws = when verbose $ hPutStrLn stderr $ unwords ws
    trace ["handle:before wait" ]
    (a,r)  <- waitAnyCatch as
    trace ["handle:after wait"  ]
    case r of
      Right  x | p x -> do
        trace [ "handle:returns" ]
        return $ Just (a, Right x)
      _ -> do
        trace [ "handle:repeats" ]
        waitAnyCatchFilter p $ filter (/= a) as


{-
-- why did this work at all?
-- if an async returns with Nothing,
-- the transaction will retry,
-- so the modification of the TVar (pred)
-- will not be published?
waitAnyCatchFilter p asyncs = atomically $ do
    running <- newTVar $ length asyncs
    foldr orElse
      ( do r <- readTVar running
           if r > 0 then retry else return Nothing
      ) 
      $ map (\a -> do 
        r <- waitCatchSTM a
        modifyTVar' running pred
        case r of
          Right x | p x -> return $ Just (a,r)
          _ -> retry 
      ) asyncs
-}

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
