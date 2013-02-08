module MB.Lock ( Lock, create, exclusive ) where

import Control.Concurrent.STM

data Lock = Lock { locked :: TVar Bool }

create :: IO Lock
create = atomically $ do
    l <- newTVar False
    return $ Lock l

acquire l = atomically $ do
    v <- readTVar $ locked l
    if not v then writeTVar (locked l) True else retry

release l = atomically $ do
    writeTVar (locked l) False

-- | runs the action and forces the result to WHNF
exclusive :: Lock -> IO a -> IO a
exclusive l action = do
    acquire l
    x <- action
    seq x $ return () 
    release l
    return x

