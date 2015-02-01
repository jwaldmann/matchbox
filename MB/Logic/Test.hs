import Prelude hiding ( log )
import System.IO

import MB.Logic

import Control.Concurrent

main = do
  hSetBuffering stderr LineBuffering
  hSetBuffering stdout LineBuffering
  -- log "t1" $ run $ p1 0
  -- log "t2" $ run $ (orelse p1 p2) 0
  -- log "t3" $ run $ (orelse p2 p1) 0
  -- log "t4" $ run $ sequential_or [ p2, p1 ] 0
  -- log "t5" $ run $ parallel_or [  p1 ] 0
  log "t6" $ run $ parallel_or [  p1, p2 ] 0
  -- test2 >>= print
  -- test3 >>= print

-- test1 = run $  (orelse p2 p1)  0
-- test2 = run $  (orelse p1 p2)  0
-- test3 = run $  (_ p1 p2)  0

p1 = mkWork $ \ x -> log "p1" $ do
     threadDelay (2 * 10^6)
     return $ Just x

p2 = mkWork $ \ x -> log "p2" $ do
     threadDelay (10^6)
     return $ Nothing

log :: Show a => String -> IO a -> IO a
log msg action = do
  hPutStrLn stderr $ unwords [ msg, "start" ]
  x <- action
  hPutStrLn stderr $ unwords [ msg, "end", "with", show x ]
  return x



