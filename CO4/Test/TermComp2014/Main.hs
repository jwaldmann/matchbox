{-# LANGUAGE LambdaCase #-}
import System.Exit (exitSuccess, exitFailure)
import TPDB.Input (get_trs)
import TPDB.DP (dp)
import CO4.Test.TermComp2014.Config (parseConfig)
import CO4.Test.TermComp2014.Run (runN)

main :: IO ()
main = do
  (config,filePath) <- parseConfig
  get_trs filePath >>= runN config . dp >>= \case
    Nothing -> putStrLn "don't know" >> exitFailure
    Just _  -> putStrLn "terminates" >> exitSuccess
