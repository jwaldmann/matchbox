{-# LANGUAGE LambdaCase #-}
import           System.Exit (exitSuccess, exitFailure)
import           Control.Monad (when)
import           CO4.Test.TermComp2014.Config (parseConfig,outputCPF)
import           CO4.Test.TermComp2014.Run (runN)
import           TPDB.Input (get_trs)
import qualified TPDB.CPF.Proof.Type as T
import qualified TPDB.CPF.Proof.Xml as T
import           Text.XML.HaXml.Pretty (document)

main :: IO ()
main = do
  (config,filePath) <- parseConfig
  trs               <- get_trs filePath 
  runN config trs >>= \case
    Nothing -> do putStrLn "MAYBE" 
                  exitFailure

    Just p  -> do putStrLn "YES"
                  when (outputCPF config) $
                    putStrLn $ show $ document $ T.tox 
                             $ T.CertificationProblem 
                                (T.TrsInput trs)
                                "2.1" p 
                                (T.ProofOrigin $ T.Tool "termcomp2014" "0")
                  exitSuccess
