import System.Environment (getArgs)
import Control.Monad (forM_)
{-
import Text.XML.HaXml (verbatim)
import Text.XML.HaXml.XmlContent.Parser (toContents)
-}
import           TPDB.Data (TRS,Identifier,rules)
import           TPDB.Pretty (pretty)
import           TPDB.Input (get_trs)
import           Compress.Paper (compress)
import           Compress.Paper.Costs (Costs (costs))

main :: IO ()
main = do
  paths    <- getArgs
  putStrLn $ show paths

  forM_ paths $ \path -> get_trs path >>= handleTrs

handleTrs :: TRS Identifier Identifier -> IO ()
handleTrs trs =
  let compressed = snd $ compress $ rules trs
  in do
    {-
    putStrLn $ "Input: " ++ (show ( costs problem) )++" Output: " ++ (show (costs compressed))
    putStrLn ""   
    -}
    putStrLn "## Problem #####################"
    putStrLn $ "Costs: " ++ (show $ costs trs)
    putStrLn $ show $ pretty trs
    putStrLn ""
    putStrLn "## Compressed ##################"
    putStrLn $ "Costs: " ++ (show $ costs compressed)
    putStrLn $ show $ pretty compressed
    putStrLn ""
    {-
    putStrLn "## Compressed (XML) ############"
    putStrLn $ show $ verbatim $ toContents compressed
    putStrLn ""
    -}
  
  

