import System.Environment (getArgs)
import Control.Monad (forM_)
{-
import Text.XML.HaXml (verbatim)
import Text.XML.HaXml.XmlContent.Parser (toContents)
-}
import           TPDB.Data (TRS,Identifier,rules)
import           TPDB.Pretty (pretty)
import           TPDB.Input (get_trs)
import           Compress.Paper (Compression(..),compress)
import           Compress.Paper.Costs (Costs (costs))

main :: IO ()
main = do
  (compression,paths) <- do
    args <- getArgs
    case args of
      "-s":paths -> return (Simple,paths)
      "-i":paths -> return (Iterative,paths)
      "-c":paths -> return (Comparison,paths)
      _          -> error "syntax: {-s,-i,-c} [PATH]*"

 -- putStrLn $ show compression
--  putStrLn $ show paths
  putStr $ show paths
  putStr "    "

  case compression of
    Comparison -> forM_ paths $ \path -> get_trs path >>= compareCompression
    _          -> forM_ paths $ \path -> get_trs path >>= handleTrs compression

handleTrs :: Compression -> TRS Identifier Identifier -> IO ()
handleTrs compression trs =
  let compressed = snd $ compress compression $ rules trs
  in do
    
    putStrLn $ (show ( costs trs) )++"    " ++ (show (costs compressed))
    {-
    putStrLn ""   
      
    putStrLn "## Problem #####################"
    putStrLn $ "Costs: " ++ (show $ costs trs)
    putStrLn $ show $ pretty trs
    putStrLn ""
    putStrLn "## Compressed ##################"
    putStrLn $ "Costs: " ++ (show $ costs compressed)
    putStrLn $ show $ pretty compressed
    putStrLn ""
    
    putStrLn "## Compressed (XML) ############"
    putStrLn $ show $ verbatim $ toContents compressed
    putStrLn ""
    -}
  
compareCompression :: TRS Identifier Identifier -> IO ()
compareCompression trs = putStrLn $ show $ compressed1 == compressed2
  where 
    compressed1 = snd $ compress Simple    $ rules trs
    compressed2 = snd $ compress Iterative $ rules trs
