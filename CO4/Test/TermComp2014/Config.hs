module CO4.Test.TermComp2014.Config 
  (Config (..), parseConfig)
where

import System.Console.GetOpt
import System.Environment

data Config = Config {
    modelBitWidth  :: Int
  , numPrecedences :: Int
  , numPatterns    :: Int
  }

defaultConfig :: Config
defaultConfig = Config 0 0 0

options :: [OptDescr (Config -> Config)]
options =
 [ Option ['m'] ["model"]       (ReqArg (\v c -> c { modelBitWidth  = read v }) "NUM") "model bitwidth"
 , Option [   ] ["precedences"] (ReqArg (\v c -> c { numPrecedences = read v }) "NUM") "number of precedences"
 , Option ['p'] ["patterns"]    (ReqArg (\v c -> c { numPatterns    = read v }) "NUM") "number of patterns (if <= 0, then all patterns are generated)"
 ]

parseConfig :: IO (Config, String)
parseConfig = do
  args    <- getArgs

  let syntaxMsg = "[OPTION ...] FILE"

  case getOpt RequireOrder options args of
     (o,[n],[]) -> return (foldl (\c o -> o c) defaultConfig o, n)
     (_,_,msgs) -> error $ (unlines msgs) ++ (usageInfo syntaxMsg options)
