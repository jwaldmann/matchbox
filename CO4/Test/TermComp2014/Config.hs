module CO4.Test.TermComp2014.Config 
  (Config (..), defaultConfig, parseConfig)
where

import System.Console.GetOpt
import System.Environment

data Config = Config {
    modelBitWidth            :: Int
  , numPrecedences           :: Int
  , numPatterns              :: Int
  , precedenceDomainBitWidth :: Int
  , bruteFilter              :: Bool
  }

defaultConfig :: Config
defaultConfig = Config 0 1 0 (-1) False

options :: [OptDescr (Config -> Config)]
options =
 [ Option ['m'] ["model"] (ReqArg (\v c -> c { modelBitWidth  = read v }) "NUM") 
   "model bitwidth (default: 0)"

 , Option [   ] ["precedences"] (ReqArg (\v c -> c { numPrecedences = read v }) "NUM") 
   "number of precedences (default: 1)"

 , Option ['p'] ["patterns"] (ReqArg (\v c -> c { numPatterns    = read v }) "NUM") 
   "number of patterns (if <= 0, all patterns are generated) (default: 0)"

 , Option [   ] ["precedence-domain"] (ReqArg (\v c -> c { precedenceDomainBitWidth = read v }) "NUM") 
   "precedence domain bitwidth (if < 0, maximum necessary bitwidth is assumed) (default: -1)"

 , Option [   ] ["brute-filter"] (NoArg (\c -> c { bruteFilter = True })) 
   "use argument filter that deletes all children (default: false)"
 ]

parseConfig :: IO (Config, String)
parseConfig = do
  args    <- getArgs

  let syntaxMsg = "[OPTION ...] FILE"

  case getOpt Permute options args of
     (o,[n],[]) -> return (foldl (\c o -> o c) defaultConfig o, n)
     (_,_,msgs) -> error $ (unlines msgs) ++ (usageInfo syntaxMsg options)
