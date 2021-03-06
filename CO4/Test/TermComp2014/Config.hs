module CO4.Test.TermComp2014.Config 
  (Config (..), ArgumentFilter (..), defaultConfig, parseConfig, repairConfig)
where

import System.Console.GetOpt
import System.Environment

data ArgumentFilter = AFNone | AFNormal | AFBrute deriving Show

parseArgumentFilter :: String -> ArgumentFilter
parseArgumentFilter "none"   = AFNone
parseArgumentFilter "normal" = AFNormal
parseArgumentFilter "brute"  = AFBrute
parseArgumentFilter s        = error $ "Config.parseArgumentFilter: can not parse '" ++ s ++ "'"

data Config = Config {
    modelBitWidth            :: Int
  , numPrecedences           :: Int
  , numPatterns              :: Int
  , precedenceDomainBitWidth :: Int
  , argumentFilter           :: ArgumentFilter
  , usePrecedence            :: Bool
  , emptyPrecedence          :: Bool
  , useInterpretation        :: Bool
  , beVerbose                :: Bool
  , outputCPF                :: Bool
  }
  deriving Show

defaultConfig :: Config
defaultConfig = Config 
  { modelBitWidth            = 0
  , numPrecedences           = 1
  , numPatterns              = 0
  , precedenceDomainBitWidth = (-1)
  , argumentFilter           = AFNormal
  , usePrecedence            = True
  , emptyPrecedence          = False
  , useInterpretation        = False
  , beVerbose                = False
  , outputCPF                = False
  }

repairConfig :: Config -> Config
repairConfig c = 
    if not (usePrecedence c) && not (useInterpretation c)
    then c { usePrecedence = True }
    else c

options :: [OptDescr (Config -> Config)]
options =
 [ Option ['m'] ["model"] (ReqArg (\v c -> c { modelBitWidth  = read v }) "NUM") 
   "model bitwidth (default: 0)"

 , Option [ 'o' ] ["orders"] (ReqArg (\v c -> c { numPrecedences = read v }) "NUM") 
   "number of orders  (default: 1)"

 , Option ['p'] ["patterns"] (ReqArg (\v c -> c { numPatterns    = read v }) "NUM") 
   "number of patterns (if <= 0, all patterns are generated) (default: 0)"

 , Option [ 'h' ] ["height"] (ReqArg (\v c -> c { precedenceDomainBitWidth = read v }) "NUM") 
   "bitwidth for height of precedence (if < 0, maximum necessary bitwidth is assumed) (default: -1)"

 , Option [ 'a'  ] ["argument-filter"] (ReqArg (\v c -> c { argumentFilter = parseArgumentFilter v })
                                       "[none,normal,brute]") 
   "used argument filter ('brute' deletes all children) (default: normal)"

 , Option [ 'l' ] ["linear-interpretation"] (NoArg (\c -> c { useInterpretation=True }))
   "use linear interpretations (with linear coefficients in {0,1}) (default: false)"

 , Option [ 'r' ] ["rpo"] (NoArg (\c -> c {usePrecedence=True}))
   "use RPO (for the moment, LPO with permuting argument filter) (default: true)"

 , Option [ 'e' ] ["empty-precedence" ] (NoArg (\c -> c {usePrecedence=True,emptyPrecedence=True}))
   "use RPO with empty precedence (that is, argument-filtered subterm relation) (default: false)"

 , Option [ 'c' ] [ "cpf" ] (NoArg (\c -> c {outputCPF=True}))
   "output proof in CPF format (default: false)"

 , Option [ 'v' ] ["verbose" ] (NoArg (\c -> c {beVerbose=True}))
   "be verbose (default: false)"
 ]

parseConfig :: IO (Config, String)
parseConfig = do
  args    <- getArgs

  let syntaxMsg = "[OPTION ...] FILE"

  case getOpt Permute options args of
     (o,[n],[]) -> 
         return ( repairConfig $ foldl (\c o -> o c) defaultConfig o, n )
     (_,_,msgs) -> error $ (unlines msgs) ++ (usageInfo syntaxMsg options)
