module MB.Options where

import System.Console.GetOpt

data Options =
     Options { dim :: Int
             , bits :: Int
             , compress :: Bool
             , dp :: Bool
             }
    deriving Show

options0 = Options 
         { dim = 5, bits = 3
         , compress = False, dp = False 
         }

options = 
    [ Option [ 'd' ] [ "dimension" ]
       ( ReqArg ( \ s opts -> opts { dim = read s }) "Int" ) "vector dimension"
    , Option [ 'b' ] [ "bits" ]
       ( ReqArg ( \ s opts -> opts { bits = read s }) "Int" ) "bit width"
    , Option [ 'c' ] [ "compress" ]
       ( NoArg ( \ opts -> opts { compress = True }) ) "compress"
    , Option [ 'p' ] [ "dp" ]
       ( NoArg ( \ opts -> opts { dp = True })) "dependency pairs transformation"   
    ]
