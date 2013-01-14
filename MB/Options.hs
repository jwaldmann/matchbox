module MB.Options where

import System.Console.GetOpt

data Compression = None | Simple | Paper
   deriving (Eq, Ord, Show)

data Options =
     Options { dim :: Int
             , bits :: Int
             , compression :: Compression
             , dp :: Bool
             }
    deriving Show

options0 = Options 
         { dim = 5, bits = 3
         , compression = None
         , dp = False 
         }

options = 
    [ Option [ 'd' ] [ "dimension" ]
       ( ReqArg ( \ s opts -> opts { dim = read s }) "Int" ) "vector dimension"
    , Option [ 'b' ] [ "bits" ]
       ( ReqArg ( \ s opts -> opts { bits = read s }) "Int" ) "bit width"
    , Option [ 'k' ] [ "compression-simple" ]
       ( NoArg ( \ opts -> opts { compression = Simple }) ) "compress"
    , Option [ 'c' ] [ "compression-paper" ]
       ( NoArg ( \ opts -> opts { compression = Paper }) ) "compress"
    , Option [ 'p' ] [ "dp" ]
       ( NoArg ( \ opts -> opts { dp = True })) "dependency pairs transformation"   
    ]
