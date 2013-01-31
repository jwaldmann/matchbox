module MB.Options where

import System.Console.GetOpt

data Compression = None 
                 | Simple | Simple_Weak_Only
                 | Paper  | PaperIter
                 | Hack_DP
   deriving (Eq, Ord, Show)

data Options =
     Options { dim :: Int
             , bits :: Int
             , compression :: Compression
             , dp :: Bool
             , mirror :: Bool
             , parallel :: Bool
             , printStatistics :: Bool
             }
    deriving Show

options0 = Options 
         { dim = 5, bits = 3
         , compression = None
         , dp = False 
         , mirror = False
         , parallel = False
         , printStatistics = False
         }

options = 
    [ Option [ 'd' ] [ "dimension" ]
       ( ReqArg ( \ s opts -> opts { dim = read s }) "Int" ) "vector dimension"
    , Option [ 'b' ] [ "bits" ]
       ( ReqArg ( \ s opts -> opts { bits = read s }) "Int" ) "bit width"
    , Option [ 'h' ] [ "hack-dp-compress" ]
       ( NoArg ( \ opts -> opts { compression = Hack_DP, dp = True }) ) 
               "DP transform on compressed system"
    , Option [ 'k' ] [ "compression-simple" ]
       ( NoArg ( \ opts -> opts { compression = Simple }) ) "compress (simple)"
    , Option [ 'i' ] [ "compression-weak" ]
       ( NoArg ( \ opts -> opts { compression = Simple_Weak_Only }) ) "compress (simple, for weak rules only)"
    , Option [ 'c' ] [ "compression-paper" ]
       ( NoArg ( \ opts -> opts { compression = Paper }) ) "compress (algorithm as in paper)"
    , Option [ 'C' ] [ "compression-paper (iterative)" ]
       ( NoArg ( \ opts -> opts { compression = PaperIter }) ) "compress (algorithm as in paper, iterative version)"
    , Option [ 'p' ] [ "dp" ]
       ( NoArg ( \ opts -> opts { dp = True })) "dependency pairs transformation"   
    , Option [     ] [ "parallel" ]
       ( NoArg ( \ opts -> opts { parallel = True })) "start threads for different dimensions in parallel"
    , Option [ 'm' ] [ "mirror" ]
       ( NoArg ( \ opts -> opts { mirror = True })) "if input is SRS, then mirror lhs and rhs"   
    , Option [ 's' ] [ "printStatistics" ]
       ( NoArg ( \ opts -> opts { printStatistics = True })) "print some statistics"   
    ]
