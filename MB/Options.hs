module MB.Options where

import System.Console.GetOpt

data Compression = None 
                 | Simple
                 | Paper  | PaperIter                 
   deriving (Eq, Ord, Show)

data Options =
     Options { dim :: Int
             , bits :: Int
             , compression :: Compression
             , dp :: Bool
             , fromtop :: Bool
             , naive :: Bool
             , mirror :: Bool
             , mirror_labelled :: Bool
             , parallel :: Bool
             , label :: Maybe (Int,Int)
             , use_lpo :: Bool
             , use_natural :: Bool
             , use_arctic :: Bool
             , printStatistics :: Bool
             , cpf :: Bool
             }
    deriving Show

options0 = Options 
         { dim = 5, bits = 3
         , compression = None
         , dp = False 
         , fromtop = False
         , naive = False
         , mirror = False
         , mirror_labelled = False
         , parallel = False
         , label = Nothing
         , use_lpo = False
         , use_natural = False
         , use_arctic = False
         , printStatistics = False
         , cpf = False
         }

options = 
    [ Option [ 'd' ] [ "dimension" ]
       ( ReqArg ( \ s opts -> opts { dim = read s }) "Int" ) "vector dimension"
    , Option [ 'b' ] [ "bits" ]
       ( ReqArg ( \ s opts -> opts { bits = read s }) "Int" ) "bit width"

    , Option [ 'l' ] [ "label" ]
       ( ReqArg ( \ s opts -> opts { label = Just $ read $ "(" ++ s ++ ")" }) "Int,Int" ) 
       "-l x,y : label by model with x bits and y interpretations before unlabeling"

    , Option [ 'M' ] ["mirror-labelled" ] 
             (NoArg ( \ opts -> opts { mirror_labelled = True } ) )
             "(with l) for each labelled rule, try all methods also for the mirror image"

    , Option [] ["lpo" ] 
             (NoArg ( \ opts -> opts { use_lpo = True } ) )
             "(with l) use LPO"
    , Option [ 'n' ] ["natural" ] 
             (NoArg ( \ opts -> opts { use_natural = True } ) )
             "(with l) use natural matrix interpretations"
    , Option [ 'a' ] ["arctic" ] 
             (NoArg ( \ opts -> opts { use_arctic = True } ) )
             "(with l) use arctic matrix interpretations"

    , Option [ 'm' ] [ "mirror" ]
       ( NoArg ( \ opts -> opts { mirror = True })) "if input is SRS, then mirror lhs and rhs"   

    , Option [ 'k' ] [ "compression-simple" ]
       ( NoArg ( \ opts -> opts { compression = Simple }) ) "compress (simple)"

    , Option [ 'c' ] [ "compression-paper" ]
       ( NoArg ( \ opts -> opts { compression = Paper }) ) "compress (algorithm as in paper)"
    , Option [ 'C' ] [ "compression-paper (iterative)" ]
       ( NoArg ( \ opts -> opts { compression = PaperIter }) ) "compress (algorithm as in paper, iterative version)"

    , Option [ 'p' ] [ "dp" ]
       ( NoArg ( \ opts -> opts { dp = True })) "dependency pairs transformation"   

    , Option [ 'P' ] [ "dp-fromtop" ]
       ( NoArg ( \ opts -> opts { dp = True, fromtop = True })) "dependency pairs transformation and then compression from the top"   

    , Option [ 'n' ] [ "dp-naive" ]
       ( NoArg ( \ opts -> opts { dp = True, naive = True })) "apply compression after dependency pairs transformation"   

    , Option [     ] [ "parallel" ]
       ( NoArg ( \ opts -> opts { parallel = True })) "start threads for different dimensions in parallel"
    , Option [ 's' ] [ "printStatistics" ]
       ( NoArg ( \ opts -> opts { printStatistics = True })) "print some statistics"   


    , Option [ 'c' ] [ "cpf" ]
       ( NoArg ( \ opts -> opts { cpf = True }))
       "proof output in CPF (XML) format"
    ]
