module MB.Options where

import System.Console.GetOpt
import System.Environment

data Compression = None 
                 | Simple
                 | Paper  | PaperIter                 
   deriving (Eq, Ord, Show)

data Solver = Boolector
            | Satchmo
            | Satchmo_Guarded
   deriving (Eq, Ord, Show)     

data Encoding = Binary | Unary
              | Interval_Plain | Interval_Fibs
              | Interval_Twos | Interval_Threes
   deriving (Eq, Ord, Show)     

data Mode = Termination
          | Complexity (Maybe Int) -- ^ upper bound for deg. of pol.
          | Cycle_Termination -- ^ for SRS, termination modulo conjugacy
     deriving (Eq, Ord, Show)

data Direction = Yeah -- ^ prove termination only
               | Noh  -- ^ prove nontermination only
               | Both -- ^ attempt both
  deriving (Eq, Ord, Show)
              
data Options =
     Options { dim :: Int
             , bits :: Int
             , solver :: Solver
             , encoding :: Encoding  
             , compression :: Compression
             , constraints :: Int
             , small_constraints :: Bool
             , mode :: Mode
             , direction :: Direction
             , remove_all :: Bool
             , triangular :: Bool
             , power_triangular :: Maybe Int
             , dependency_pairs :: Bool
             , usable_rules :: Bool  
             , fromtop :: Bool
             , naive :: Bool
             , mirror :: Bool
             , mirror_labelled :: Bool
             , parallel :: Bool
             , cores :: Maybe Int
             , label :: Maybe (Int,Int)
             , use_lpo :: Bool
             , use_natural :: Bool
             , use_arctic :: Bool
             , printStatistics :: Bool
             , dump_boolector :: Dump
             , cpf :: Bool
             , latex :: Maybe (Maybe FilePath) 
             }
    deriving Show

data Dump = Never | Above Int 
  deriving ( Eq, Ord, Show )

options0 = Options 
         { mode = Termination
         , direction = Yeah
         , dim = 5, bits = 3
         , solver = Satchmo
         , encoding = Binary
         , compression = None
         , constraints = 0
         , remove_all = False
         , triangular = False
         , power_triangular = Nothing
         , small_constraints = False
         , dependency_pairs = False
         , usable_rules = False
         , fromtop = False
         , naive = False
         , mirror = False
         , mirror_labelled = False
         , parallel = False
         , cores = Just 2
         , label = Nothing
         , use_lpo = False
         , use_natural = False
         , use_arctic = False
         , printStatistics = False
         , dump_boolector = Never
         , cpf = False
         , latex = Nothing
         }

options = 
    [ Option [ ] [ "complexity" ]
      (OptArg ( \ ms opts -> opts
         { mode = Complexity $ fmap read ms
         -- , triangular = True
         , remove_all = True
         , use_natural = True
         , dependency_pairs = False
         } ) "Int" )
      "prove polynomial complexity (with degree bound)"

    , Option [] [ "yeah" ]
      (NoArg ( \ opts -> opts{direction = Yeah}))
      "prove termination (upper bounds)"
    , Option [] [ "noh" ]
      (NoArg ( \ opts -> opts{direction = Noh}))
      "prove nontermination (lower bounds)"
    , Option [] [ "both" ]
      (NoArg ( \ opts -> opts{direction = Both}))
      "start proof attempts for termination and nontermination (upper and lower bounds)"
      
    , Option [] [ "cycle" ]
       (NoArg ( \ opts -> opts
         { mode = Cycle_Termination
         , dependency_pairs = False
         , constraints = 0
         } ) )
      "prove cycle termination (for SRS, termination modulo conjugacy)"
      
    , Option [ 'd' ] [ "dimension" ]
       ( ReqArg ( \ s opts -> opts { dim = read s }) "Int" ) "vector dimension"
    , Option [ 'b' ] [ "bits" ]
       ( ReqArg ( \ s opts -> opts { bits = read s }) "Int" ) "bit width"

    , Option [ ] [ "boolector" ]
       (NoArg ( \ opts -> opts { solver = Boolector } ))
       "use Boolector SMT solver"
    , Option [ ] [ "dump-boolector-above" ]
       (OptArg ( \ s opts -> opts { dump_boolector = case s of
               Nothing -> Above 0 ; Just s -> Above $ read s
               } ) "Int" )
       "dump smt2 file if Boolector takes at least N seconds (default N=0, dump all)"
    , Option [ ] [ "satchmo" ]
       (NoArg ( \ opts -> opts { solver = Satchmo } ))
       "use Satchmo SMT solver (bitblasting via minisat)"
    , Option [ ] [ "guarded-satchmo" ]
       (NoArg ( \ opts -> opts { solver = Satchmo_Guarded } ))
       "use Satchmo SMT solver (bitblasting via minisat) (with guard bits)"


    , Option [ ] [ "binary" ]
        (NoArg ( \ opts -> opts { encoding = Binary } ))
        "bitblast numbers to binary"
    , Option [ ] [ "unary" ]
        (NoArg ( \ opts -> opts { encoding = Unary } ))
        "bitblast numbers to unary"

    , Option [ ] [ "plain" ]
        (NoArg ( \ opts -> opts { encoding = Interval_Plain }))
        "interval bitblasting for [0,1,..]"
    , Option [ ] [ "fibonacci" ]
        (NoArg ( \ opts -> opts { encoding = Interval_Fibs }))
        "interval bitblasting for Fibonacci numbers"
    , Option [ ] [ "twos" ]
        (NoArg ( \ opts -> opts { encoding = Interval_Twos }))
        "interval bitblasting for powers of 2"
    , Option [ ] [ "threes" ]
        (NoArg ( \ opts -> opts { encoding = Interval_Threes }))
        "interval bitblasting for powers of 3"

    , Option [] [ "constraints" ]
        ( ReqArg ( \ s opts -> opts { constraints = read s } ) "Int" )
      "number of constraints for polyhedral domain"

    , Option [] [ "all" ]
        ( NoArg ( \ opts -> opts { remove_all = True } ) )
        "remove all rules at once"
      
    , Option [] [ "triangular" ]
        ( NoArg ( \ opts -> opts { triangular = True } ) )
        "use upper triangular shape (with --all, proves polynomial complexity)"

    , Option [] [ "power-triangular" ]
        ( ReqArg ( \ s opts -> opts { power_triangular = Just $ read s } ) "Int" )
        "max matrix has upper triangular power (with --all, proves polynomial complexity)"

    , Option [] [ "small-constraints" ]
        ( OptArg ( \ s opts -> opts { small_constraints = case s of
                                         Nothing -> True
                                         Just s -> read s } ) "Bool" )
        "use small numbers {-1,0,1} in C matrix of constraint"
      
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
             "use natural matrix interpretations"
    , Option [ 'a' ] ["arctic" ] 
             (NoArg ( \ opts -> opts { use_arctic = True } ) )
             "use arctic matrix interpretations"

    , Option [ 'm' ] [ "mirror" ]
       ( NoArg ( \ opts -> opts { mirror = True })) "if input is SRS, then mirror lhs and rhs"   

    , Option [ 'k' ] [ "compression-simple" ]
       ( NoArg ( \ opts -> opts { compression = Simple }) ) "compress (simple)"

    , Option [ 'c' ] [ "compression-paper" ]
       ( NoArg ( \ opts -> opts { compression = Paper }) ) "compress (algorithm as in paper)"
    , Option [ 'C' ] [ "compression-paper (iterative)" ]
       ( NoArg ( \ opts -> opts { compression = PaperIter }) ) "compress (algorithm as in paper, iterative version)"

    , Option [ 'p' ] [ "dp", "dependency-pairs" ]
       ( NoArg ( \ opts -> opts { dependency_pairs = True })) "dependency pairs transformation"   

    , Option [ 'u' ] [ "ur", "usable-rules" ]
       ( NoArg ( \ opts -> opts { usable_rules = True })) "restrict to usable rules"   

    , Option [ 'P' ] [ "dp-fromtop" ]
       ( NoArg ( \ opts -> opts { dependency_pairs = True, fromtop = True })) "dependency pairs transformation and then compression from the top"   

    , Option [ 'n' ] [ "dp-naive" ]
       ( NoArg ( \ opts -> opts { dependency_pairs = True, naive = True })) "apply compression after dependency pairs transformation"   

    , Option [     ] [ "parallel" ]
       ( NoArg ( \ opts -> opts { parallel = True }))
      "start threads for different dimensions in parallel"

    , Option [] [ "cores" ]
       (OptArg ( \ s opts -> opts { cores = fmap read s }) "Int" )
      "use several cores (threads), no argument: all available"
      
    , Option [ 's' ] [ "printStatistics" ]
       ( NoArg ( \ opts -> opts { printStatistics = True })) "print some statistics"   


    , Option [ 'c' ] [ "cpf" ]
       ( NoArg ( \ opts -> opts { cpf = True }))
       "proof output in CPF (XML) format"

    , Option [ ] [ "latex" ]
      ( OptArg ( \ s opts -> opts { latex = Just s }) "FilePath" )
      "proof output in LaTeX format to file (default: to stdout)" 
    ]

parse :: IO (Options, String)
parse = do
    args    <- getArgs

    let syntaxMsg = "[OPTION ...] FILE"

    case getOpt Permute options args of
        (o,[n],[]) -> 
            return (  foldl (\c o -> o c) options0 o, n )
        (_,_,msgs) ->
            error $ (unlines msgs) ++ (usageInfo syntaxMsg options)
