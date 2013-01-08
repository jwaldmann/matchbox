-- | simplified Matchbox Termination Prover

import qualified Compress.Simple as C

import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.Boolean as B
import qualified Satchmo.SAT.Mini
import Satchmo.Code

import TPDB.Data
import qualified TPDB.DP
import TPDB.Pretty
import TPDB.Plain.Write
import TPDB.Plain.Read
import TPDB.Input ( get_trs )

import System.Environment
import System.Console.GetOpt
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad ( forM, void, foldM )
import Text.PrettyPrint.HughesPJ (render)

handle :: (Show s, Ord v, Pretty v, Pretty s, Ord s)
       => Options -> TRS v s -> IO ()
handle opts sys = do
    print $ pretty sys

    let (co, trees) = 
          ( if compress opts
            then C.compress else C.nocompress 
          ) $ rules sys

    out <- Satchmo.SAT.Mini.solve $ do
        let ldict = L.linear mdict
            mdict = M.matrix idict
            idict = I.binary_fixed (bits opts)
        funmap <- system ldict (dim opts) trees
        return $ mdecode ldict funmap

    case out of
        Just f -> void $ forM (M.toList f) print    

handle_dp :: (Show s, Ord v, Pretty v, Pretty s, Ord s)
       => Options -> TRS v (TPDB.DP.Marked s) -> IO ()
handle_dp opts sys = do
    print $ pretty sys

    let (co, trees) = 
          ( if compress opts
            then C.compress else C.nocompress 
          ) $ rules sys

    out <- Satchmo.SAT.Mini.solve $ do
        let ldict = L.linear mdict
            mdict = M.matrix idict
            idict = I.binary_fixed (bits opts)
        funmap <- system_dp ldict (dim opts) trees
        return $ mdecode ldict funmap

    case out of
        Just f -> void $ forM (M.toList f) print    
    
mdecode dict f = do
    pairs <- forM ( M.toList f) $ \ (k,v) -> do
        w <- L.decode dict v
        return (k,w)
    return $ M.fromList pairs 

-- | assert that at least one rule can be removed.
-- returns interpretation of function symbols.
system dict dim trees = do
    let ofs = original_function_symbols trees
    opairs <- forM (S.toList ofs) $ \ (f,ar) -> do
        l <- L.make dict ar (dim , dim)
        s <- L.positive dict l
        B.assert [s]
        return (f, l)
    funmap <- foldM (digger dict) ( M.fromList opairs )
           $ reverse $ C.extras trees
    flags <- forM (C.roots trees) 
             $ rule dict dim funmap
    B.assert flags 
    return funmap

-- | assert that at least one rule can be removed.
-- returns interpretation of function symbols.
system_dp dict dim trees = do
    let ofs = original_function_symbols trees
    opairs <- forM (S.toList ofs) $ \ (f,ar) -> do
        let topdim = case f of
                C.Orig (TPDB.DP.Marked   {}) -> 1
                C.Orig (TPDB.DP.Original {}) -> dim
        l <- L.make dict ar (topdim , dim)
        -- s <- L.positive dict l
        -- B.assert [s]
        return (f, l)
    funmap <- foldM (digger dict) ( M.fromList opairs )
           $ reverse $ C.extras trees
    flags <- forM (C.roots trees) 
             $ rule_dp dict dim funmap
    B.assert flags 
    return funmap

original_function_symbols trees = 
    let remaining_ofs = S.fromList $ do 
           u <- C.roots trees ; t <- [ lhs u, rhs u ]
           Node (f @ C.Orig{}) xs <- subterms t 
           return (f, length xs)
        ofs_in_digrams ds = do
           C.Dig d <- ds
           (f,a) <- [ (C.parent d, C.parent_arity d)
                    , (C.child  d, C.child_arity  d)
                    ]
           case f of
                C.Orig {} -> [ (f,a) ]
                C.Dig {}  -> ofs_in_digrams [f]
    in  S.union remaining_ofs 
        $ S.fromList $ ofs_in_digrams $ C.extras trees

digger dict m (C.Dig d) = do
            let p = m M.! C.parent d 
                pos = C.position d - 1
                (pre,post) = splitAt pos $ L.lin p
                c = m M.! C.child d 
            h <- L.substitute dict
                ( L.Linear {L.abs = L.abs p
                   , L.lin = [L.lin p !! pos ]
                   } ) [ c ]
            let fg = L.Linear { L.abs = L.abs h
                     , L.lin = pre ++ L.lin h ++ post
                     , L.dim = (L.to p, L.from c)
                     }
            return $ M.insert (C.Dig d) fg m

-- | asserts weak decrease and returns strict decrease
rule dict dim funmap u = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term dict dim funmap varmap $ lhs u
    r <- term dict dim funmap varmap $ rhs u
    w <- L.weakly_greater dict l r
    B.assert [w]
    s <- L.strictly_greater dict l r
    return s

-- | asserts weak decrease and returns strict decrease
-- for strict rule
rule_dp dict dim funmap u = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term dict dim funmap varmap $ lhs u
    r <- term dict dim funmap varmap $ rhs u
    w <- L.weakly_greater dict l r
    B.assert [w]    
    s <- L.strictly_greater dict l r
    su <- B.constant $ strict u
    B.and [ s, su ]

term dict dim funmap varmap t = case t of
    Var v -> return 
        $ projection dim (M.size varmap) (varmap M.! v)
    Node f args -> do
        gs <- forM args $ term dict dim funmap varmap 
        L.substitute dict (funmap M.! f) gs

-- TODO: move this to Satchmo.SMT.Linear
projection dim n i = 
   L.Linear { L.abs = M.Zero (dim,1)
            , L.lin = do
                   k <- [ 0 .. n-1]
                   return $ if k == i
                          then M.Unit (dim,dim)
                          else M.Zero (dim,dim)
            }


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

instance Pretty a => Show (TPDB.DP.Marked a) where
    show = render . pretty

main = do
   argv <- getArgs
   case getOpt Permute options argv of
       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os
           sys <- get_trs path
           case dp opts of
               False -> handle opts sys
               True -> handle_dp opts $ TPDB.DP.dp sys
       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "MB" options
