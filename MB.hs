-- | simplified Matchbox Termination Prover

import qualified Compress.Simple as C

import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.Boolean as B
import qualified Satchmo.SAT.Mini
import Satchmo.Code

import TPDB.Data
import TPDB.DP
import TPDB.Pretty
import TPDB.Plain.Write
import TPDB.Plain.Read
import TPDB.Input ( get_trs )

import System.Environment
import System.Console.GetOpt
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad ( forM, void, foldM )

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
    
mdecode dict f = do
    pairs <- forM ( M.toList f) $ \ (k,v) -> do
        w <- L.decode dict v
        return (k,w)
    return $ M.fromList pairs 

-- | assert that at least one rule can be removed.
-- returns interpretation of function symbols.
system dict dim trees = do
    let ofs = S.fromList $ do 
           u <- C.roots trees ; t <- [ lhs u, rhs u ]
           Node (f @ C.Orig{}) xs <- subterms t 
           return (f, length xs)
    opairs <- forM (S.toList ofs) $ \ (f,ar) -> do
        l <- L.make dict ar (dim, dim)
        s <- L.positive dict l
        B.assert [s]
        return (f, l)
    let dig m (C.Dig d) = do
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
    funmap <- foldM dig ( M.fromList opairs )
           $ reverse $ C.extras trees

    flags <- forM (C.roots trees) 
             $ rule dict dim funmap
    B.assert flags 
    return funmap

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
             }
    deriving Show

options0 = Options 
         { dim = 5, bits = 5, compress = False }

options = 
    [ Option [ 'd' ] [ "dimension" ]
       ( ReqArg ( \ s opts -> opts { dim = read s }) "Int" ) "vector dimension"
    , Option [ 'b' ] [ "bits" ]
       ( ReqArg ( \ s opts -> opts { bits = read s }) "Int" ) "bit width"
    , Option [ 'c' ] [ "compress" ]
       ( NoArg ( \ opts -> opts { compress = True }) ) "compress"
    ]

main = do
   argv <- getArgs
   case getOpt Permute options argv of
       (os, [path], []) -> do
           let opts = foldl (flip id) options0 os
           sys <- get_trs path
           handle opts sys
       (_,_,errs) -> do
           ioError $ userError $ concat errs
              ++ usageInfo "MB" options
