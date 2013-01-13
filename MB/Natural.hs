{-# language OverloadedStrings #-}

module MB.Natural where

import MB.Options
import MB.Pretty

import TPDB.Data
import TPDB.Pretty
import qualified TPDB.DP

import qualified Compress.Common as C
import qualified Compress.Simple as C

import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M
-- import qualified Satchmo.Boolean as B
import qualified Satchmo.SAT.Mini

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad ( forM, void, foldM )
import Text.PrettyPrint.HughesPJ (render, vcat, hsep, ( <+>), text )



handle :: (Show s, Ord v, Pretty v, Pretty s, Ord s)
       => Options -> TRS v s 
       -> IO ( Maybe ( M.Map s (L.Linear (M.Matrix Integer))
                     , TRS v s))
handle opts sys = do
    eprint $ pretty sys
    eprint $ show opts

    let (co, trees) = 
          ( if compress opts
            then C.compress else C.nocompress 
          ) $ rules sys

    out <- Satchmo.SAT.Mini.solve $ do
        let ldict = L.linear mdict
            mdict = M.matrix idict
            idict = I.binary_fixed (bits opts)
        funmap <- system ldict (dim opts) trees
        return $ mdecode ldict $ originals_only funmap

    case out of
        Just f -> do
            eprint $ pretty f
            let dict = L.linear $ M.matrix $ I.direct
            case remaining dict (dim opts) f sys of
                Right sys' -> return $ Just ( f, sys' )
                Left err -> error $ render $ vcat
                    [ "verification error"
                    , "input system: " <+> pretty sys
                    , "interpretation: " <+> pretty f
                    ]
        Nothing -> return Nothing

handle_dp :: (Show s, Ord v, Pretty v, Pretty s, Ord s)
       => Options -> TRS v (TPDB.DP.Marked s) 
       -> IO ( Maybe ( M.Map (TPDB.DP.Marked s) (L.Linear (M.Matrix Integer))
                     , TRS v (TPDB.DP.Marked s)))
handle_dp opts sys = do
    eprint $ pretty sys
    eprint $ show opts

    let (co, trees) = 
          ( if compress opts
            then C.compress else C.nocompress 
          ) $ rules sys

    out <- Satchmo.SAT.Mini.solve $ do
        let ldict = L.linear mdict
            mdict = M.matrix idict
            idict = I.binary_fixed (bits opts)
        funmap <- system_dp ldict (dim opts) trees
        return $ mdecode ldict $ originals_only funmap

    case out of
        Just f -> do
            eprint $ pretty f
            let dict = L.linear $ M.matrix $ I.direct
            case remaining dict (dim opts) f sys of
                Right sys' -> return $ Just ( f, sys' )
                Left err -> error $ render $ vcat
                    [ "verification error"
                    , "input system: " <+> pretty sys
                    , "interpretation: " <+> pretty f
                    ]
        Nothing -> return Nothing
    

-- | check that all rules are weakly decreasing.
-- returns the system with the rules that are not strictly decreasing.
remaining dict dim funmap sys = do
    uss <- forM ( rules sys ) $ \ u -> do
        s <- rule_dp dict dim funmap u
        return ( u, s )
    return $ sys { rules = map fst $ filter (not . snd) uss }

mdecode dict f = do
    pairs <- forM ( M.toList f) $ \ (k,v) -> do
        w <- L.decode dict v
        return (k,w)
    return $ M.fromList pairs 

originals_only funmap = M.fromList $ do
    ( C.Orig o, f ) <- M.toList funmap
    return ( o, f )

-- | assert that at least one rule can be removed.
-- returns interpretation of function symbols.
system dict dim trees = do
    let ofs = original_function_symbols trees
    opairs <- forM (S.toList ofs) $ \ (f,ar) -> do
        l <- L.make dict ar (dim , dim)
        s <- L.positive dict l
        L.assert dict [s]
        return (f, l)
    funmap <- foldM (digger dict) ( M.fromList opairs )
           $ reverse $ C.extras trees
    flags <- forM (C.roots trees) 
             $ rule dict dim funmap
    L.assert dict flags 
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
    L.assert dict flags 
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
    L.assert dict [w]
    L.strictly_greater dict l r

-- | asserts weak decrease and returns strict decrease (for strict rules)
rule_dp dict dim funmap u = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term dict dim funmap varmap $ lhs u
    r <- term dict dim funmap varmap $ rhs u
    w <- L.weakly_greater dict l r
    L.assert dict [w] 
    case relation u of
        Strict -> L.strictly_greater dict l r
        Weak   -> L.bconstant dict False

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
