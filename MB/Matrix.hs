{-# language OverloadedStrings #-}
{-# language DeriveGeneric #-}

module MB.Matrix where

import MB.Options
import MB.Pretty
import MB.Proof (Interpretation (..))

import qualified MB.Count

import TPDB.Data
import TPDB.Pretty
import qualified TPDB.DP

import qualified Compress.Common as CC
-- import qualified Compress.Simple as CS
-- import qualified Compress.Paper as CP

import qualified Satchmo.SMT.Exotic.Semiring as S
import qualified Satchmo.SMT.Dictionary as D
import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.Boolean as B
import qualified Satchmo.SAT.Mini

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad ( forM, void, foldM )
import Control.Monad.Identity
-- import Text.PrettyPrint.HughesPJ (render, vcat, hsep, ( <+>), text )
import System.IO

import Data.Hashable

-- | note: we are assuming that we get a compressed system.
-- the choice of the compressor should be done outside this module.
-- so we only import Compress.Common (and none of the implementations).
-- We do return an interpretation for the _original_ signature
-- (because that is needed for independent verification)
-- and the remaining rules in the _compressed_ signature
-- (because we might want to avoid re-compression).

handle :: (Show s, Hashable s, Ord v, Show v, Pretty v, Pretty s, Ord s
          , S.Semiring val, Pretty val)
       => (Int -> D.Dictionary Satchmo.SAT.Mini.SAT num val B.Boolean )
       -> D.Dictionary (Either String) val val Bool
       -> Options -> TRS v (CC.Sym s)
       -> IO ( Maybe ( Interpretation s val
                     , TRS v (CC.Sym s)))
handle encoded direct opts sys = do
    eprint $ pretty_short sys
    eprint $ show opts

    let count = MB.Count.run $ do
            system MB.Count.linear (dim opts) sys
    hPutStrLn stderr $ show count

    out <- Satchmo.SAT.Mini.solve $ do
        let ldict = L.linear mdict
            mdict = M.matrix idict
            idict = encoded (bits opts)
        funmap <- system ldict (dim opts) sys
        return $ mdecode ldict $ originals_only funmap

    case out of
        Just f -> do
            eprint $ pretty f
            let dict = L.linear $ M.matrix direct
            case remaining_compressed False dict (dim opts) f sys of
                Right sys' -> return 
                   $ Just ( Interpretation 
                            { dimension = dim opts
                            , domain = D.domain direct
                            , mapping = f
                            }
                          , sys' )
                Left err -> error $ render $ vcat
                    [ "verification error"
                    , "input system: " <+> pretty sys
                    , "interpretation: " <+> pretty f
                    , "message:" <+> vcat (map text $ lines  err)
                    ]
        Nothing -> return Nothing

handle_dp :: (Show s, Hashable s, Ord v, Show v, Pretty v, Pretty s, Ord s
          , Pretty val, S.Semiring val)
       => (Int -> D.Dictionary Satchmo.SAT.Mini.SAT num val B.Boolean )
       -> D.Dictionary (Either String) val val Bool
       -> Options -> TRS v (CC.Sym (TPDB.DP.Marked s))
       -> IO ( Maybe ( Interpretation (TPDB.DP.Marked s) val
                     , TRS v (CC.Sym (TPDB.DP.Marked s))))
handle_dp encoded direct opts sys = do
    eprint $ pretty_short sys
    eprint $ show opts

    let count = MB.Count.run $ do
            system_dp MB.Count.linear (dim opts) sys
    hPutStrLn stderr $ show count

    out <- Satchmo.SAT.Mini.solve $ do
        let ldict = L.linear mdict
            mdict = M.matrix idict
            idict = encoded (bits opts) 
        funmap <- system_dp ldict (dim opts) sys
        return $ mdecode ldict $ originals_only funmap

    case out of
        Just f -> do
            eprint $ pretty f
            let dict = L.linear $ M.matrix direct 
                rc = remaining_compressed True dict (dim opts) f sys
            eprint $ pretty rc
            case rc of
                Right sys' -> return 
                   $ Just ( Interpretation 
                            { dimension = dim opts
                            , domain = D.domain direct
                            , mapping = f
                            }
                          , sys' )
                Left err -> error $ render $ vcat
                    [ "verification error"
                    , "input system: " <+> pretty sys
                    , "interpretation: " <+> pretty f
                    , "message:" <+> vcat (map text $ lines  err)
                    ]
        Nothing -> return Nothing
    

-- | check that all rules are weakly decreasing.
-- returns the system with the rules that are not strictly decreasing.
remaining_compressed top dict dim funmap sys = do
    uss <- forM ( rules sys ) $ \ u -> do
        s <- traced_rule top dict dim funmap $ fmap CC.expand_all u 
        return ( u, s )
    return $ sys { rules = map fst $ filter (not . snd) uss }

remaining top dict dim funmap sys = do
    uss <- forM ( rules sys ) $ \ u -> do
        s <- traced_rule top dict dim funmap u 
        return ( u, s )
    return $ sys { rules = map fst $ filter (not . snd) uss }

traced doc con = case con of
    Right x -> return x
    Left msg -> 
        Left $ show $ vcat [ doc , text msg ]

traced_rule top dict dim funmap u = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term dict dim funmap varmap $ lhs u
    r <- term dict dim funmap varmap $ rhs u
    w <- L.weakly_greater dict l r
    traced ( vcat [ "rule:" <+> pretty u
                  , "left:" <+> pretty l
                  , "right: " <+> pretty r
                  ]
           ) $ L.assert dict [w] 
    case relation u of
        Strict -> L.strictly_greater dict l r
        Weak   -> case top of
            False -> L.strictly_greater dict l r
            True  -> L.bconstant dict  False -- cannot remove

mdecode dict f = do
    pairs <- forM ( M.toList f) $ \ (k,v) -> do
        w <- L.decode dict v
        return (k,w)
    return $ M.fromList pairs 

originals_only funmap = M.fromList $ do
    ( CC.Orig o, f ) <- M.toList funmap
    return ( o, f )

-- | assert that at least one rule can be removed.
-- returns interpretation of function symbols.
system dict dim sys = do
    let (originals, digrams) = CC.deep_signature  sys
    opairs <- forM originals $ \ (f,ar) -> do
        l <- L.make dict ar (dim , dim)
        s <- L.positive dict l
        L.assert dict [s]
        return (f, l)
    funmap <- foldM (digger dict) (M.fromList opairs) digrams
    flags <- forM (rules sys) 
             $ rule dict dim funmap
    L.assert dict flags 
    return funmap

-- | assert that at least one rule can be removed.
-- returns interpretation of function symbols.
system_dp dict dim sys = do
    let (originals, digrams) = CC.deep_signature  sys
    opairs <- forM originals $ \ (f,ar) -> do
        let topdim = case f of
                CC.Orig (TPDB.DP.Marked   {}) -> 1
                CC.Orig (TPDB.DP.Original {}) -> dim
        l <- L.make dict ar (topdim , dim)
        -- FIXME: this is a hack:
        when ( L.domain dict == D.Arctic ) $ do
            s <- L.positive dict l -- wrong name
            L.assert dict [s]
        return (f, l)
    funmap <- foldM (digger dict) ( M.fromList opairs ) digrams
    flags <- forM (rules sys) 
             $ rule_dp dict dim funmap
    L.assert dict flags 
    return funmap


digger dict m (CC.Dig d, _) = do
    let get s x = M.findWithDefault ( error
                $ unlines [ unwords [ "missing", s, "of", show d ] 
                        , show $ M.keys m
                        ] ) x m
        p = get "parent"  (CC.parent d) 
        pos = CC.position d - CC.position_index_start
        (pre, this : post) = 
              splitAt pos $ L.lin p
        c = get "child"   (CC.child d) 
    h <- L.substitute dict
        ( L.Linear {L.abs = L.abs p
           , L.lin = [ this ]
           } ) [ c ]
    let fg = L.Linear { L.abs = L.abs h
             , L.lin = pre ++ L.lin h ++ post
             , L.dim = (L.to p, L.from c)
             }
    return $ M.insertWith 
           (error "cannot happen")
           (CC.Dig d) fg m

-- | asserts weak decrease and returns strict decrease
rule dict dim funmap u = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term dict dim funmap varmap $ lhs u
    r <- term dict dim funmap varmap $ rhs u
    w <- L.weakly_greater dict l r
    L.assert dict [w]
    L.strictly_greater dict l r

-- | asserts weak decrease and 
-- returns strict decrease (for strict rules)
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
    Node f [] -> do
        let a = L.abs $ funmap M.! f 
        return $ L.Linear
               { L.abs = a
               , L.lin = replicate (M.size varmap) 
                       $ M.Zero (M.to a ,dim)
               }
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

