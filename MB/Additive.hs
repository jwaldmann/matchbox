{-# LANGUAGE OverloadedStrings #-}

-- | simplex solver for linear weights.
-- can only be applied 
-- for non-duplicating systems (not checked here!)

module MB.Additive where

import qualified MB.Matrix 

import Numeric.LinearProgramming

import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Integer as I

import TPDB.Data

import Data.Set ( Set )
import qualified Data.Set as S

import Data.Map ( Map )
import qualified Data.Map as M

import Control.Monad (guard, when)
import Text.PrettyPrint.HughesPJ
import TPDB.Pretty (pretty, Pretty (..))
import Data.List ( sort )

is_linear sys = and $ do
    u <- rules sys
    let vcount t = M.fromListWith (+) $ do
            ( p, Var v ) <- positions t
            return ( v, 1 )
    return $ vcount (lhs u) == vcount (rhs u)

-- | need to convert from doubles to integers,
-- since GLPK simplex solver insists on doubles.

eps = 1e-5 -- urgh

toint opt fm = 
    let values = sort $ M.elems fm
        diffs = sort $ zipWith (-) (tail values) values
        delta = case filter (> eps) diffs of
            [] -> error $ unlines
                [ "MB.Additive: no (large) diff?"
                , show values
                ]
            d : _ -> d
    in  M.map ( \ v ->  round $ v / delta ) fm
        
mkinter opt sig fm = M.fromList $ do
    ( c, w ) <- M.toList $ toint opt fm
    return ( c, L.Linear { L.dim = (1,1)
                         , L.abs = M.Matrix { M.dim = (1,1), M.contents = [[w]] }
                         , L.lin = replicate ( sig M.! c ) 
                                 $ M.Unit { M.dim = (1,1) } 
                         } )

find sys = do
    guard $ is_linear sys
    let arities = M.fromList $ do
            u <- rules sys ; t <- [ lhs u, rhs u ]
            Node f args <- subterms t
            return ( f, length args )
        sig = M.keys arities
        idxOf = M.fromList $ zip sig [ 1 .. ]
        varOf = M.fromList $ zip [ 1 .. ] sig       
    let count t = M.fromListWith (+) $ do 
            Node f args <- subterms t ; return ( f, 1 )
        for = flip map
        differences = for ( rules sys ) $ \ u -> 
                 M.filter ( /= 0)
               $ M.unionWith (+) (count $ lhs u)
               $ M.map negate (count $ rhs u)
        total = foldr (M.unionWith (+)) M.empty differences
        global = ( for sig $ \ s -> 1 # idxOf M.! s ) :==: 1 
        monotonic = for differences $ \ d -> 
                ( for (M.toList d) $ \ (var,coeff) -> coeff # idxOf M.! var ) :=>: 0
        goal = Maximize $ do 
            idx <- [ 1 .. length sig ]      
            return $ M.findWithDefault 0 ( varOf M.! idx ) total
    Optimal (opt, values) <- return $
        simplex goal (Sparse $ global : monotonic)  []
    guard $ opt > eps    

    let double_int = M.fromList 
                 $ for ( zip [1..] values )
                 $ \ (i,v) -> (varOf M.! i, v)
        int = mkinter opt arities double_int
    let dict = L.linear $ M.matrix I.direct
    case MB.Matrix.remaining False dict 1 int sys of
        Right sys' -> do
             when ( length (rules sys) 
                    == length (rules sys')) $ do 
                 error $ render $ vcat
                    [ "MB.additive: not removing any rule?"
                    , "input system: " <+> pretty sys
                    ,  "interpretation: " <+> pretty double_int
                    ]
             return ( int, sys' )
	Left err ->  error $  render $ vcat
                    [ "MB.additive: verification error"
                    , "input system: " <+> pretty sys
                    , "interpretation: " <+> pretty int
                    , "message:" <+> vcat (map text $ lines  err)
                    ]

instance Pretty Double where 
    pretty = text . show