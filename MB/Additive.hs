{-# LANGUAGE OverloadedStrings #-}

-- | simplex solver for linear weights.
-- can only be applied 
-- for non-duplicating systems (not checked here!)

module MB.Additive where

import Debug.Trace

import qualified MB.Matrix 
import Compress.Common

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

eps = 1e-6 -- urgh

geeceedee x y = 
          if abs y < eps then x
          else let d = truncate (x/y) :: Int
                   r = x - fromIntegral d * y
               in  geeceedee y r

geeceedees xs = foldr geeceedee 1 xs


toint opt fm = 
    let delta = geeceedees 
              $ filter (> eps) $ M.elems fm
        fm1 = M.map ( / delta ) fm
        fm2 = M.map round fm1
    in  
{-
    trace ( unlines [ show $ pretty fm
                        , show $ pretty fm1
                        , show delta
                        , show $ pretty fm2 
                        ] )
-}
                        fm2
        
mkinter opt sig fm = M.fromList $ do
    ( c, w ) <- M.toList $ toint opt fm
    return ( c, L.Linear { L.dim = (1,1)
                         , L.abs = M.Matrix { M.dim = (1,1), M.contents = [[w]] }
                         , L.lin = replicate ( sig M.! c ) 
                                 $ M.Matrix { M.dim = (1,1), M.contents = [[1]] } 
                         } )


-- | top = True: prove relative top termination
-- (it is not allowed to remove weak rules).
-- top = False: prover relative termination
-- (it is allowed to remove weak rules).

find :: ( Pretty s, Ord s , Pretty v, Ord v)
     => Bool 
     -> TRS v s 
     -> Maybe (Map s (L.Linear (M.Matrix Integer)), TRS v s)
find top sys = finder top sys plain_continuation

find_compress :: ( Pretty s, Ord s , Pretty v, Ord v)
     => Bool 
     -> TRS v (Sym s) 
     -> Maybe (Map s (L.Linear (M.Matrix Integer)), TRS v (Sym s))
find_compress top sys = 
    let esys = (expand_all_trs sys) 
    in  finder top esys $ compress_continuation sys

finder top sys k = do

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
        differences us = for us $ \ u -> 
                 M.filter ( /= 0)
               $ M.unionWith (+) (count $ lhs u)
               $ M.map negate (count $ rhs u)
        strict_diffs = differences 
               $ filter strict $ rules sys
        weak_diffs = differences 
               $ filter ( not . strict ) $ rules sys
        all_diffs = weak_diffs ++ strict_diffs
        total = foldr (M.unionWith (+)) M.empty 
              $ if top then strict_diffs else all_diffs
        global = ( for sig $ \ s -> 1 # idxOf M.! s ) :==: 1 
        monotonic = for all_diffs $ \ d -> 
                ( for (M.toList d) $ \ (var,coeff) -> coeff # idxOf M.! var ) :=>: 0
        goal = Maximize $ do 
            idx <- [ 1 .. length sig ]      
            return $ M.findWithDefault 0 
                   ( varOf M.! idx ) total

    let result = 
          simplex goal (Sparse $ global : monotonic) []

    Optimal (opt, values) <- return result
    guard $ opt > eps    

    let double_int = M.fromList 
                 $ for ( zip [1..] values )
                 $ \ (i,v) -> (varOf M.! i, v)
        int = mkinter opt arities double_int
    let dict = L.linear $ M.matrix I.direct

    k top dict 1 int double_int sys

plain_continuation top dict dim int double_int sys = 
    case MB.Matrix.remaining top dict dim int sys of
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

compress_continuation sys top dict dim int double_int expsys = 
    case MB.Matrix.remaining_compressed top dict dim int sys of
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