{-# OPTIONS -fallow-overlapping-instances #-}

-- | simplex solver for linear weights.
-- can only be applied 
-- for non-duplicating systems (not checked here!)

module MB.Additive where

import MB.Simplex

import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.SMT.Linear as L


import TPDB.Data

import Data.Ratio
import Data.Array

import Data.Set ( Set )
import qualified Data.Set as S

import Data.Map ( Map )
import qualified Data.Map as M

import Control.Monad (guard)

is_linear sys = and $ do
    u <- rules sys
    let vcount t = M.fromListWith (+) $ do
            ( p, Var v ) <- positions t
            return ( v, 1 )
    return $ vcount (lhs u) == vcount (rhs u)


    
mkinter sig fm = M.fromList $ do
    ( c, w ) <- M.toList fm
    return ( c, L.Linear { L.dim = (1,1)
                         , L.abs = M.Matrix { M.dim = (1,1), M.contents = [[w]] }
                         , L.lin = replicate ( sig M.! c ) 
                                 $ M.Unit { M.dim = (1,1) } 
                         } )


find tes = do
    guard $ is_linear tes
    let sig = M.fromList $ do
            u <- rules tes ; t <- [ lhs u, rhs u ]
            Node f args <- subterms t
            return ( f, length args )
        ( fm, tabin ) = tableau (M.keysSet sig) tes
	tabout = short_simplex tabin
    fm <- case status tabout of
            Positive -> 
                Just $ continue fm tabout
	    Optimal | contents tabout ! (0,0) > 0 -> 
                Just $ continue fm tabout
	    _ -> 
                Nothing
    let weight t = sum $ do
            Node f _ <- subterms t
            return $ fm M.! f
        remaining = do
            u <- rules tes
            case compare (weight $ lhs u) (weight $ rhs u) of
                GT ->  [ ]
                EQ ->  [u]
                LT ->  error "MB.additive"
    return ( mkinter sig fm, tes { rules = remaining } )

continue fm tab =  
    let sol = solution tab
        wei = M.fromList $ do
           ( c, i ) <- M.toList fm
           return ( c, sol ! i )
        common = foldr1 lcm $ map denominator $ M.elems wei
    in  fmap ( \ w -> numerator w * common `div` denominator w ) wei

--------------------------------------------------------------------------

tableau :: ( Ord c )
	=> Set c
        -> RS c ( Term v c ) 
       -> ( Map  c Int 
	  , Tableau Rational 
          )  -- ^ ( maps letter to index, simplex input table)
tableau sig tes = 
    let sigma = S.toList sig
        fm = M.fromList $ zip sigma [ 1 .. ] 
	mf = M.fromList $ zip [ 1.. ] sigma
        nrules = length $ rules tes
	nvars = length sigma
	diffs = array ((1,0), (nrules, nvars)) $ do 
	      ( i, rule )  <- zip [ 1 .. ] $ rules tes
	      ( j ) <- [ 0 .. nvars  ]
	      let Just c = M.lookup j mf
		  l = count c $ lhs rule
		  r = count c $ rhs rule
              let e = if j == 0 
		      then 0 -- target
		      else negate $ fromIntegral $ l - r -- difference
	      return ( (i,j) , e )
	a = array ((0,0),(nrules+1, nvars)) $ do
	       (p,q) <- range  ((0,0),(nrules+1, nvars)) 
	       let e = if 0 == p
		       then sum $ do 
				p' <- [ 1 .. nrules ]
				return $ diffs ! (p',q)
		       else if nrules + 1 == p
		       then 1 -- sum of variables
		       else diffs ! (p,q)
	       return ( (p,q), e )
    in  ( fm
	, MB.Simplex.make a
	)


-- | number of letter  c   occurences in this term
count c = length . filter ( == c ) . symsl
	

