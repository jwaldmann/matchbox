{-# language OverloadedStrings #-}
{-# language FlexibleContexts #-}    

module MB.Complexity where

import MB.Proof.Type
import TPDB.Pretty
import MB.Pretty ((</>), oneline)

import qualified SMT.Linear as L
import qualified SMT.Matrix as M

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.Writer

for = flip map

-- FIXME: these declarations should be hidden elsewhere
auspack :: Num s => M.Matrix s -> M.Matrix s
auspack m = case m of
  M.Zero {M.dim=(to,from)} ->
    M.Matrix (M.dim m) $ replicate to $ replicate from 0
  M.Unit {M.dim=(to,_)} ->
    M.Matrix (M.dim m) $ for [1..to] $ \ r -> for [1..to] $ \ c ->
      if r == c then 1 else 0
  M.Matrix{} -> m
larger a b | M.dim a == M.dim b =
  M.Matrix (M.dim a) $ zipWith (zipWith max) (M.contents a) (M.contents b)
times a b =
  let (ta,fa) = M.dim a ; (tb,fb) = M.dim b
  in  M.Matrix (ta,fb)
      $ for (M.contents a) $ \ row ->
       for (transpose $ M.contents b) $ \ col ->
       sum $ zipWith (*) row col
power a 1 = a
power a e | e > 1 =
    let (d,m) = divMod e 2 ; h = power a d ; s = times a a
    in if m == 0 then s else times s a
istriangular :: (Num s, Ord s) => M.Matrix s -> Bool
istriangular mat =
  and $ for ( zip [1..] $ M.contents mat ) $ \ (r,row) ->
  and $ for (zip [1..] row) $ \ (c,ent) ->
  case compare r c of  GT -> ent == 0 ; EQ -> abs ent <= 1 ; _ ->  True
maximum_matrix i = foldr1 larger $ do
  (f,l) <- M.toList $ mapping i
  map auspack $ L.lin l


degree :: Proof v s -> Maybe (Int, Doc)
degree p = do
  Matrix_Interpretation_Natural i _ _ <- return $ reason p
  
  let mm = maximum_matrix i
      d0 = dimension i ; bound = foldl lcm 1 [ 2 .. d0 ]      
  let lower Nothing that = that
      lower this Nothing = this
      lower this@(Just (i,d)) that@(Just (j,e)) = if i <= j then this else that
  foldr lower Nothing $ for [1..bound] $ triangular_degree i mm


triangular_degree
  :: Interpretation v s Integer -> M.Matrix Integer -> Int -> Maybe (Int, Doc)
triangular_degree i m e = do
  let me = power m e
  guard $ istriangular me
  let (d0,_) = M.dim m
  let nzs = map (> 0) $ M.diagonal me
  let d1 = length $ filter id nzs
      r1 = vcat [ "point-wise maximum of linear coefficients is M = " </> pretty m
                , "consider M^" TPDB.Pretty.<> pretty e TPDB.Pretty.<> " = " </> pretty me
                , "is triangular matrix of dimension" <+> pretty d0
                , "diagonal contains" <+> pretty d1 <+> "non-zeros"
                ]
  return $ case constraint i of
    Just c ->
      let (r,ds) =
            runWriter $ do
              tell [ r1 ]
              reduce_shape nzs (L.lin $ restriction c)
      in (r, vcat ds)
    Nothing -> (d1,r1)

pic nzs =
        pretty $ map ( \ nz -> if nz then text "*" else "0" ) nzs

reduce_shape nzs [ m ] = do
  kills <- forM (M.contents m) $ \ line -> do
    let (pre,post) = span (<= 0) line
        ks = do (i,x) <- zip [0 :: Int ..] pre ; guard $ x < 0 ; return i
    when (not $ null ks) $ tell [ vcat
       [ "by constraint" <+> oneline line
       , "entries at positions" <+> oneline ks
         <+> "are bounded by a linear function of later ones"
       , "and can be ignored for computing the degree"
       ] ]
    return $ S.fromList ks
  let kill =  S.unions kills 
      nzs' = do (i,nz) <- zip [0..] nzs
                return $ nz && S.notMember i kill
      d2 = length $ filter id nzs'
  when (nzs' /= nzs) $ tell [ vcat
    [ "resulting shape is" </> pic nzs'
    , "with" <+> pretty d2 <+> "nonzeros"
    ] ]
  return d2    
