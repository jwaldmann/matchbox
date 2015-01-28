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

degree :: Proof v s -> Maybe (Int, Doc)
degree p = do
  Matrix_Interpretation_Natural i _ _ <- return $ reason p

  let d0 = dimension i
      r0 = "triangular matrices of dimension" <+> pretty d0

  let nzs = map or $ transpose $ do
        (f,l) <- M.toList $ mapping i
        m <- L.lin l
        return $ map (> 0) $ M.diagonal m
  let d1 = length $ filter id nzs
      r1 = vcat [ "for each coefficient matrix of each symbol"
                , "the diagonal is subsumed under" </> pic nzs
                , "which contains" <+> pretty d1 <+> "non-zeros"
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
