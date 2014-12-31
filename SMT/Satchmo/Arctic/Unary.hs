{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}

module SMT.Satchmo.Arctic.Unary where

import qualified SMT.Dictionary  as D
import qualified SMT.Semiring.Arctic as A

import qualified Data.Map as M

import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code as C
import qualified Satchmo.Boolean as B
import Control.Monad (forM, guard, when, replicateM)
import Control.Applicative

data Arctic = Arctic { contents :: [ B.Boolean ]
                     }

minus_infinite = B.not . head . contents

dict :: Int 
     -> D.Dictionary Satchmo.SAT.Mini.SAT Arctic ( A.Arctic Integer ) B.Boolean
dict bits = D.Dictionary
  { D.domain = D.Arctic 
  , D.number = Arctic <$> do
        bs <- replicateM bits B.boolean
        forM ( zip bs $ tail bs ) $ \ (b,b') ->
            B.assert [ B.not b', b ]
        return bs
  , D.nconstant = \ n -> do
        t <- B.constant True ; f <- B.constant False
        let nu k = Arctic
                 $ replicate k t ++ replicate (bits - k) f
        return $ nu $ fromInteger $ case n of
             A.Minus_Infinite -> 0
             A.Finite c -> c+1
  , D.decode = \ a -> do
        b : bs <- C.decode $ contents a
        return $ if not b then A.Minus_Infinite
                 else A.Finite $ fromIntegral $ length
                               $ takeWhile id bs
  , D.positive = \ x -> return $ B.not $ minus_infinite x
  , D.ge = \ l r -> do
      ps <- forM (zip (contents l) (contents r) ) $ \ (x,y) ->
          B.or [ x, B.not y ]
      B.and ps
  , D.gt = \ l r -> do
      ps <- forM (zip (contents l) (contents r) ) $ \ (x,y) ->
          B.and [ x, B.not y ]
      B.or $ minus_infinite r : ps
  , D.add = \ x y -> Arctic <$> do
      forM (zip (contents x)(contents y)) $ \ (x,y)->
               B.or [x,y] 
  , D.times = \ s t -> Arctic <$> do
          m <- B.or [ minus_infinite s, minus_infinite t ]
          let a = contents s ; b = contents t
          let width = length a
          when ( length b /= width ) 
               $ error "Arctic.times: different bit widths"
          pairs <- sequence $ do
              (i,x) <- zip [0 .. ] a
              (j,y) <- zip [0 .. ] b
              guard $ i+j <= width
              return $ do z <- B.and [x,y] ; return (i+j, [z])
          cs <- forM ( map snd $ M.toAscList $ M.fromListWith (++) pairs ) B.or
          -- overflow is not allowed
          B.assert [ B.not $ last cs ]
          forM (init cs) $ \ c -> B.and [ B.not m, c ]

    , D.boolean = B.boolean
    , D.bconstant = B.constant
    , D.and = B.and
    , D.or = B.or
    , D.not = return . B.not 
    , D.beq = B.equals2
    , D.assert = B.assert
  }

