{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}

module SMT.Satchmo.Interval where

import qualified SMT.Dictionary  as D
import qualified SMT.Semiring.Class as C


import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code as C
import qualified Satchmo.Boolean as B

import Control.Monad (forM, guard, when, replicateM)
import Control.Applicative

import Data.Ix ( range, inRange, Ix )
import Data.List ( tails )

data Number = Number
    { contents :: [ B.Boolean ]
      
    }

dict :: ( C.Semiring a, Ix a )
     => D.Domain
     -> [(a,a)]
     -> D.Dictionary Satchmo.SAT.Mini.SAT Number a B.Boolean
dict dom ints =
  let bits = length ints
  in D.Dictionary
  { D.domain = dom
  , D.number = do
        cs <- replicateM bits B.boolean
        B.assert cs
        forM (filter (not. null) $ tails cs) $ \ (c:ds) ->
          forM ds $ \ d -> B.assert [ B.not c, B.not d ]
        return $ Number { contents = cs }
  , D.nconstant = \ n -> do
        cs <- forM ints $ \ int ->
          B.constant $ inRange int n
        return $ Number { contents = cs }
  , D.decode = \ a -> do
        cs <- C.decode $ contents a
        return $ head $ do
            ((lo,hi), True) <- zip ints cs
            return lo
  , D.positive = prop1 C.strictly_positive ints
  , D.ge = prop2 C.ge ints 
  , D.gt = prop2 C.gt ints
  , D.add = fun2 C.plus  ints
  , D.times = fun2 C.times ints
    , D.boolean = B.boolean
    , D.bconstant = B.constant
    , D.and = B.and
    , D.or = B.or
    , D.not = return . B.not 
    , D.beq = B.equals2
    , D.assert = B.assert
  }

fun2 f ints = \ l r -> do
  cs <- forM ints $ \ int -> do
      pss <- forM (zip ints $ contents l) $ \ (xint@(lox,hix),x) ->
        forM (zip ints $ contents r) $ \ (yint@(loy,hiy),y) ->
          -- if any (inRange int) $ do
          -- a <- range xint ; b <- range yint ; return $ f a b
          if all (inRange int) [ f lox loy, f lox hiy, f hix loy, f hix hiy ]
          then B.and [x,y] else B.constant False
      B.or $ concat pss
  B.assert cs    
  return $ Number { contents = cs }
            
prop2 p ints = \ l r -> do
      good <- forM (zip ints $ contents l) $ \(xint, x) ->
        forM ( zip ints $ contents r) $ \ (yint, y) ->
          if -- all2 p (range xint) (range yint)
             all2' p xint yint
             then B.and[x,y] else B.constant False
      g <- B.or $ concat good
      bad <-  forM (zip ints $ contents l) $ \(xint, x) ->
        forM ( zip ints $ contents r) $ \ (yint, y) ->
          if not $
             -- all2 p (range xint) (range yint)
             all2' p xint yint
             then B.and[x,y] else B.constant False
      b <- B.or $ concat bad
      B.and [ g, B.not b ]
      
all2 p xs ys = all ( \ x -> all (p x) ys ) xs

-- | assume p is monotone (if it holds for all endpoints,
-- then it holds for the interval)
all2' p (lo1,hi1) (lo2,hi2) =
  p lo1 lo2 && p lo1 hi2 && p hi1 lo2 && p hi1 hi2

prop1 p ints = \ x -> do
  good <- forM (zip ints $ contents x) $ \ (int,c) ->
          if -- all p (range int)
            all' p int
          then return c else B.constant False
  g <- B.or good                             
  bad <- forM (zip ints $ contents x) $ \ (int,c) ->
          if not $
             -- all p (range int)
             all' p int
          then return c else B.constant False
  b <- B.or bad
  B.and [ B.not b, g ]

all' p (lo,hi) = p lo && p hi
  

