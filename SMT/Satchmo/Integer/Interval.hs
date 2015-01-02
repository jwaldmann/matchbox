{-# language PatternSignatures #-}

module SMT.Satchmo.Integer.Interval where

import qualified SMT.Satchmo.Interval as I
import qualified SMT.Semiring.Class as C
import qualified SMT.Semiring.Integer
import qualified SMT.Dictionary as D

dict_plain = dict_ $ [0..]
dict_fibs = dict_ $ fibs
dict_twos = dict_ $ 0 : map (2^) [0..]
dict_threes = dict_ $ 0 : map (3^) [0..]

dict_ ( nums :: [Integer ]) bits =
  let ints = intervals $ increasing nums 
  in  I.dict D.Int ( take bits ints )

fibs = 0 : 1 : zipWith (+) fibs ( tail fibs )

intervals (x:y:zs) = (x, y-1) : intervals (y:zs)

increasing (x:ys) = x : increasing (filter (>x) ys)
