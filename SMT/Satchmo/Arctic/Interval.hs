module SMT.Satchmo.Arctic.Interval where

import qualified SMT.Satchmo.Interval as I
import qualified SMT.Semiring.Arctic as A
import qualified SMT.Semiring.Class as C
import qualified SMT.Dictionary as D

dict_plain = dict_ $ [0..]
dict_fibs = dict_ $ fibs
dict_twos = dict_ $ 0 : map (2^) [0..]
dict_threes = dict_ $ 0 : map (3^) [0..]

dict_ nums bits =
  let ints = (A.Minus_Infinite, A.Minus_Infinite)
           : map (\(lo,hi) -> (A.Finite lo,A.Finite hi))
             
           (  intervals $ increasing nums )
  in  I.dict D.Arctic ( take bits ints )

fibs = 0 : 1 : zipWith (+) fibs ( tail fibs )

intervals (x:y:zs) = (x, y-1) : intervals (y:zs)

increasing (x:ys) = x : increasing (filter (>x) ys)
