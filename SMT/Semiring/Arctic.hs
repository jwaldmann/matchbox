module SMT.Semiring.Arctic where

import SMT.Semiring.Class
import Data.Ix

data Arctic a = Minus_Infinite | Finite a deriving (Eq, Ord)

instance Functor Arctic where
    fmap f a = case a of
        Minus_Infinite -> Minus_Infinite
        Finite x -> Finite $ f x

instance Show a => Show ( Arctic a ) where 
    show a = case a of
        Minus_Infinite -> "-"
        Finite x -> show x

-- | NOTE: range is partial:
-- range (Minus_Infinite, Finite _) is undefined.

instance Ix a => Ix (Arctic a) where
    inRange (lo,hi) x = lo <= x && x <= hi
    range (Minus_Infinite,Minus_Infinite) = [Minus_Infinite]
    range (Finite lo, Finite hi) = map Finite $ range (lo,hi)

instance (Ord a, Num a) => Semiring (Arctic a) where
    strictness _ = Half
    nonnegative a = True -- ??
    strictly_positive a = case a of Finite x -> x >= 0 ; _ -> False
    ge = (>=)
    gt x y = y == Minus_Infinite || (x > y)
    plus = max
    zero = Minus_Infinite
    times x y = case (x,y) of
        (Finite a, Finite b) -> Finite (a+b)
        _ -> Minus_Infinite
    one = Finite 0         
