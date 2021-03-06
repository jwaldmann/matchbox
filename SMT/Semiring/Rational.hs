{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}

module Semiring.Rational where

import Data.Ratio
import Semiring.Class    

instance Semiring Rational where    
    strictness _ = Full
    nonnegative x = x >= 0 ; strictly_positive x = x >= 1 
    ge = (>=) ; gt = (>)
    plus = (+) ; zero = 0 ; times = (*) ; one = 1
