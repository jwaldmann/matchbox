module SMT.Semiring.Integer where

import SMT.Semiring

instance Semiring Integer where    
  strictness _ = Full
  nonnegative x = x >= 0 
  strictly_positive x = x >= 1 
  ge = (>=) ; gt = (>)
  plus = (+) ; zero = 0 ; times = (*) ; one = 1
