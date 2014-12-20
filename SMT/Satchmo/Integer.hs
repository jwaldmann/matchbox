module SMT.Satchmo.Integer where

import Prelude hiding ( not, and, or )
import qualified Prelude
import Control.Monad.Error ( throwError )


import SMT.Dictionary

import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code
import qualified Satchmo.Boolean as B

import qualified Satchmo.Binary as Bin
import qualified Satchmo.Binary.Op.Fixed  

import Control.Monad ( forM )

dict :: Int 
  -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number Integer B.Boolean
dict bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(fixed)" ]
    , domain = SMT.Dictionary.Int
    , nbits = bits
    , number = Bin.number bits
    , decode = Satchmo.Code.decode
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = Satchmo.Binary.Op.Fixed.add
    , times = Satchmo.Binary.Op.Fixed.times
    , dot_product = Satchmo.Binary.Op.Fixed.dot_product bits
    , positive = \ n -> B.or $ Bin.bits n
    , gt = Bin.gt
    , ge = Bin.ge
    , neq = Bin.eq
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    }
