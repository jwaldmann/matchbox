module SMT.Satchmo.Integer.Native where


import Prelude hiding ( not, and, or )
import qualified Prelude
import Control.Monad (when)

import SMT.Dictionary

import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code as C
import qualified Satchmo.Boolean as B
import qualified Satchmo.Counting as C

import qualified Satchmo.Integer as I

import Control.Monad ( forM )
import Control.Applicative
import qualified Data.Map.Strict as M

dict :: Int 
  -> Dictionary Satchmo.SAT.Mini.SAT I.Number Integer B.Boolean
dict bits = Dictionary
    { info = unwords [ "native-integer", "bits:", show bits, "(fixed)" ]
    , domain = SMT.Dictionary.Int
    , nbits = bits
    , number = do n <- I.number bits ; B.assert [ B.not $ sign n ] ; return n
    , small_nn_number = do
        b <- B.boolean ; s <- B.constant False
        return $ I.make [ b, s ]
    , any_number = I.number bits
    , small_number = I.number 2
    , decode = \ n -> do
        bs <- forM (I.bits n) C.decode
        let v = fromBinary bs ; h = 2^(I.width n - 1)
        return $ if v < h then v else v - 2*h
    , nconstant = \ i -> I.constant bits i
    , boolean = B.boolean
    , bconstant = B.constant
    , add = \ x y -> I.add x y
    , times = \ x y -> I.times x y
    , positive = \ x -> do z <- I.constant bits 0 ; I.gt x z
    , nonnegative = \ x -> do z <- I.constant bits 0 ; I.ge x z
    , gt =  I.gt
    , ge = I.ge
    , neq = I.eq
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    , atmost = \ k bs -> C.atmost k bs
    }

sign n = last $ I.bits n

fromBinary bs = foldr ( \ b n -> 2*n + if b then 1 else 0 ) 0 bs
