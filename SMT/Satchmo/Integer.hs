-- | integers as difference of naturals

module SMT.Satchmo.Integer where

import Prelude hiding ( not, and, or )
import qualified Prelude
import Control.Monad (when)


import SMT.Dictionary

import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code
import qualified Satchmo.Boolean as B
import qualified Satchmo.Counting as C

import qualified SMT.Satchmo.Natural as N

import qualified Satchmo.Binary as Bin
import qualified Satchmo.Binary.Op.Fixed  

import Control.Monad ( forM )
import Control.Applicative
import qualified Data.Map.Strict as M

data Diff = Difference Bin.Number Bin.Number
          --   | Nonnegative Bin.Number -- for efficiency, later

dict :: Int 
  -> Dictionary Satchmo.SAT.Mini.SAT Diff Integer B.Boolean
dict bits = let n = N.dict bits in Dictionary
    { info = unwords [ "diff-integer", "bits:", show bits, "(fixed)" ]
    , domain = SMT.Dictionary.Int
    , nbits = bits
    , number = Difference <$> number n <*> nconstant n 0
    , smallnumber = Difference <$> smallnumber n <*> nconstant n 0
    , any_number =
      -- TODO possible require that one of them is zero:
      Difference <$> number n <*> number n
    , decode = \ (Difference x y) -> (-) <$> decode n x <*> decode n y
    , nconstant = \ c -> if c >= 0
         then Difference <$> nconstant n (abs c) <*> nconstant n 0
         else Difference <$> nconstant n 0 <*> nconstant n (abs c)
    , boolean = B.boolean
    , bconstant = B.constant
    , add = \ (Difference ax ay) (Difference bx by) ->
         Difference <$> add n ax bx <*> add n ay by
    , times = \ (Difference ax ay) (Difference bx by) ->
         Difference <$> ( app2 (add n)(times n ax bx)(times n ay by ))
                    <*> ( app2 (add n)(times n ax by)(times n ay bx ))
    , positive = \ (Difference x y) -> gt n x y
    , nonnegative = \ (Difference x y) -> ge n x y
    , gt =  \ (Difference ax ay) (Difference bx by) ->
         app2 (gt n) (add n ax by) ( add n ay bx)
    , ge = \ (Difference ax ay) (Difference bx by) ->
         app2 (ge n) ( add n ax by ) ( add n ay bx)
    , neq = \ (Difference ax ay) (Difference bx by) ->
         app2 (neq n) (add n ax by) ( add n ay bx)
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    , atmost = \ k bs -> C.atmost k bs
    }

app1 f a = do x <- a ; f a
app2 f a b = do x <- a ; y <- b ; f x y
