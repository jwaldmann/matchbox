module Satchmo.SMT.Integer where

import Prelude hiding ( not, and, or )
import qualified Prelude
import Control.Monad.Error ( throwError )

import Language.SMTLIB

import Satchmo.SMT.Config

import Satchmo.SMT.Dictionary
import Satchmo.SMT.Exotic.Semiring.Integer
import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code
import qualified Satchmo.Boolean as B

import qualified Satchmo.Unary.Op.Fixed
import qualified Satchmo.Unary.Op.Flexible
import qualified Satchmo.Unary as Un

import qualified Satchmo.Binary as Bin
import qualified Satchmo.Binary.Op.Fixed  
import qualified Satchmo.Binary.Op.Flexible

import qualified Satchmo.SMT.Opt.Integer as OI
import qualified Satchmo.SMT.Opt.Base as OB

import Satchmo.SMT.ToTerm

import Control.Monad ( forM )

direct :: Dictionary (Either String) Integer Integer Bool
direct = Dictionary 
    { info = unwords [ "binary (direct)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , nconstant = \ n -> return n
    , bconstant = \ b -> return b
    , add   = \ x y -> return $ x + y
    , times = \ x y -> return $ x * y
    , positive = \ x -> return $ x > 0 
    , gt = \ x y -> return $ x > y
    , ge = \ x y -> return $ x >= y 
    , and = \ xs -> return $ Prelude.and xs
    , or  = \ xs -> return $ Prelude.or xs
    , not = return . Prelude.not 
    , assert = \ bs -> 
          if Prelude.or bs then return () 
          else throwError "Satchmo.SMT.Integer.assert"
    }

unary_fixed :: Int -> Unary_Addition 
            -> Dictionary Satchmo.SAT.Mini.SAT Un.Number Integer B.Boolean
unary_fixed bits a = Dictionary
    { info = unwords [ "unary", "bits:", show bits, "(fixed)", "addition:", show a ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Un.number bits
    , nconstant = Un.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = case a of
          Quadratic -> Satchmo.Unary.Op.Fixed.add_quadratic
          Bitonic_Sort -> Satchmo.Unary.Op.Fixed.add_by_bitonic_sort
          Odd_Even_Merge -> Satchmo.Unary.Op.Fixed.add_by_odd_even_merge
    , gt = Un.gt
    , ge = Un.ge
    , neq = Un.eq
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    }

unary_flexible :: Int -> Unary_Addition
               -> Dictionary Satchmo.SAT.Mini.SAT Un.Number Integer  B.Boolean
unary_flexible bits a = Dictionary
    { info = unwords [ "unary", "bits:", show bits, "(flexible)", "addition:", show a ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Un.number bits
    , nconstant = Un.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = case a of
          Quadratic -> Satchmo.Unary.Op.Flexible.add_quadratic
          Bitonic_Sort -> Satchmo.Unary.Op.Flexible.add_by_bitonic_sort
          Odd_Even_Merge -> Satchmo.Unary.Op.Flexible.add_by_odd_even_merge
    , gt = Un.gt
    , ge = Un.ge
    , neq = Un.eq
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    }

binary_fixed bits =
    if bits <= 3
    then binary_fixed_opt   bits
    else binary_fixed_plain bits
    -- binary_fixed_double $ binary_fixed (div bits 2)

binary_fixed_opt bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(fixed)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Bin.number bits
    , nbits = bits
    , decode = Satchmo.Code.decode
    , nconstant = \ n -> do
          let digitsRest n 0 = ( [], n )
              digitsRest n b = 
                  let (d,m) = divMod n 2
                      (ds,r) = digitsRest d (b-1)
                  in  (toEnum m : ds, r)
          let (ds, 0) = 
                  digitsRest (fromIntegral n) bits
          fmap Bin.make $ forM ds B.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = 
       -- OI.op2 ( OB.improve $ OB.fun2 (+) bits ) bits
       Satchmo.Binary.Op.Fixed.add
    , times = 
       OI.op2 ( OB.improve $ OB.fun2 (*) bits ) bits
       -- Satchmo.Binary.Op.Fixed.times
    , positive = \ n -> B.or $ Bin.bits n
    , gt = 
       OI.prop2 ( OB.improve $ OB.rel2 (>) bits) 
       -- Bin.gt
    , ge = 
       OI.prop2 ( OB.improve $ OB.rel2 (>=) bits) 
       -- Bin.ge
    -- , neq = OI.prop2 ( OB.improve $ OB.rel2 (/=) bits) 
    
    , and = B.and, or = B.or, not = return . B.not
    , beq = B.equals2, assert = B.assert
    }

binary_fixed_plain :: Int 
  -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number Integer B.Boolean
binary_fixed_plain bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(fixed)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , nbits = bits
    , number = Bin.number bits
    , decode = Satchmo.Code.decode
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = Satchmo.Binary.Op.Fixed.add
    , times = Satchmo.Binary.Op.Fixed.times
    , positive = \ n -> B.or $ Bin.bits n
    , gt = Bin.gt
    , ge = Bin.ge
    , neq = Bin.eq
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    }

binary_flexible :: Int -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number Integer B.Boolean
binary_flexible bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(flexbible)" ]
    , domain = Satchmo.SMT.Dictionary.Int
    , number = Bin.number bits
    , decode = Satchmo.Code.decode
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = Satchmo.Binary.Op.Flexible.add
    , times = Satchmo.Binary.Op.Flexible.times
    , positive = \ n -> B.or $ Bin.bits n
    , gt = Bin.gt
    , ge = Bin.ge
    , neq = Bin.eq
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    }

instance ToTerm Integer where
  toTerm int =
    if int >= 0  
    then Term_spec_constant ( Spec_constant_numeral int )
    else Term_qual_identifier_ ( Qual_identifier ( Identifier "-"))
             [ toTerm $ negate int ]
