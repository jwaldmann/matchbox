module SMT.Plain.Integer where

import SMT.Dictionary

import Prelude hiding ( not, and, or )
import qualified Prelude

import Control.Monad.Error

direct :: Dictionary (Either String) Integer Integer Bool
direct = Dictionary 
    { info = unwords [ "Plain.Integer" ]
    , domain = SMT.Dictionary.Int
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

