module SMT.Plain.Arctic where

import Prelude hiding ( not, and, or )
import qualified Prelude
import Control.Monad.Error ( throwError )

import SMT.Dictionary

import qualified SMT.Semiring as S
import qualified SMT.Semiring.Arctic as A

direct :: Dictionary (Either String) 
       (A.Arctic Integer) (A.Arctic Integer) Bool
direct = Dictionary 
    { info = unwords [ "arctic (direct)" ]
    , domain = SMT.Dictionary.Arctic
    , nconstant = \ n -> return n
    , bconstant = \ b -> return b
    , add   = \ x y -> return $ S.plus x y
    , times = \ x y -> return $ S.times x y
    , positive = \ x -> return $ S.strictly_positive x
    , gt = \ x y -> return $ S.gt x y
    , ge = \ x y -> return $ S.ge x y 
    , and = \ xs -> return $ Prelude.and xs
    , or  = \ xs -> return $ Prelude.or xs
    , not = return . Prelude.not 
    , assert = \ bs -> if Prelude.or bs then return () 
       else throwError "Satchmo.SMT.Arctic.assert"
    }

