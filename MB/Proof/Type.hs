module MB.Proof.Type where

import TPDB.Data hiding ( Termination )
import TPDB.DP (Marked )

import SMT.Dictionary (Domain)
import qualified SMT.Linear as L
import qualified SMT.Matrix as M

import qualified SMT.Semiring.Arctic  as A

import qualified Data.Map as M
import TPDB.Pretty ( Doc )

import qualified TPDB.CPF.Proof.Type as T

-- * the data type

data Claim = Termination | Top_Termination

data Proof v s = Proof
     { input :: TRS v s
     , claim :: Claim
     , reason :: Reason v s
     }

data Interpretation s e = Interpretation 
        { dimension :: Int
        , domain :: Domain
        , mapping :: M.Map s (L.Linear (M.Matrix e))
        , constraint :: Maybe (Constraint s e)
        }

data Constraint s e =
  Constraint { restriction :: L.Linear (M.Matrix e) -- ^ unary
             , nonemptiness_certificate :: M.Matrix e -- ^ vector
             , mapping_certificate :: M.Map s [M.Matrix e]
             , compatibility_certificate :: [ M.Matrix e ]
             }
        

data Reason v s = No_Strict_Rules
     | Equivalent Doc (Proof v s)
     | DP_Transform (Proof v (Marked s ))
     | Mirror_Transform (Proof v s)
     | Matrix_Interpretation_Natural
         (Interpretation s Integer)
         (Maybe [ Rule (Term v s) ]) -- maybe mention usable rules
         (Proof v s)
     | Matrix_Interpretation_Arctic  
         (Interpretation s (A.Arctic Integer))
        (Maybe [ Rule (Term v s) ]) -- maybe mention usable rules
           (Proof v s)
     | Usable_Rules (Proof v s)
     | SCCs [ Either (Rule (Term v s)) (Proof v s) ]
     | Extra Doc (Proof v s)

     | Cpf2Cpf Doc (T.DpProof -> T.DpProof) (Proof v s)


