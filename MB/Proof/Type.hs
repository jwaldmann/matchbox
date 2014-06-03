module MB.Proof.Type where

import TPDB.Data hiding ( Termination )
import TPDB.DP (Marked )

import Satchmo.SMT.Dictionary (Domain)
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M

import qualified Satchmo.SMT.Exotic.Semiring.Arctic  as A

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
        }

data Reason v s = No_Strict_Rules
     | Equivalent Doc (Proof v s)
     | DP_Transform (Proof v (Marked s ))
     | Mirror_Transform (Proof v s)
     | Matrix_Interpretation_Natural
         (Interpretation s Integer) (Proof v s)
     | Matrix_Interpretation_Arctic  
         (Interpretation s (A.Arctic Integer))
        (Maybe [ Rule (Term v s) ]) -- maybe mention usable rules
           (Proof v s)
     | Usable_Rules (Proof v s)
     | SCCs [ Either (Rule (Term v s)) (Proof v s) ]
     | Extra Doc (Proof v s)

     | Cpf2Cpf Doc (T.DpProof -> T.DpProof) (Proof v s)


