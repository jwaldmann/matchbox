module MB.Proof.Type where

import TPDB.Data hiding ( Termination )
import TPDB.DP (Marked )



import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.SMT.Exotic.Semiring.Arctic  as A

import qualified Data.Map as M
import Text.PrettyPrint.HughesPJ

-- * the data type

data Claim = Termination | Top_Termination

data Proof v s = Proof
     { input :: TRS v s
     , claim :: Claim
     , reason :: Reason v s
     }

data Reason v s = No_Strict_Rules
     | Equivalent Doc (Proof v s)
     | DP_Transform (Proof v (Marked s ))
     | Mirror_Transform (Proof v s)
     | Matrix_Interpretation_Natural 
           (M.Map s (L.Linear (M.Matrix Integer)))
           (Proof v s)
     | Matrix_Interpretation_Arctic  
           (M.Map s (L.Linear (M.Matrix (A.Arctic Integer))) )
           (Proof v s)


