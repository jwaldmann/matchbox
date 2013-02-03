{-# language OverloadedStrings #-}

module MB.Proof where

import TPDB.Data hiding ( Termination )
import TPDB.DP (Marked )

import TPDB.Plain.Write ()

import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.SMT.Exotic.Semiring.Arctic  as A

import qualified Data.Map as M

import Text.PrettyPrint.HughesPJ
import TPDB.Pretty
import MB.Pretty () -- instances

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

-- * TODO: render as CPF 

-- * render as Doc

instance (Pretty v, Pretty s) => Pretty (Proof v s) where
    pretty p = vcat 
        [ "system" <+> pretty ( input p )
        , "is" <+> pretty (claim p) <+> "because"
        , pretty (reason p)
        ]

instance Pretty Claim where
    pretty c = case c of
        Termination -> "terminating"
        Top_Termination -> "top-terminating"

instance (Pretty v, Pretty s) => Pretty (Reason v s) where
    pretty r = case r of
        No_Strict_Rules -> "it contains no strict rules"
        Equivalent i p -> vcat
            [ "equivalent transformation"
            , nest 4 i
            , pretty p
            ]
        DP_Transform p -> vcat
            [ "dependency pairs transformation"
            , pretty p
            ]
        Mirror_Transform p -> vcat
            [ "mirror transformation"
            , pretty p
            ]
        Matrix_Interpretation_Natural i p -> vcat
            [ "rule removal by matrix interpretation into natural numbers"
            , nest 4 $ pretty i
            , pretty p
            ]
        Matrix_Interpretation_Arctic i p -> vcat
            [ "rule removal by matrix interpretation into arctic numbers"
            , nest 4 $ pretty i
            , pretty p
            ]

