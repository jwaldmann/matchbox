{-# language OverloadedStrings #-}

module MB.Proof.Doc where

import MB.Proof.Type

import TPDB.Plain.Write ()

import TPDB.Pretty
import MB.Pretty (pretty_short) -- and instances

instance (Pretty v, Pretty s) => Pretty (Proof v s) where
    pretty p = vcat 
        [ "system" <+> pretty_short ( input p )
        , "is" <+> pretty (claim p) <+> "because"
        , pretty (reason p)
        ]

instance Pretty Claim where
    pretty c = case c of
        Termination -> "terminating"
        Top_Termination -> "top-terminating"

instance (Pretty s, Pretty e ) =>
    Pretty (Interpretation s e) where
       pretty i = vcat
          [ hsep [ "matrix interpretation"
                 , "domain", text ( show $ domain i)
                 , "dimension", text (show $dimension i)
                 ]
          , pretty $ mapping i
          ]

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
        Extra doc p -> vcat
            [ "extra proof method"
            , nest 4 doc
            , pretty p
            ]