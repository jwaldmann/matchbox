{-# language OverloadedStrings #-}

module MB.Proof.Doc where

import MB.Proof.Type
import qualified SMT.Matrix as M
import qualified SMT.Linear as L

import TPDB.Plain.Write ()

import qualified Data.Map as M

import TPDB.Pretty
import MB.Pretty (pretty_short, oneline, beside, (</>)) -- and instances

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
        Cycle_Termination -> "cycle-terminating"

instance (Pretty v, Pretty s, Pretty e ) =>
    Pretty (Interpretation v s e) where
       pretty i = hsep [ "matrix interpretation" 
                 , "domain", text ( show $ domain i)
                 , "dimension", text (show $dimension i)
                 ] </> vcat [
            pretty $ mapping i
          , case constraint i of
            Nothing -> empty
            Just c -> pretty c
          , case values_for_rules i of
            Nothing -> empty
            Just vs -> "interpretations for rules:"
               </> vcat ( map ( \ (u,(l,r)) ->
                   pretty u </> vcat [pretty l, pretty r]  ) vs )
          ]

instance (Pretty v, Pretty s, Pretty e)
         => Pretty (Constraint v s e) where
    pretty c = "Polyhedral constraints with certificates:" </> vcat
      [ "number of constraints:" <+> pretty (width c)
      , "domain restriction" </> pretty (restriction c) <+> ">= 0"
      , "nonemptiness certificate"
        </> pretty (M.transpose $ nonemptiness_certificate c ) 
      , "mapping certificate (nonzero components only):" </>
            vcat (map pretty $ M.toList $ nonzero_mapping_certificate c)
      , "rules with nonzero compatibility certificate:" </>
            vcat (map ( \ (u,cert,(lhs,rhs)) -> pretty u </> vcat
                       [ "certificate" </> pretty cert
                       , "lhs value" </> pretty lhs
                       , "rhs value" </> pretty rhs
                       ]
                   ) $ rules_with_nonzero_compatibility_certificate c )
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
        Matrix_Interpretation_Natural i u p -> vcat
            [ "rule removal by matrix interpretation into natural numbers"
            , nest 4 $ pretty i
            , nest 4 $ case u of
                   Nothing -> empty
                   Just rs -> "usable rules" <+> vcat (map pretty rs)
            , pretty p
            ]
        Matrix_Interpretation_Arctic i u p -> vcat
            [ "rule removal by matrix interpretation into arctic numbers"
            , nest 4 $ pretty i
            , nest 4 $ case u of
                   Nothing -> empty
                   Just rs -> "usable rules" <+> vcat (map pretty rs)
            , pretty p
            ]
        Usable_Rules p -> vcat
            [ "restriction to usable rules"
            , pretty p
            ]
        SCCs ps -> vcat
            [ "EDG has" <+> (pretty $ length ps) <+> "SCCs"
            , vcat $ do
                  (k,p) <- zip [1 :: Int .. ] ps
                  return $ "SCC" <+> pretty k <+> pretty p
            ]

        Cpf2Cpf info f p -> vcat 
            [ "semanticLabeling" 
            , nest 4 info
            , pretty p 
            ]

        Extra doc p -> vcat
            [ "extra proof method"
            , nest 4 doc
            , pretty p
            ]

