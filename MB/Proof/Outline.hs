{-# language OverloadedStrings #-}

module MB.Proof.Outline where

import MB.Proof.Type
import MB.Proof.Doc ()

import TPDB.Data (strict, rules )
import TPDB.Pretty 
import Text.PrettyPrint.Leijen.Text ( align, indent)

outline :: Proof v s -> Doc
outline p = vcat
    [ pretty (claim p) <+> "for" <+> outsys (input p)
    , outreason $ reason p
    ]

outsys sys = 
    let p = length $ filter strict $ rules sys
        r = length $ filter (not . strict) $ rules sys
    in  "TRS/DP with" <+> pretty p <+> "strict (pairs)" <+> pretty r <+> "relative (rules)"

outreason r = case r of
    No_Strict_Rules -> "no strict pairs"
    Mirror_Transform p -> vcat [ "mirror SRS", outline p ]
    DP_Transform p -> vcat [ "DP transform", indent 4 $ outline p ]
    Matrix_Interpretation_Arctic  i u p -> 
        vcat ["matrix interpretation, domain" <+> text  ( show $ domain i)
                      <+> "dimension" <+> pretty (dimension i)
             , case u of 
                     Nothing -> empty 
                     Just us -> "for" <+> pretty (length us) <+> "usable rules" 
             , indent 4 $ outline p
             ]
    SCCs cs ->  vcat ["EDG decomposed in SCCs" 
                     , indent 4 $ vcat $ do Right c <- cs ; return $ outline c
                     ]
    Cpf2Cpf info f p -> vcat [ "Cpf2Cpf", indent 4 $ info , indent 4 $ outline p ]


