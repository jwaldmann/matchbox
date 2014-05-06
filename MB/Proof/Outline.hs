{-# language OverloadedStrings #-}

module MB.Proof.Outline where

import MB.Proof.Type

import TPDB.Pretty 


outline :: Proof v s -> Doc
outline p = outreason $ reason p

outreason r = case r of
    No_Strict_Rules -> "no strict pairs"
    DP_Transform p -> vcat [ "DP transform", nest 4 $ outline p ]
    Matrix_Interpretation_Arctic  i u p -> 
        vcat ["matrix interpretation, domain" <+> text  ( show $ domain i)
                      <+> "dimension" <+> pretty (dimension i)
             , case u of Nothing -> empty ; Just _ -> "for usable rules"
             , nest 4 $ outline p
             ]
    SCCs cs ->  vcat ["EDG decomposed in SCCs" 
                     , nest 4 $ vcat $ do Right c <- cs ; return $ outline c
                     ]
    Cpf2Cpf f p -> vcat [ "Cpf2Cpf", nest 4 $ outline p ]

