{-# language OverloadedStrings #-}

module MB.Proof.Outline where

import MB.Proof.Type
import MB.Proof.Doc ()

import qualified MB.Closure.Enumerate as Cl

import TPDB.Data (strict, rules )
import TPDB.Pretty 
import Text.PrettyPrint.Leijen.Text ( align, indent)

import Data.Time ( getCurrentTime, diffUTCTime )

headline :: Proof v s -> Doc
headline p = case claim p of
  Termination -> "YES"
  Cycle_Termination -> "YES"
  Non_Termination -> "NO"
  Cycle_Non_Termination -> "NO"
  c -> pretty c

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
             , timing i
             , indent 4 $ outline p
             ]
    Matrix_Interpretation_Natural  i u p -> 
        vcat ["matrix interpretation, domain" <+> text  ( show $ domain i)
                      <+> "dimension" <+> pretty (dimension i)
                      <+> case constraint i of
                               Nothing -> empty
                               Just con -> "with" <+> pretty (width con) <+> "constraints"
             , case u of 
                     Nothing -> empty 
                     Just us -> "for" <+> pretty (length us) <+> "usable rules"
             , timing i
             , indent 4 $ outline p
             ]
    SCCs cs ->  vcat ["EDG decomposed in SCCs" 
                     , indent 4 $ vcat $ do Right c <- cs ; return $ outline c
                     ]
    Nonterminating c -> vcat
      [ "nonterminating" , Cl.brief c ]
                
    Cpf2Cpf info f p -> vcat [ "Cpf2Cpf", indent 4 $ info , indent 4 $ outline p ]


timing i = case time i of
  Nothing -> empty
  Just t -> text "found in"
            <+> (text $ show $ diffUTCTime (end t) (start t) )
            <+> text "from" <+> (text $ show $ start t)
            <+> text "to"   <+> (text $ show $ end   t)
