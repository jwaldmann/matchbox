{-# language OverloadedStrings #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# language NoMonomorphismRestriction #-}

module MB.Proof.LaTeX where

import MB.Proof.Type
import qualified SMT.Matrix as M
import qualified SMT.Linear as L
import SMT.Semiring.Arctic
import SMT.Dictionary (Domain)

import Text.LaTeX (Texy, texy, par, (<>), empty, verbatim, raw)
import Data.Monoid (mconcat, mempty)

import Text.LaTeX.Base.Class (liftL, liftL2, liftListL, LaTeXC)
import Text.LaTeX.Packages.AMSMath
import qualified Data.Matrix as DM
import Text.LaTeX.Base.Pretty

import qualified Text.PrettyPrint.Leijen.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Map as M
import Data.List (intersperse)
import Data.String ( fromString )

import qualified TPDB.Data as TD
import qualified TPDB.DP.Transform as TD

-- * approximations for Doc functions:

liftL1 = liftL
liftLN = liftListL

matexy = math . texy

vcat docs = liftLN mconcat $ map ( \ d -> par <+> d ) docs
hsep docs = foldr (<+>) mempty docs
nest :: LaTeXC l => Int -> l -> l
nest _ doc = doc

p <+> q = liftL2 (<>) p (liftL2 (<>) (raw " ") q)

(</>) = liftL2 (<>)

fromDoc d = verbatim $ TL.toStrict $ T.displayT $ T.renderPretty 0.4 80 d

instance (Texy v, Texy s) => Texy (Proof v s) where
    texy p = vcat 
        [ "system" <+> matexy ( MB.Proof.Type.input p )
        , "is" <+> texy (claim p) <+> "because"
        , texy (reason p)
        ]

instance Texy Claim where
    texy c = case c of
        Termination -> "terminating"
        Top_Termination -> "top-terminating"

instance (Texy v, Texy s, Texy e ) =>
    Texy (Interpretation v s e) where
       texy i = hsep [ "matrix interpretation" 
                 , "domain", texy (  domain i)
                 , "dimension", texy ( dimension i)
                 ] </> vcat
          [ mathDisplay $ texy $ mapping i
          , case constraint i of
            Nothing -> mempty
            Just c -> texy c
          , case values_for_rules i of
            Nothing -> mempty
            Just vs -> "interpretations for rules:"
               </> align_ ( map ( \ (u,(l,r)) ->
                   texy u </> vcat [texy l, texy r]  ) vs )
          ]

instance (Texy v, Texy s, Texy e)
         => Texy (Constraint v s e) where
    texy c = "Polyhedral constraints with certificates:" </> vcat
      [ "number of constraints:" <+> texy (width c)
      , "domain restriction" </>
         mathDisplay ( texy (restriction c) >=: texy (0::Integer) )
      , "domain nonemptiness certificate"
        </> matexy (M.transpose $ nonemptiness_certificate c ) 
      , "domain mapping certificate:" </>
            align_ (map (\(k,us) ->  texy k <+> raw "\\mapsto"
                        <+> commasep (map texy us)  )
                    $ M.toList $ mapping_certificate c)
      , "rules with compatibility certificate:" </>
            vcat (map ( \ (u,cert,(lhs,rhs)) -> matexy u </> vcat
                       [ "certificate" </> ( math $ commasep $ map texy cert)
                       , "lhs value" </> matexy lhs
                       , "rhs value" </> matexy rhs
                       ]
                   ) $ rules_with_nonzero_compatibility_certificate c )
      ]


instance (Texy v, Texy s) => Texy (Reason v s) where
    texy r = case r of
        No_Strict_Rules -> "it contains no strict rules"
        Equivalent i p -> vcat
            [ "equivalent transformation"
            , nest 4 $ fromDoc i
            , texy p
            ]
        DP_Transform p -> vcat
            [ "dependency pairs transformation"
            , texy p
            ]
        Mirror_Transform p -> vcat
            [ "mirror transformation"
            , texy p
            ]
        Matrix_Interpretation_Natural i u p -> vcat
            [ "rule removal by matrix interpretation into natural numbers"
            , nest 4 $ texy i
            , nest 4 $ case u of
                   Nothing -> mempty
                   Just rs -> "usable rules" <+> vcat (map texy rs)
            , texy p
            ]
        Matrix_Interpretation_Arctic i u p -> vcat
            [ "rule removal by matrix interpretation into arctic numbers"
            , nest 4 $ texy i
            , nest 4 $ case u of
                   Nothing -> mempty
                   Just rs -> "usable rules" <+> vcat (map texy rs)
            , texy p
            ]
        Usable_Rules p -> vcat
            [ "restriction to usable rules"
            , texy p
            ]
        SCCs ps -> vcat
            [ "EDG has" <+> (texy $ length ps) <+> "SCCs"
            , vcat $ do
                  (k,p) <- zip [1 :: Int .. ] ps
                  return $ "SCC" <+> texy k <+> texy p
            ]

        Cpf2Cpf info f p -> vcat 
            [ "semanticLabeling" 
            , nest 4 $ fromDoc info
            , texy p 
            ]

        Extra doc p -> vcat
            [ "extra proof method"
            , nest 4 $ fromDoc doc
            , texy p
            ]

-- * this should not be here:

instance Texy a  => Texy (M.Matrix a) where
  texy m = let (r,c) = M.dim m in case m of
    M.Matrix {} -> pmatrix Nothing $ DM.fromList r c $ concat $ M.contents m
    M.Zero {} -> pmatrix Nothing (DM.zero r c :: DM.Matrix Integer)
    M.Unit {} -> pmatrix Nothing (DM.identity r   :: DM.Matrix Integer)

instance Texy a  => Texy (L.Linear a) where
  texy l = texy (L.abs l)
    <> mconcat ( map ( \ (k,m) -> raw "+" <+> texy m <> raw " \\cdot " <> raw " x_" <> texy k )
                 (zip [1 :: Int ..] $ L.lin l) )

instance Texy n => Texy (Arctic n) where
  texy a = case a of
    Minus_Infinite -> raw " -\\infty "
    Finite f -> texy f

instance Texy Domain where
  texy d = raw $ fromString $ show d

instance (Texy k, Texy v) => Texy (M.Map k v) where
  texy m = commasep $ map (\(k,v) -> texy k <> raw " \\mapsto " <> texy v) $ M.toList m

instance (Texy a, Texy b) => Texy (Either a b) where
  texy e = case e of
    Left a -> "Left" <> texy a
    Right b -> "Right" <> texy b

-- * this should so not be here:

instance Texy TD.Identifier where
  texy = fromString . show

instance (Texy v, Texy s) => Texy (TD.Term v s) where
  texy t = case t of
    TD.Var v -> texy v
    TD.Node f args -> texy f <> "(" <> commasep (map texy args) <> ")"

instance (Texy t) => Texy (TD.Rule t) where
  texy u = texy (TD.lhs u) <> raw " \\to " <> texy (TD.rhs u)

instance (Texy v, Texy s) => Texy (TD.TRS v s) where
  texy sys = raw "\\{" <> ( commasep $ map texy $ TD.rules sys ) <> raw "\\}"

instance Texy s => Texy (TD.Marked s) where
  texy s = case s of
    TD.Marked s -> texy s <> raw "^\\#"
    TD.Original o -> texy o

commasep xs =     mconcat $ intersperse "," $ xs

