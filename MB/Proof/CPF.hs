{-# language FlexibleInstances #-}
{-# language StandaloneDeriving #-}

module MB.Proof.CPF where

import TPDB.Data
import TPDB.DP 
import MB.Proof.Type

import MB.Proof.Doc () -- for print error messages
import TPDB.Pretty ( render, pretty ) -- "

import qualified TPDB.CPF.Proof.Type as C
import qualified TPDB.CPF.Proof.Xml 

import Satchmo.SMT.Dictionary (Domain (..))
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.SMT.Exotic.Semiring.Arctic  as A

import qualified Data.Map as M
import Text.XML.HaXml.XmlContent

import Data.Array
import Data.Typeable
import qualified Data.List

tox = TPDB.CPF.Proof.Xml.tox

rtoc :: Proof Identifier Identifier 
     -> C.CertificationProblem
rtoc p = C.CertificationProblem
    { C.input = C.TrsInput { C.trsinput_trs = input p }
    , C.cpfVersion = "2.1"
    , C.proof = C.TrsTerminationProof $ proof $ reason p 
    , C.origin = C.ProofOrigin 
               $ C.Tool { C.name = "matchbox", C.version = "03-February-2013" }
    }

proof :: Reason Identifier Identifier
      -> C.TrsTerminationProof
proof r = case r of
    No_Strict_Rules -> C.RIsEmpty
    Equivalent d p -> proof $ reason p
    DP_Transform p -> 
            C.DpTrans { C.dptrans_dps = C.DPS $ map rsharp $ filter strict $ rules $ input  p
                        , C.markedSymbols = True
                        , C.dptrans_dpProof = dpproof p
                        }
    Mirror_Transform p -> C.StringReversal { C.trs = input  p
                                    , C.trsTerminationProof = proof $ reason p
                                    }
    Matrix_Interpretation_Natural min q -> 
        C.RuleRemoval { C.rr_orderingConstraintProof = 
                              ocp plain  C.Naturals min
                      , C.trs = input q
                      , C.trsTerminationProof = proof $ reason q
                      }

dpproof :: Proof Identifier (Marked Identifier) 
        -> C.DpProof
dpproof p = case reason p of
    No_Strict_Rules -> C.PIsEmpty
    Equivalent d p -> dpproof  p
    Matrix_Interpretation_Natural mia q -> 
        C.RedPairProc { C.rppOrderingConstraintProof 
                      = ocp sharp C.Naturals mia
                      , C.rppDps = C.DPS $ map rsharp $ filter strict $ rules $ input q
                      , C.rppDpProof = dpproof q
                      }
    Matrix_Interpretation_Arctic mia usable q -> 
        C.RedPairProc { C.rppOrderingConstraintProof 
                      = ocp sharp (C.Arctic C.Naturals) mia
                      , C.rppDps = C.DPS $ map rsharp $ filter strict $ rules $ input q
                      , C.rppUsableRules = 
                           fmap (C.DPS . map rsharp ) usable
                      , C.rppDpProof = dpproof q
                      }
    SCCs ps -> C.DepGraphProc $ do
        p <- ps
        return $ case p of
            Left v -> C.DepGraphComponent
               { C.dgcRealScc = False
               , C.dgcDps = C.DPS $ map rsharp [ v ]
               }
            Right p -> C.DepGraphComponent 
               { C.dgcRealScc = True 
               , C.dgcDps = C.DPS $ map rsharp $ filter strict $ rules $ input p
               , C.dgcDpProof = dpproof p
               }
    Usable_Rules p -> dpproof p

    Cpf2Cpf _ f p -> f $ dpproof p

    r -> error $ unlines [ "dpproof: missing CPF output for"
                         , render $ pretty r 
                         ]

plain :: Identifier -> C.Symbol
plain k = C.SymName k 

sharp :: Marked Identifier -> C.Symbol
sharp k =  case k of
            Original o ->              plain o
            Marked   o -> C.SymSharp $ plain o

deriving instance Eq C.Symbol
deriving instance Ord C.Symbol
deriving instance Eq C.Label
deriving instance Ord C.Label

{-
msharp m = m { mapping = M.fromList $ do
    ( k, v ) <- M.toList $ mapping m
    return (sharp k, v) }
-}

rsharp :: Rule (Term Identifier (Marked Identifier)) 
       -> Rule (Term Identifier C.Symbol)
rsharp u = u { lhs = fmap sharp $ lhs u
             , rhs = fmap sharp $ rhs u
             }

ocp fsym dom mi = C.OCPRedPair 
           $ C.RPInterpretation 
           $ interpretation fsym dom mi 

interpretation :: ( C.ToExotic e)
               => (s -> C.Symbol) 
    -> C.Domain 
    -> Interpretation s e
    -> C.Interpretation 
interpretation fsym dom mi = C.Interpretation
    { C.interpretation_type = C.Matrix_Interpretation
            { C.domain = case domain mi of
                  Int -> C.Naturals
                  Arctic -> C.Arctic C.Naturals
                  Tropical -> C.Tropical C.Naturals
            , C.dimension = dimension mi
            , C.strictDimension = 1 -- FIXME
            }
    , C.interprets = map (interpret $ dimension mi)
            $ M.toList $ M.mapKeys fsym $ mapping mi
    }


interpret dim ( s, v ) = C.Interpret
   { C.symbol = s
   , C.arity = length $ L.lin v
   , C.value = fun dim $ blow_up dim v 
   }

-- | this needs to be applied to interpretations of top symbols.
-- in a many-sorted algebra, their result sort is A^1,
-- but apparently CPF is one-sorted so we need A^dim.
blow_up dim f = if L.to f == dim then f else
    let blow m = case M.contents m of
            [ row ] -> M.Matrix { M.dim = (dim, M.from m)
                                , M.contents = replicate dim $ row
                                }
    in L.Linear { L.abs = blow $ L.abs f
                , L.lin = map blow $ L.lin f
                }
                             
fun dim f = C.Polynomial $ C.Sum 
       $ C.Polynomial_Coefficient 
              ( absolute dim $ L.abs f ) 
       : do (k,m) <- zip [ 1 .. ] $ L.lin f 
            return $ C.Product 
                   [ C.Polynomial_Coefficient $ matrix m
                   , C.Polynomial_Variable $ show k
                   ]

absolute dim m = vector
         $ map ( \ [e] -> e )
         $ M.contents m

matrix  m = C.Matrix $ map ( vector  ) 
        -- CETA uses column major representation??
        $ Data.List.transpose 
        $ M.contents m

column 0 m = map head $ M.contents m

vector  (  xs ) = C.Vector 
        $ map ( C.Coefficient_Coefficient . C.toExotic ) xs


instance C.ToExotic Integer where
    toExotic i = C.E_Integer i

instance C.ToExotic (A.Arctic Integer) where
    toExotic a = case a of
        A.Minus_Infinite -> C.Minus_Infinite
        A.Finite f -> C.E_Integer f
