{-# language FlexibleInstances #-}
{-# language StandaloneDeriving #-}

module MB.Proof.CPF where

import TPDB.Data
import TPDB.DP 
import MB.Proof.Type

import qualified TPDB.CPF.Proof.Type as C
import qualified TPDB.CPF.Proof.Xml 

import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.SMT.Exotic.Semiring.Arctic  as A

import qualified Data.Map as M
import Text.XML.HaXml.XmlContent

import Data.Array
import Data.Typeable

tox = TPDB.CPF.Proof.Xml.tox

rtoc :: Proof Identifier Identifier 
     -> C.CertificationProblem
rtoc p = C.CertificationProblem
    { C.input = C.TrsInput { C.trsinput_trs = input p }
    , C.cpfVersion = "2.1"
    , C.proof = C.TrsTerminationProof $ proof $ reason p 
    , C.origin = C.ProofOrigin $ C.Tool { C.name = "matchbox", C.version = "03-February-2013" }
    }

proof :: Reason Identifier Identifier
      -> C.TrsTerminationProof
proof r = case r of
    No_Strict_Rules -> C.RIsEmpty
    DP_Transform p -> 
            C.DpTrans { C.dptrans_dps = C.DPS $ map rsharp $ rules $ input  p
                        , C.markedSymbols = True
                        , C.dptrans_dpProof = dpproof p
                        }
    Mirror_Transform p -> C.StringReversal { C.trs = input  p
                                    , C.trsTerminationProof = proof $ reason p
                                    }

dpproof :: Proof Identifier (Marked Identifier) 
        -> C.DpProof
dpproof p = case reason p of
    No_Strict_Rules -> C.PIsEmpty
    Matrix_Interpretation_Natural min q -> 
        C.RedPairProc { C.dp_orderingConstraintProof = ocp C.Naturals $ msharp min
                      , C.red_pair_dps = C.DPS $ map rsharp $ rules $ input q
                      , C.redpairproc_dpProof = dpproof q
                      }
    Matrix_Interpretation_Arctic mia q -> 
        C.RedPairProc { C.dp_orderingConstraintProof = ocp (C.Arctic C.Naturals) $ msharp mia
                      , C.red_pair_dps = C.DPS $ map rsharp $ rules $ input q
                      , C.redpairproc_dpProof = dpproof q
                      }

deriving instance Eq  a => Eq  (C.Sharp a)
deriving instance Ord a => Ord (C.Sharp a)


sharp k =  case k of
            Original o -> C.Plain o
            Marked   o -> C.Sharp o

msharp m = M.fromList $ do
    ( k, v ) <- M.toList m
    return (sharp k, v)

rsharp u = u { lhs = fmap sharp $ lhs u
             , rhs = fmap sharp $ rhs u
             }

ocp dom mi = 
        C.RedPair { C.interpretation = interpretation dom mi }

interpretation :: (XmlContent s, C.ToExotic e)
               => C.Domain 
    -> M.Map s (L.Linear (M.Matrix e))
    -> C.Interpretation 
interpretation dom mi = C.Interpretation
    { C.interpretation_type = C.Matrix_Interpretation
            { C.domain =  dom
            , C.dimension = 42  -- FIXME
            , C.strictDimension = 1 -- FIXME
            }
    , C.interprets = 
          map interpret $ M.toList mi
    }

{-
domain :: Domain -> C.Domain
domain d = case d of
    Natural -> C.Naturals
    Arctic -> C.Arctic C.Naturals
    Tropical -> C.Tropical C.Naturals
-}



interpret  ( s, v ) = C.Interpret
   { C.symbol = s
   , C.arity = 1 -- what?
   , C.value = fun  v 
   }
                             
fun  f = C.Polynomial $ C.Sum 
       $ map C.Polynomial_Coefficient 
       $ vector  ( column 0 $ L.abs f ) 
       : map ( matrix  ) ( L.lin f )

matrix  m = C.Matrix $ map ( vector  ) 
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