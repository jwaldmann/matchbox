{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
module CO4.Test.TermComp2014.Proof.CPF 
where

import           Control.Exception (assert)
import qualified Data.Map as M
import qualified TPDB.CPF.Proof.Type as T
import qualified TPDB.CPF.Proof.Type 
import qualified TPDB.CPF.Proof.Util as T
import           TPDB.CPF.Proof.Xml ()
import qualified TPDB.Data as T
import qualified TPDB.DP as T
import           CO4.PreludeNat (width,value,nat)
import           CO4.Test.TermComp2014.Util
import           CO4.Test.TermComp2014.Standalone
import qualified Data.List ( transpose )
import           Data.List ( partition, nubBy )
import           Data.Function (on)

import Prelude hiding (lookup)

type Arities = M.Map Symbol Int

toCpfProof :: SymbolMap -> (UnlabeledTrs, [Domain]) -> Proof -> T.DpProof -> T.DpProof
toCpfProof symbolMap (trs, modelValues) (Proof model orders) innerProof = 
  semLabProof
  where
    arities           = nodeArities trs
    (labeledTrs,True) = makeLabeledTrs model trs modelValues
    labeledUR         = T.DPS $ labeledTrsToTPDBRules symbolMap (flip addCpfLabel') 
                              $ filterUsable 
                              $ steps (tagAll labeledTrs) orders
    
    ints              = intermediates trs labeledTrs orders

    semLabProof       = toCpfSemLabProof symbolMap labeledTrs model redPairProofs

    redPairProofs     = 
      foldr (\(i,o) -> toCpfRedPairProof symbolMap arities i o labeledUR) 
                        unlabProof
                      $ zip (tail ints) orders

    unlabProof        = toCpfUnlabProof symbolMap trs (last ints) innerProof

    filterUsable (TaggedGroupedTrs rs) = Trs 
      $ map snd 
      $ filter (\(isTagged, Rule isMarked _ _ ) -> not isMarked && isTagged) 
      $ concat rs

toCpfSemLabProof :: SymbolMap -> GroupedLabeledTrs Label -> Model Symbol -> T.DpProof -> T.DpProof
toCpfSemLabProof symbolMap trs model = 
  T.SemLabProc model' dps trs'
  where
    model' = toCpfModel symbolMap model
    trs'   = T.DPS $ filter (not . T.strict) all
    dps    = T.DPS $ filter T.strict all
    all    = labeledTrsToTPDBRules symbolMap (flip addCpfLabel') $ ungroupTrs trs

toCpfRedPairProof :: SymbolMap -> Arities -> TaggedGroupedLabeledTrs Label
                  -> UsableOrder SymLab -> T.DPS -> T.DpProof -> T.DpProof
toCpfRedPairProof symbolMap arities labeledTrs order usableRules innerProof = 
  T.RedPairProc { T.rppOrderingConstraintProof = ocp 
                , T.rppDps                     = dps 
                , T.rppUsableRules             = (Just usableRules)
                , T.rppDpProof                 = innerProof
                }
  where
    ocp = toCpfOrderingConstraintProof symbolMap arities order
    dps = T.DPS
        $ filter T.strict
        $ labeledTrsToTPDBRules symbolMap (flip addCpfLabel')
        $ ungroupTrs 
        $ removeMarkedUntagged' labeledTrs

toCpfUnlabProof :: SymbolMap -> UnlabeledTrs -> TaggedGroupedLabeledTrs Label -> T.DpProof 
                -> T.DpProof
toCpfUnlabProof symbolMap trs labeledTrs innerProof =
  T.UnlabProc { T.ulpDps = T.DPS 
                         $ filter T.strict
                         $ unlabeledTrsToTPDBRules symbolMap T.fromMarkedIdentifier
                         $ fst
                         $ removeMarkedUntagged trs labeledTrs
              , T.ulpTrs     = T.DPS $ unlabeledTrsToTPDBRules symbolMap T.fromMarkedIdentifier trs
              , T.ulpDpProof = innerProof
              }

toCpfModel :: SymbolMap -> Model Symbol -> T.Model
toCpfModel symbolMap model = T.FiniteModel (2^bitWidth) $ map toInterpret model
  where
    bitWidth = width $ snd $ head $ snd $ head model
    toInterpret (sym, intpr) = T.Interpret (toCpfSymbol symbolMap sym) arity
                             $ T.ArithFunction 
                             $ toArithFunction1 bitWidth 
                             $ expandArithFunction bitWidth arity
                             $ nubBy ((==) `on` fst) 
                             $ intpr
      where 
        arity = length $ fst $ head intpr

ex0 = [([Exactly (nat 2 0),Exactly (nat 2 1)],nat 2 1),([Any,Any],nat 2 0)]


expandArithFunction bw ar ints = do
    let vs = map (nat bw) [ 0 .. 2^bw -1 ]
    arg <- sequence $ replicate ar vs
    let argPat = map Exactly arg
    let val = lookup (\ xs ys -> and $ zipWith (eqPattern (==)) xs ys) argPat ints
    return ( argPat , val )

toArithFunction1 bitWidth ints = T.AFSum $ do
    let toNatural n = assert (width n <= bitWidth) $ T.AFNatural $ value n
    (argPat,val) <- ints
    let go [] = toNatural val
        go ((i,Exactly k): rest) = 
           T.AFIfEqual (T.AFVariable i) (toNatural k) (go rest) (T.AFNatural 0)
    return $ go $ zip [1..] argPat

-- for debugging:
deriving instance Show TPDB.CPF.Proof.Type.ArithFunction

toArithFunction0 bitWidth ints = goInts ints
          where
            toNatural n      = assert (width n <= bitWidth) $ T.AFNatural $ value n

            defaultValue     = toNatural $ snd $ head ints

            goInts []        = defaultValue
            goInts [([],v)]  = toNatural v
            goInts ints      = case p of
              Any       -> goInts same'
              Exactly k -> T.AFIfEqual (T.AFVariable i) (toNatural k)
                           (goInts same')
                           (goInts other)
              where
                d@(i,p)      = head $ fst $ head ints
                (same,other) = partition (\i -> head (fst i) == d) ints
                same'        = map (\(ps,v) -> (tail ps, v)) same

toCpfOrderingConstraintProof :: SymbolMap -> Arities -> UsableOrder SymLab
                             -> T.OrderingConstraintProof
toCpfOrderingConstraintProof symbolMap arities uo = case uo of
  (_, LinearInt lint ) -> 
    T.OCPRedPair $ T.RPInterpretation 
      $ T.Interpretation 
      { T.interpretation_type = T.Matrix_Interpretation
          { T.domain = T.Naturals, T.dimension = 1
          , T.strictDimension = 1 }
      , T.interprets = do
          (k,v @ (LinearFunction abs lin)) <- lint
          return $ T.Interpret 
                 { T.symbol = toCpfLabeledSymbol symbolMap k
                 , TPDB.CPF.Proof.Type.arity = length lin
                 , T.value = fun v
                 }
      }
   where 
    einpack x = matrix [[x]]
    matrix xss = T.Matrix $ map vector $ Data.List.transpose xss
    vector xs = T.Vector $ map T.Coefficient_Coefficient 
              $ map T.E_Integer xs
    fun f = T.Polynomial $ T.Sum 
          $ T.Polynomial_Coefficient (einpack $ value $ absolute f)
          : do (k,b) <- zip [1..] $ linear f
               let c = fromIntegral $ fromEnum b 
               return $ T.Product 
                      [ T.Polynomial_Coefficient (einpack c)
                      , T.Polynomial_Variable $ show k
                      ]
  (_, FilterAndPrec filter (Precedence prec)) -> 
    T.OCPRedPair $ T.RPPathOrder $ T.PathOrder 
      (map toPrecedenceEntry prec) (map toFilterEntry filter)
   where
    toPrecedenceEntry ((sym,label), prec) = 
        T.PrecedenceEntry (toCpfLabeledSymbol symbolMap (sym,label))
                        (arity sym)
                        (value prec)

    toFilterEntry ((sym,label), filter) =
      T.ArgumentFilterEntry (toCpfLabeledSymbol symbolMap (sym,label)) (arity sym)
        $ case filter of
            Selection is -> Right $ map (\i -> 1 + fromIndex i) is
            Projection i -> Left $ 1 + (fromIndex i)

    arity sym = case M.lookup sym arities of
      Nothing -> error $ "CO4.Test.TermComp2014.Proof.CPF.toCpfOrderingConstraintProof: missing symbol (" ++ show sym ++ ")"
      Just a  -> a

toCpfSymbol :: SymbolMap -> Symbol -> T.Symbol
toCpfSymbol symbolMap symbol = case M.lookup symbol symbolMap of
  Just (Left  i) -> T.SymName i
  Just (Right i) -> T.fromMarkedIdentifier i
  Nothing        -> error $ "CO4.Test.TermComp2014.Proof.CPF.toCpfSymbol: missing symbol (" ++ show symbol ++ ")"

toCpfLabeledSymbol :: SymbolMap -> (Symbol,Label) -> T.Symbol
toCpfLabeledSymbol symbolMap (symbol,label) = case M.lookup symbol symbolMap of
  Just (Right i) -> addCpfLabel label $ T.fromMarkedIdentifier i
  Nothing        -> error $ "CO4.Test.TermComp2014.Proof.CPF.toLabeledCpfSymbol: missing symbol (" ++ show symbol ++ ")"


addCpfLabel :: Label -> T.Symbol -> T.Symbol
addCpfLabel label symbol = T.SymLabel symbol $ T.LblNumber $ map value label

addCpfLabel' :: Label -> T.Marked T.Identifier -> T.Symbol
addCpfLabel' label id = addCpfLabel label $ T.fromMarkedIdentifier id
