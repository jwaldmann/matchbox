{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
module CO4.Test.TermComp2014.Proof.CPF 
where

import           Control.Exception (assert)
import           Data.List (nub)
import qualified Data.Map as M
import qualified TPDB.CPF.Proof.Type as T
import qualified TPDB.CPF.Proof.Util as T
import           TPDB.CPF.Proof.Xml ()
import qualified TPDB.Data as T
import qualified TPDB.DP as T
import           CO4.PreludeNat (width,value)
import           CO4.Test.TermComp2014.Util
import           CO4.Test.TermComp2014.Standalone

toCpfProof :: SymbolMap -> (DPTrs (), Assignments Symbol) -> Proof -> T.DpProof -> T.DpProof
toCpfProof symbolMap (trs, assignments) (Proof model order) = 
    toCpfSemLabProof  symbolMap labeledTrs model
  . toCpfRedPairProof symbolMap trs labeledTrs order
  where
    (labeledTrs,True) = makeLabeledTrs model trs assignments

toCpfSemLabProof :: SymbolMap -> GroupedDPTrs Label -> Model Symbol -> T.DpProof -> T.DpProof
toCpfSemLabProof symbolMap trs model = 
  T.SemLabProc model' dps trs'
  where
    model' = toCpfModel symbolMap model
    trs'   = T.DPS $ filter (not . T.strict) all
    dps    = T.DPS $ filter T.strict all
    all    = toTPDBRules symbolMap (flip addCpfLabel') $ ungroupTrs trs

toCpfRedPairProof symbolMap trs labeledTrs usableOrder innerProof = 
  T.RedPairProc { T.rppOrderingConstraintProof = ocp 
                , T.rppDps = dps 
                , T.rppUsableRules = (Just usableRules)
                , T.rppDpProof = inner'
                }
  where
    inner' = T.UnlabProc 
                { T.ulpDps = T.DPS 
                        $ filter T.strict
                        $ toTPDBRules symbolMap (flip addCpfLabel')
                        $ ungroupTrs trs'
                , T.ulpTrs = T.DPS
                        $ toTPDBRules symbolMap (flip addCpfLabel')
                        $ filterUsable
                        $ steps (tagAll labeledTrs) usableOrder
                , T.ulpDpProof = innerProof
                }

    ocp         = toCpfOrderingConstraintProof symbolMap labeledTrs usableOrder
    usableRules = T.DPS $ toTPDBRules symbolMap (flip addCpfLabel')
                        $ filterUsable
                        $ steps (tagAll labeledTrs) usableOrder

    dps         = T.DPS $ filter T.strict
                        $ toTPDBRules symbolMap (flip addCpfLabel')
                        $ ungroupTrs trs'

    filterUsable (TaggedGroupedTrs rs) = Trs 
      $ map snd 
      $ filter (\(isTagged, Rule isMarked _ _ ) -> not isMarked && isTagged) 
      $ concat rs
  
    ints = intermediates trs labeledTrs usableOrder
    trs' = removeMarkedUntagged_HACK (ungroupTrs labeledTrs) $ last ints

toCpfModel :: SymbolMap -> Model Symbol -> T.Model
toCpfModel symbolMap model = T.FiniteModel (2^bitWidth) $ map toInterpret model
  where
    bitWidth = width $ snd $ head $ snd $ head model

    toInterpret (sym, intpr) = T.Interpret (toCpfSymbol symbolMap sym) arity
                             $ T.ArithFunction 
                             $ toArithFunction intpr
      where 
        arity = length $ fst $ head intpr

        toArithFunction = T.AFSum . map (goMapping . indexArgs)
          where
            indexArgs (ps,v)        = (zip [1..] ps, v)
            goMapping ([],v)        = toNatural v
            goMapping ((i,p):ps, v) = 
              case p of
                Exactly k -> T.AFIfEqual (T.AFVariable i) (toNatural k) 
                                                          (goMapping (ps,v)) 
                                                          (T.AFNatural 0)
                Any       -> goMapping (ps,v)

            toNatural n = assert (width n <= bitWidth) $ T.AFNatural $ value n

toCpfOrderingConstraintProof :: SymbolMap -> GroupedDPTrs Label -> [UsableOrder MSL]
                             -> T.OrderingConstraintProof
toCpfOrderingConstraintProof symbolMap trs [(_, FilterAndPrec filter (Precedence prec))] = 
  T.OCPRedPair $ T.RPPathOrder $ T.PathOrder 
    (map toPrecedenceEntry prec) (map toFilterEntry filter)
  where
    arities = nodeArities $ ungroupTrs trs
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
