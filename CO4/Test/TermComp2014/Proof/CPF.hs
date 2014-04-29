{-# LANGUAGE LambdaCase #-}
module CO4.Test.TermComp2014.Proof.CPF 
where

import           Control.Exception (assert)
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
  toCpfSemLabProof symbolMap trs model
  where
    (labeledTrs,True) = makeLabeledTrs model trs assignments

toCpfSemLabProof :: SymbolMap -> DPTrs () -> Model Symbol -> T.DpProof -> T.DpProof
toCpfSemLabProof symbolMap trs model = 
  T.SemLabProc model' dps  emptyTrs
  where
    model'   = toCpfModel symbolMap model
    emptyTrs = T.RS [] [] False
    dps      = T.DPS $ toTPDBRules symbolMap (\i () -> T.fromMarkedIdentifier i) trs

toCpfRedPairProof :: SymbolMap -> GroupedDPTrs Label -> [UsableOrder MSL] -> T.DpProof -> T.DpProof
toCpfRedPairProof symbolMap trs usableOrder innerProof = 
  T.RedPairProc ocp dps innerProof (Just usableRules)
  where
    ocp         = toCpfOrderingConstraintProof symbolMap trs usableOrder
    usableRules = T.DPS $ toTPDBRules symbolMap toLabeledSymbol
                        $ filterUsable
                        $ steps (tagAll trs) usableOrder
    dps         = T.DPS $ toTPDBRules symbolMap toLabeledSymbol
                        $ ungroupTrs trs

    filterUsable (TaggedGroupedTrs rs) = Trs $ map snd $ filter fst $ concat rs
    toLabeledSymbol i l                = addCpfLabel l $ T.fromMarkedIdentifier i

toCpfModel :: SymbolMap -> Model Symbol -> T.Model
toCpfModel symbolMap = T.FiniteModel (2^bitWidth) . map toInterpret 
  where
    Just bitWidth = M.foldlWithKey 
      (\bw symbol -> \case 
              Left  _ -> bw
              Right _ -> case bw of
                Nothing                    -> Just $ width symbol
                Just w | width symbol == w -> Just w
                _                          -> error "CO4.Test.TermComp2014.Proof.CPF.toCpfModel: diverging symbol widths"
      ) Nothing symbolMap

    toInterpret (sym, intpr) = T.Interpret (toCpfSymbol symbolMap sym) arity
                             $ T.ArithFunction 
                             $ toArithFunction intpr
      where 
        arity = length $ fst $ head intpr

    toArithFunction = T.AFSum . map (goMapping . indexArgs)
      where
        indexArgs (ps,v)        = (zip [0..] ps, v)
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
            Selection is -> Right $ map fromIndex is
            Projection i -> Left $ fromIndex i

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
