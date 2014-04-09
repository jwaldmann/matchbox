module CO4.Test.TermComp2014.PPrint
where

import           Data.List (intercalate,intersperse,sortBy,groupBy)
import           Data.Function (on)
import qualified Data.Map as M
import           CO4.PreludeNat (value)
import           CO4.Test.TermComp2014.Standalone 
import           CO4.Test.TermComp2014.Util (SymbolMap)

pprintUnlabeledTrs :: SymbolMap -> UnlabeledTrs -> String
pprintUnlabeledTrs = pprintTrs pprintSymbol pprintSymbol $ const ""

pprintLabeledTrs :: (label -> String) -> SymbolMap -> Trs Symbol Symbol label -> String
pprintLabeledTrs = pprintTrs pprintSymbol pprintSymbol

pprintDPTrs :: (l -> String) -> SymbolMap -> DPTrs l -> String
pprintDPTrs goL symbolMap = pprintTrs pprintSymbol pprintMarkedSymbol goL symbolMap

pprintDPRule :: (l -> String) -> SymbolMap -> DPRule l -> String
pprintDPRule = pprintRule pprintSymbol pprintMarkedSymbol

pprintTrs :: (SymbolMap -> v -> String) -> (SymbolMap -> n -> String) -> (l -> String) 
          -> SymbolMap -> Trs v n l -> String 
pprintTrs goV goN goL symbolMap (Trs rules) = unlines $ map (pprintRule goV goN goL symbolMap) rules

pprintRule :: (SymbolMap -> v -> String) -> (SymbolMap -> n -> String) -> (l -> String) 
           -> SymbolMap -> Rule v n l -> String 
pprintRule goV goN goL symbolMap (Rule l r) = concat [ goTerm l, " -> ", goTerm r ]
  where
    goTerm (Var v)         = goV symbolMap v
    goTerm (Node s l args) = 
      case goL l of
        "" -> concat [ goN symbolMap s          ," (", intercalate ", " (map goTerm args), ")" ]
        l' -> concat [ goN symbolMap s, "^", l' ," (", intercalate ", " (map goTerm args), ")" ]

pprintValue :: Domain -> String
pprintValue = show . value

pprintSymbol :: SymbolMap -> Symbol -> String
pprintSymbol map symbol = case M.lookup symbol map of
  Nothing -> error "PPrint.pprintSymbol"
  Just s  -> s

pprintMarkedSymbol :: SymbolMap -> MarkedSymbol -> String
pprintMarkedSymbol symbolMap (s,b) = case b of
  False -> pprintSymbol symbolMap s
  True  -> pprintSymbol symbolMap s ++ "#"

pprintModel :: (SymbolMap -> s -> String) -> SymbolMap -> Model s -> String
pprintModel f symbolMap = unlines . intersperse "" . map pprintInterpretation
  where
    pprintInterpretation (s,i) = unlines $ map (pprintMapping $ f symbolMap s) i
      where
        pprintMapping s (xs, y) = 
          concat [ s, " ", intercalate " " (map (pprintPattern pprintValue) xs)
                 , " |-> ", pprintValue y ]

pprintPattern :: (k -> String) -> Pattern k -> String
pprintPattern f pattern = case pattern of
  Any       -> "*"
  Exactly k -> f k

pprintLabel :: Label -> String
pprintLabel vs = "[" ++ (intercalate ", " $ map pprintValue vs) ++ "]"

pprintPrecedence :: (SymbolMap -> s -> String) -> (l -> String) -> SymbolMap 
                 -> Precedence s l -> String
pprintPrecedence goS goL symbolMap = intercalate " > "
                                   . map     (intercalate " = " . map fst)
                                   . groupBy ((==)    `on` snd)
                                   . reverse
                                   . sortBy  (compare `on` snd)
                                   . map     (\((s,l),n) -> (goS symbolMap s ++ "^" ++ goL l, value n))

pprintArgFilter :: (SymbolMap -> s -> String) -> SymbolMap -> ArgFilter s -> String
pprintArgFilter goS symbolMap = unlines . map go
  where
    go (s,indices) = goS symbolMap s ++ (" [" ++ (intercalate ", " $ map (show . goIndex) indices)
                                              ++ "]")
    goIndex This     = 0
    goIndex (Next i) = 1 + (goIndex i)

