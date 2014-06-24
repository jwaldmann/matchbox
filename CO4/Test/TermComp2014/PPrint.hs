module CO4.Test.TermComp2014.PPrint
where

import           Data.List (intercalate,intersperse,sortBy,groupBy)
import           Data.Function (on)
import qualified Data.Map as M
import qualified TPDB.Data as TPDB
import qualified TPDB.DP as TPDB
import           CO4.PreludeNat (value)
import           CO4.Test.TermComp2014.Standalone 
import           CO4.Test.TermComp2014.Util (SymbolMap)

pprintUnlabeledTrs :: SymbolMap -> UnlabeledTrs -> String
pprintUnlabeledTrs = pprintTrs pprintSymbol pprintSymbolWithMark

pprintLabeledTrs :: (l -> String) -> SymbolMap -> LabeledTrs l -> String
pprintLabeledTrs goL = pprintTrs pprintSymbol $ pprintLabeled pprintSymbolWithMark goL

pprintTaggedLabeledTrs :: (l -> String) -> SymbolMap -> TaggedGroupedLabeledTrs l -> String
pprintTaggedLabeledTrs goL = pprintTaggedTrs pprintSymbol $ pprintLabeled pprintSymbolWithMark goL

pprintUnlabeledRule :: SymbolMap -> UnlabeledRule -> String
pprintUnlabeledRule = pprintRule pprintSymbol pprintSymbolWithMark

pprintTrs :: (SymbolMap -> v -> String) -> (SymbolMap -> n -> String)
          -> SymbolMap -> Trs v n -> String 
pprintTrs goV goN symbolMap (Trs rules) = unlines $ map (pprintRule goV goN symbolMap) rules

pprintTaggedTrs goV goN symbolMap (TaggedGroupedTrs ruless) = 
    unlines $ map (pprintTaggedRule goV goN symbolMap) $ concat ruless

pprintTaggedRule goV goN symbolMap (tag, Rule isMarked l r) = 
     unwords [ desc, goTerm l, "->", goTerm r ]
  where
    desc = case isMarked of
        True -> if tag then "keep" else "delete"
        False -> if tag then "usable" else "unusable"
    goTerm (Var v)       = goV symbolMap v
    goTerm (Node s args) = goN symbolMap s 
                        ++ (concat [ " (", intercalate ", " (map goTerm args), ")" ])


pprintRule :: (SymbolMap -> v -> String) -> (SymbolMap -> n -> String)
           -> SymbolMap -> Rule v n -> String 
pprintRule goV goN symbolMap (Rule isMarked l r) = 
  concat [ goTerm True l, " -> ", goTerm True r ]
  where
    goTerm _ (Var v) = goV symbolMap v
    goTerm topLeft (Node s args) = 
      concat [ goN symbolMap s -- pprintLabeledSymbol goN goL symbolMap (s,l)
             -- , if isMarked && topLeft then "#" else ""
             , concat [ " (", intercalate ", " (map (goTerm False) args), ")" ]
             ]

pprintValue :: Domain -> String
pprintValue = show . value

pprintSymbol :: SymbolMap -> Symbol -> String
pprintSymbol map symbol = case M.lookup symbol map of
  Nothing                        -> error "PPrint.pprintSymbol"
  Just (Left s)                  -> TPDB.name s
  Just (Right (TPDB.Original s)) -> TPDB.name s 
  Just (Right (TPDB.Marked   s)) -> TPDB.name s 

pprintSymbolWithMark :: SymbolMap -> Symbol -> String
pprintSymbolWithMark map symbol = case M.lookup symbol map of
  Nothing                        -> error "PPrint.pprintSymbolWithMark"
  Just (Left s)                  -> TPDB.name s
  Just (Right (TPDB.Original s)) -> TPDB.name s 
  Just (Right (TPDB.Marked   s)) -> TPDB.name s ++ "#"

pprintLabeledSymbolWithMark :: SymbolMap -> SymLab -> String
pprintLabeledSymbolWithMark = pprintLabeled pprintSymbol pprintLabel

pprintLabeled :: (SymbolMap -> n -> String) -> (l -> String) -> SymbolMap -> (n,l) -> String
pprintLabeled goN goL symbolMap (s,l) = 
  case goL l of
    "" -> goN symbolMap s
    l' -> concat [ goN symbolMap s, "^", l']

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
                 -> Precedence (s,l) -> String
pprintPrecedence goS goL symbolMap precedence = case precedence of 
    EmptyPrecedence -> "empty precedence"
    Precedence prec -> intercalate " > "
                                   . map     (intercalate " = " . map fst)
                                   . groupBy ((==)    `on` snd)
                                   . reverse
                                   . sortBy  (compare `on` snd)
                                   . map     (\((s,l),n) -> (goS symbolMap s ++ "^" ++ goL l, value n))
                                   $ prec

pprintArgFilter :: (SymbolMap -> s -> String) -> (l -> String) -> SymbolMap 
                -> ArgFilter (s,l) -> String
pprintArgFilter goS goL symbolMap = unlines . map go
  where
    go ((s,l),filt) = pprintLabeled goS goL symbolMap (s,l) ++ goFilter filt
    goFilter filt = case filt of
        Selection indices -> 
           (" select [" ++ (intercalate ", " $ map (show . goIndex) indices) ++ "]")
        Projection i -> 
           (" project " ++ (show . goIndex) i )
    goIndex This     = 0 :: Int
    goIndex (Next i) = 1 + (goIndex i)

pprintLinearInt :: (SymbolMap -> s -> String) -> (l -> String) -> SymbolMap 
                -> LinearInterpretation (s,l) -> String
pprintLinearInt  goS goL symbolMap = unlines . map go
  where
    go ((s,l),func) = pprintLabeled goS goL symbolMap (s,l)
                      ++ " : " ++ goFunc func

    goFunc (LinearFunction abs lins) = unwords $ intersperse " + "
        $ show (value abs) : map (\(_,i) -> "x_" ++ show i ) 
                         (filter (\(c,_) -> c) $ zip lins [1 :: Int ..])
