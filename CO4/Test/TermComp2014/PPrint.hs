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
pprintUnlabeledTrs = pprintTrs pprintSymbol pprintSymbolWithMark $ const ""

pprintLabeledTrs :: (label -> String) -> SymbolMap -> Trs Symbol Symbol label -> String
pprintLabeledTrs = pprintTrs pprintSymbol pprintSymbolWithMark

pprintDPTrs :: (l -> String) -> SymbolMap -> DPTrs l -> String
pprintDPTrs goL symbolMap = pprintTrs pprintSymbol pprintSymbolWithMark goL symbolMap

-- pprintTaggedDPTrs :: (l -> String) -> SymbolMap -> TaggedDPTrs l -> String
pprintTaggedDPTrs goL symbolMap = pprintTaggedTrs pprintSymbol pprintSymbolWithMark goL symbolMap

pprintDPRule :: (l -> String) -> SymbolMap -> DPRule l -> String
pprintDPRule = pprintRule pprintSymbol pprintSymbolWithMark

pprintTrs :: (SymbolMap -> v -> String) -> (SymbolMap -> n -> String) -> (l -> String) 
          -> SymbolMap -> Trs v n l -> String 
pprintTrs goV goN goL symbolMap (Trs rules) = unlines $ map (pprintRule goV goN goL symbolMap) rules

pprintTaggedTrs goV goN goL symbolMap (TaggedGroupedTrs ruless) = 
    unlines $ map (pprintTaggedRule goV goN goL symbolMap) $ concat ruless

pprintTaggedRule goV goN goL symbolMap (tag, Rule isMarked l r) = 
     unwords [ desc, goTerm l, "->", goTerm r ]
  where
    desc = case isMarked of
        True -> if tag then "keep" else "delete"
        False -> if tag then "usable" else "unusable"
    goTerm (Var v)         = goV symbolMap v
    goTerm (Node s l args) = pprintLabeledSymbol goN goL symbolMap (s,l)
                         ++ (concat [ " (", intercalate ", " (map goTerm args), ")" ])


pprintRule :: (SymbolMap -> v -> String) -> (SymbolMap -> n -> String) -> (l -> String) 
           -> SymbolMap -> Rule v n l -> String 
pprintRule goV goN goL symbolMap (Rule isMarked l r) = 
  concat [ goTerm True l, " -> ", goTerm True r ]
  where
    goTerm _ (Var v) = goV symbolMap v
    goTerm topLeft (Node s l args) = 
      concat [ pprintLabeledSymbol goN goL symbolMap (s,l)
             -- , if isMarked && topLeft then "#" else ""
             , concat [ " (", intercalate ", " (map (goTerm False) args), ")" ]
             ]

pprintLabeledSymbol :: (SymbolMap -> n -> String) -> (l -> String) -> SymbolMap -> (n,l) -> String
pprintLabeledSymbol goN goL symbolMap (s,l) = 
  case goL l of
    "" -> goN symbolMap s
    l' -> concat [ goN symbolMap s, "^", l']

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
    go ((s,l),filt) = pprintLabeledSymbol goS goL symbolMap (s,l) ++ goFilter filt
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
    go ((s,l),func) = pprintLabeledSymbol goS goL symbolMap (s,l)
                      ++ " : " ++ goFunc func

    goFunc (LinearFunction abs lins) = unwords $ intersperse " + "
        $ show (value abs) : map (\(_,i) -> "x_" ++ show i ) 
                         (filter (\(c,_) -> c) $ zip lins [1 :: Int ..])
