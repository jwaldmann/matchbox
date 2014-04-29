{-# LANGUAGE LambdaCase #-}
module CO4.Test.TermComp2014.Util
where

import           Control.Exception (assert)
import           Control.Monad.State
import           Data.List (nub)
import           Data.Either (partitionEithers)
import           Data.Tuple (swap)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified TPDB.Data as TPDB
import qualified TPDB.DP as TPDB
import           CO4.PreludeNat (nat)
import           CO4.Util (bitWidth)
import           CO4.Test.TermComp2014.Standalone hiding (ord)

type SymbolMap = M.Map Symbol (Either TPDB.Identifier (TPDB.Marked TPDB.Identifier))

fromTPDBTrs :: TPDB.TRS TPDB.Identifier (TPDB.Marked TPDB.Identifier) -> (UnlabeledTrs, SymbolMap)
fromTPDBTrs trs = (Trs rules', M.fromList $ map swap $ M.toList symbolMap)
  where
    numIds              = numIdentifiers trs
    (rules', symbolMap) = runState (mapM goRule $ TPDB.rules trs) M.empty

    goRule rule = 
      let isMarked = case TPDB.lhs rule of
                      TPDB.Node (TPDB.Marked _) _ -> True
                      _                           -> False
      in
        return (Rule isMarked) `ap` (goTerm $ TPDB.lhs rule) 
                               `ap` (goTerm $ TPDB.rhs rule)

    goTerm (TPDB.Var v) = 
      return Var `ap` goSymbol (Left v)

    goTerm (TPDB.Node v args) = 
      return Node `ap` goSymbol (Right v) `ap` return () `ap` mapM goTerm args

    goSymbol i = gets (M.lookup i) >>= \case
      Nothing -> do n <- gets M.size
                    let sym = assert (n < numIds)
                            $ nat (bitWidth numIds) $ fromIntegral n
                    modify $ M.insert i sym
                    return sym

      Just sym -> return sym

    numIdentifiers = length . nub . concatMap goRule . TPDB.rules
      where
        goRule rule = (goTerm $ TPDB.lhs rule) ++ (goTerm $ TPDB.rhs rule)
        goTerm term = (map Left $ TPDB.lvars term) ++ (map Right $ TPDB.lsyms term)

toTPDBRules :: SymbolMap -> (TPDB.Marked TPDB.Identifier -> label -> a) -> DPTrs label
            -> [TPDB.Rule (TPDB.Term TPDB.Identifier a)]
toTPDBRules symbolMap f (Trs rules) = map goRule rules
  where
    goRule (Rule isMarked lhs rhs) = TPDB.Rule (goTerm lhs) (goTerm rhs)
                                               (if isMarked then TPDB.Strict else TPDB.Weak)
                                               True -- top ???
    goTerm (Var s) = case M.lookup s symbolMap of
      (Just (Left i)) -> TPDB.Var i
    
    goTerm (Node s label args) = case M.lookup s symbolMap of
      (Just (Right i)) -> TPDB.Node (f i label) $ map goTerm args

assignments :: Ord var => Int -> Trs var n l -> Assignments var
assignments n trs = do 
  values <- sequence $ replicate (length vars) [0..(2^n)-1]
  return $ zipWith goMapping vars values
  where
    vars              = S.toList $ variableSet trs
    goMapping v value = (v, nat n value)

variableSet :: Ord v => Trs v s l -> S.Set v
variableSet (Trs rules) = S.unions $ map goRule rules
  where
    goRule (Rule _ l r) = variableSet' l `S.union` (variableSet' r)

variableSet' :: Ord v => Term v s l -> S.Set v
variableSet' (Var v)          = S.singleton v
variableSet' (Node _  _ args) = S.unions $ map variableSet' args

nodeArities :: Ord node => Trs v node l -> M.Map node Int
nodeArities (Trs rules) = M.fromListWith (\a b -> assert (a == b) a) 
                        $ concatMap goRule rules
  where 
    goRule (Rule _ l r)    = (goTerm l) ++ (goTerm r)
    goTerm (Var {})        = []
    goTerm (Node v _ args) = (v, length args) : (concatMap goTerm args)

isVar :: Term n v l -> Bool
isVar (Var _) = True
isVar _       = False

isSubterm :: (Eq v, Eq n, Eq l) => Term v n l -> Term v n l -> Bool
isSubterm subterm = go
  where
    go t@(Var _)       = t == subterm
    go t@(Node _ _ ts) = (t == subterm) || (any go ts)

isStrictSubterm :: (Eq v, Eq n, Eq l) => Term v n l -> Term v n l -> Bool
isStrictSubterm subterm term = (term /= subterm) && (isSubterm subterm term)

subterms :: Term v n l -> [Term v n l]
subterms = go
  where
    go t@(Var _)       = [t]
    go t@(Node _ _ ts) = t : (concatMap go ts)

ungroupTrs :: GroupedTrs v n l -> Trs v n l
ungroupTrs (GroupedTrs rules) = Trs $ concat rules

intermediates (Trs rules) g @ (GroupedTrs labeledRules) orders =
    assert (length rules == length labeledRules)
    $ scanl step (tagAll g) orders

removeMarkedUntagged (Trs rules) (TaggedGroupedTrs labeledRules) =  (Trs keep, delete)
  where
    (delete, keep) = partitionEithers $ zipWith check rules labeledRules
    check rule labeledRules = 
      if all (\ (tag,rule) -> isMarkedRule rule && not tag ) labeledRules
      then Left rule -- delete
      else Right  rule -- keep

hasMarkedRule :: DPTrs label -> Bool
hasMarkedRule (Trs rules) = any goRule rules
  where
    goRule (Rule isMarked _ _) = isMarked

isValidTrs :: Ord v => Trs v s l -> Bool
isValidTrs (Trs rules) = all isValidRule rules
  where
    isValidRule (Rule _ lhs rhs) = (not $ isVar lhs) 
                                && (variableSet' rhs `S.isSubsetOf` (variableSet' lhs))

fromIndex :: Num a => Index -> a
fromIndex This     = 0
fromIndex (Next i) = 1 + (fromIndex i)
