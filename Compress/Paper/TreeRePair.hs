{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Compress.Paper.TreeRePair
  (treeRePair)
where

import Control.Monad.State
import TPDB.Data
import Compress.Common
import Compress.Paper.Selection (select)
import Compress.Paper.Digram (nonOverlappingOccurences)
import Data.Hashable

newtype TreeRePair var sym a = TreeRePair { run :: State (Trees var sym) a }
  deriving (Monad, Functor, MonadState (Trees var sym))

-- |Runs tree re-pair algorithm 
treeRePair :: (Ord var, Ord sym, Hashable sym) 
           => Trees var (Sym sym) -> Trees var (Sym sym)
treeRePair = execState $ run $ treeRePairStep

-- |Runs tree re-pair algorithm on the TRS of the @TreeRePair@ monad until
-- no more proper digrams are found.
treeRePairStep :: (Ord var, Ord sym, Hashable sym) => TreeRePair var (Sym sym) ()
treeRePairStep = do
  trees <- get
  case select trees of
    Nothing     -> return ()
    Just digram -> replaceInTrees digram >> treeRePairStep

-- |@replaceInTrees d s@ replaces all occurences of digram @d@ 
-- in trees of the @TreeRePair@ monad
replaceInTrees :: (Eq sym, Hashable sym) => Digram (Sym sym) -> TreeRePair var (Sym sym) ()
replaceInTrees digram = 
  modify $ \trees -> trees { roots  = map (fmap $ replaceInTerm digram) $ roots trees 
                           , extras = Dig digram : (extras trees)
                           }

-- |@replaceInTerm d s t@ replaces all occurences of digram @d@ in term @t@.
replaceInTerm :: (Eq sym, Hashable sym) 
              => Digram (Sym sym) -> Term var (Sym sym) -> Term var (Sym sym)
replaceInTerm digram term = foldl replaceAtPosition term
                          $ reverse 
                          $ nonOverlappingOccurences digram term
  where
    replaceAtPosition (Node _ fChild) [] = Node (Dig digram) 
                                         $ fChild1 ++ gChild ++ fChild2
      where
        (fChild1, (Node _ gChild) : fChild2) = splitAt (position digram) fChild

    replaceAtPosition (Node f fChild) (p:ps) = Node f $ fChild1 ++ [g'] ++ fChild2
      where
        (fChild1, g : fChild2) = splitAt p fChild
        g'                     = replaceAtPosition g ps
