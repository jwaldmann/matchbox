{-# LANGUAGE FlexibleContexts #-}
module Compress.Paper
  (Compression (..), compress, nocompress)
where

import           TPDB.Data
import           Compress.Common
import qualified Compress.Paper.TreeRePair as P
import qualified Compress.PaperIter.TreeRePair as PI
import           Compress.Paper.Costs (Costs(costs))

import Data.Hashable

data Compression = Simple | Iterative | Comparison deriving Show

compress :: (Ord sym, Hashable sym, Ord var, Costs (Trees var (Sym sym)))
         => Compression -> [Rule (Term var sym)] -> (Cost, Trees var (Sym sym))
compress compression rules = (Cost $ costs trees, trees)
  where 
    trees = increaseDigramPositions $ treeRePair $ lift $ build rules

    treeRePair = case compression of
                    Simple    ->  P.treeRePair
                    Iterative -> PI.treeRePair

    increaseDigramPositions ts = ts { roots  = map (fmap go)   $ roots  ts 
                                    , extras = map increaseSym $ extras ts
                                    }
      where 
        go (Node s ts) = Node (increaseSym s) $ map go ts
        go (Var v    ) = Var v

        increaseSym (Dig d) = Dig $ d 
                { parent    = increaseSym $ parent d 
                , position  = position d + 1 
                , child     = increaseSym $ child d
                }
        increaseSym s       = s

nocompress :: (Ord sym, Ord var, Costs (Trees var (Sym sym))) 
           => [Rule (Term var sym)] -> (Cost, Trees var (Sym sym))
nocompress rules = (Cost $ costs trees, trees)
  where 
    trees = lift $ build rules
