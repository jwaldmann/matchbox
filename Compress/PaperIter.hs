module Compress.PaperIter
  (compress, nocompress)
where

import TPDB.Data
import TPDB.Pretty
import Compress.Common
import Compress.PaperIter.TreeRePair (treeRePair)
import Compress.Paper.Costs (costs)

compress :: (Ord sym, Ord var, Pretty var, Pretty sym
                ,Show sym,Show var)  -- delete this
         => [Rule (Term var sym)] -> (Cost, Trees var (Sym sym))
compress rules = (Cost $ costs trees, trees)
  where 
    trees = increaseDigramPositions $ treeRePair $ lift $ build rules

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

nocompress :: (Ord sym, Ord var, Pretty var, Pretty sym) 
           => [Rule (Term var sym)] -> (Cost, Trees var (Sym sym))
nocompress rules = (Cost $ costs trees, trees)
  where 
    trees = lift $ build rules
