module Compress.Paper
  (compress, nocompress)
where

import TPDB.Data
import TPDB.Pretty
import Compress.Common
import Compress.Paper.TreeRePair (treeRePair)
import Compress.Paper.Costs (costs)

compress :: (Ord sym, Ord var, Pretty var, Pretty sym) 
         => [Rule (Term var sym)] -> (Cost, Trees var (Sym sym))
compress rules = (Cost $ costs trees, trees)
  where 
    trees = treeRePair $ lift $ build rules

nocompress :: (Ord sym, Ord var, Pretty var, Pretty sym) 
           => [Rule (Term var sym)] -> (Cost, Trees var (Sym sym))
nocompress rules = (Cost $ costs trees, trees)
  where 
    trees = lift $ build rules
