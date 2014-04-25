{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Compress.Paper.Costs
  (Costs (..))
where

import qualified Data.Set as S
import           Data.List (delete)
import           Compress.Common
import           TPDB.Data

class Costs a where
  costs :: a -> Int
  
instance (Ord var, Eq sym) => Costs (Term var sym) where
  costs term = sum $ map numDifferentVars 
                   $ delete term 
                   $ subterms term
    where 
      numDifferentVars (Var _) = 0
      numDifferentVars node    = S.size $ vars node

instance Costs a => Costs (Rule a) where
  costs rule = costs (lhs rule) + costs (rhs rule)
  
instance Costs r => Costs (RS s r) where
  costs = sum . map costs . rules
  
instance (Ord var, Eq sym) => Costs (Problem var sym) where
  costs = costs . trs

instance Costs (Digram a) where
  costs = child_arity

instance Costs (Sym sym) where
  costs (Dig d) = costs d

instance (Ord var, Eq sym, Costs sym) => Costs (Trees var sym) where
  costs trees = (sum $ map costs $ roots trees)
              + (sum $ map costs $ extras trees) 
