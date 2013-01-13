{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Compress.Paper.Costs
  (Costs (..))
where

import qualified Data.Set as S
import           Compress.Common
import           TPDB.Data

class Costs a where
  costs :: a -> Int
  
instance Ord v => Costs (Term v s) where
  costs (Var _)     = 0
  costs (Node _ ts) = sum $ map numDifferentNonChildVars ts 
    where 
      numDifferentNonChildVars (Var _) = 0
      numDifferentNonChildVars node    = S.size $ vars node

instance Costs a => Costs (Rule a) where
  costs rule = costs (lhs rule) + costs (rhs rule)
  
instance Costs r => Costs (RS s r) where
  costs = sum . map costs . rules
  
instance Ord v => Costs (Problem v s) where
  costs = costs . trs

instance Costs (Digram a) where
  costs = child_arity

instance Ord v => Costs (Trees v s) where
  costs = sum . map costs . roots
