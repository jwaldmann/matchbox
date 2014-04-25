module Compress.Paper.Selection 
  (select)
where

import qualified Data.Set as S
import           Data.List (maximumBy)
import           TPDB.Data.Term
import           Compress.Common
import           Compress.Paper.Digram
import           Compress.Paper.Weight
import           Compress.Paper.Costs

import Data.Hashable

data DigramPosition = DigramPosition { termIndex      :: Int
                                     , positionInTerm :: Position
                                     } deriving Show

data DigramSaving sym = DigramSaving { digram :: Digram sym
                                     , saving :: Int } deriving (Show, Eq, Ord)
                                 
-- |Returns the digram with the highest saving, if there is such one
select :: (Ord var, Hashable sym, Ord sym) => Trees var sym -> Maybe (Digram sym)
select trees = bestDigram 
             $ digramSavings (allDigrams trees) (terms trees) numVarsInChild

bestDigram :: (Ord sym) => S.Set (DigramSaving sym) -> Maybe (Digram sym)
bestDigram digramSavings =
  if (not . S.null) digramSavings && saving maxDigram > 0 
  then Just $ digram maxDigram
  else Nothing
  where 
    maxDigram = maximumBy (\a b -> compare (saving a) (saving b)) 
              $ S.toList digramSavings

-- |@digramSavings ds ts f@ computes the savings of digrams @ds@ which occurs 
-- in @ts@ using the weighting function @f@
digramSavings :: (Ord sym, Hashable sym) 
              => S.Set (Digram sym) -> [Term var sym] -> DigramWeight var sym 
              -> S.Set (DigramSaving sym)
digramSavings digrams terms f = S.map toDigramSaving digrams
  where
    toDigramSaving digram = 
      let positions = nonOverlappingDigramPositions digram terms
      in
        DigramSaving digram $ digramSaving digram positions terms f

-- |@digramSaving d ps ts f@ computes the saving of digram @d@ which occurs at 
-- positions @ps@ in @ts@ using the weighting function @f@
digramSaving :: (Eq sym)
                => Digram sym -> [DigramPosition] -> [Term var sym] 
                -> DigramWeight var sym -> Int
digramSaving digram positions terms f = 
  (sum $ map weightOfDigramAtPos positions) - (costs digram)
  where 
    weightOfDigramAtPos p =  
      f digram (positionInTerm p) $ terms !! (termIndex p)

-- |Finds a set of nonoverlapping positions of a digram in a list of terms
nonOverlappingDigramPositions :: (Eq sym, Hashable sym)
                              => Digram sym -> [Term var sym] -> [DigramPosition] 
nonOverlappingDigramPositions digram = concatMap findPos . zip [0..]
  where
    findPos (termIndex, term) = 
      map (DigramPosition termIndex) $ nonOverlappingOccurences digram term
