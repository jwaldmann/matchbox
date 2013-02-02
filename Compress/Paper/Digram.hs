module Compress.Paper.Digram
where

import qualified Data.Set as S
import           Data.List (nubBy,sortBy)
import           Compress.Common
import           TPDB.Data.Term

import Data.Hashable

-- |Gets all digrams of a term 
digrams :: (Ord sym, Hashable sym) => Term var sym -> S.Set (Digram sym)
digrams (Var _)     = S.empty
digrams term@(Node _ is) = topLevelDigrams term `S.union` subLevelDigrams
  where
    subLevelDigrams = S.unions $ map digrams is

-- |Gets all top level digrams of a term 
topLevelDigrams :: (Ord sym, Hashable sym) => Term var sym -> S.Set (Digram sym)
topLevelDigrams (Var {})    = S.empty
topLevelDigrams (Node i is) = S.fromList 
                            $ map mkDigram
                            $ filter (not . isvar . snd)
                            $ zip [0..] is
  where
    mkDigram (pos, Node j js) = 
       Digram { _digram_hash = hash ( i, pos, j )
              , parent = i
              , parent_arity = (length is) 
              , position = pos 
              , child = j
              , child_arity = (length js)
              }
    
-- |Gets the set of all digrams from @Trees@
allDigrams :: (Ord sym, Hashable sym) => Trees var sym -> S.Set (Digram sym)
allDigrams = S.unions . map digrams . terms

-- |Gets the set of all top level digrams from @Trees@
allTopLevelDigrams :: (Ord sym, Hashable sym) => Trees var sym -> S.Set (Digram sym)
allTopLevelDigrams = S.unions . map topLevelDigrams . terms

-- |Gets all non-overlapping occurences of a digram in a term, s.t. the result 
-- includes the topest occurence. The resulting positions are ordered by their length. 
nonOverlappingOccurences :: (Eq sym, Hashable sym) 
                         => Digram sym -> Term var sym -> [Position]
nonOverlappingOccurences digram term = nubBy isOverlapping topDownOccurences
  where
    occ                = occurences digram term 
    topDownOccurences  = sortBy (\a b -> compare (length a) (length b)) occ
    i                  = [position digram]
    isOverlapping v w  = or [ v == w, v ++ i == w , w ++ i == v ]

-- |Gets all occurences of a digram in a term
occurences :: (Eq sym) => Digram sym -> Term var sym -> [Position]
occurences digram = map fst . filter matchesParent . positions 
  where matchesParent (_, Var _)        = False 
        matchesParent (_, Node n terms) = 
             parent digram == n 
          && length terms > position digram 
          && matchesChild ( terms !! (position digram) )

        matchesChild (Var _)    = False
        matchesChild (Node n _) = n == child digram
