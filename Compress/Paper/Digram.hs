module Compress.Paper.Digram
where

import qualified Data.Set as S
import           Data.List (nubBy,sortBy)
import           Compress.Common
import           TPDB.Data.Term

-- |Gets all digrams of a term 
digrams :: (Ord sym) => Term var sym -> S.Set (Digram sym)
digrams (Var _)     = S.empty
digrams (Node i is) = toplevelDigrams `S.union` sublevelDigrams
  where
    mkDigram (pos, Node j js) = Digram i (length is) pos j (length js)
    toplevelDigrams           = S.fromList 
                                $ map mkDigram
                                $ filter (not . isvar . snd)
                                $ zip [0..] is
    sublevelDigrams           = S.unions $ map digrams is
    
-- |Gets all non-overlapping occurences of a digram in a term, s.t. the result 
-- includes the topest occurence. The resulting positions are ordered by their length. 
nonOverlappingOccurences :: (Eq sym) 
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
