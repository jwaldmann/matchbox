module Compress.Paper.Weight
  (DigramWeight, simple, numVarsInChild)
where

import qualified Data.Set as S
import           TPDB.Data.Term
import           Compress.Common

type DigramWeight var sym = Digram sym -> Position -> Term var sym -> Int

simple :: DigramWeight var sym
simple _ _ _ = 1

numVarsInChild :: (Ord var) => DigramWeight var sym 
numVarsInChild digram pos term = 
  S.size $ vars (peek term $ pos ++ [position digram])
