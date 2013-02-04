{-# language OverloadedStrings #-}

module MB.Count where

import qualified Satchmo.SMT.Dictionary as D
import qualified Satchmo.SMT.Matrix as M
import qualified Satchmo.SMT.Linear as L

import qualified Satchmo.SMT.Exotic.Semiring as S

import Control.Monad.State.Strict
import qualified Data.Map.Strict as M

data Count =
     Count { elem_alloc :: ! Int
           , elem_add :: ! Int
           , elem_times :: ! Int
           , matrix_alloc :: ! ( M.Map (Int,Int) Int )
           , matrix_add :: ! ( M.Map (Int,Int) Int )
           , matrix_times :: ! ( M.Map (Int,Int,Int) Int )
           } 
    deriving Show

run comp = execState comp count0

count0 = Count
        { elem_alloc = 0
        , elem_add = 0
        , elem_times = 0
        , matrix_alloc = M.empty
        , matrix_add = M.empty
        , matrix_times = M.empty
        }

instance S.Semiring () where

elt :: D.Dictionary (State Count) () () ()
elt = D.Dictionary
      { D.domain = D.Int -- that's a lie
      , D.nconstant = \ n -> return ()
      , D.bconstant = \ b -> return ()
      , D.number = modify $ \ c -> c { elem_alloc = succ $ elem_alloc c }
      , D.add = \ _ _ -> modify $ \ c -> c { elem_add = succ $ elem_add c }
      , D.times = \ _ _ -> modify $ \ c -> c { elem_times = succ $ elem_times c }
      , D.positive = \ _ -> return ()
      , D.and = \ _ -> return ()
      , D.ge = \ _ _ -> return ()
      , D.gt = \ _ _ -> return ()
      , D.assert = \ _ -> return ()
      }

matrix :: M.Dictionary (State Count) () () ()
matrix = 
    let d = M.matrix elt
    in  d { M.make = \ dim -> do
             -- count operation at the matrix level:
             modify $ \ c -> c { matrix_alloc = M.insertWith (+) dim 1 $ matrix_alloc c }
             -- execute elementary operations:
             -- (this will modify the counters at the elementary level)
             M.make d dim
          , M.add = \ a b -> do
             case (a,b) of
                (M.Zero {}, _) -> return () ; (_, M.Zero {}) -> return ()
                _ -> modify $ \ c -> 
                    c { matrix_add = M.insertWith (+) (M.dim a) 1 $ matrix_add c }
             M.add d a b
          , M.times = \ a b -> do
             case (a,b) of
                (M.Zero {}, _) -> return () ; (_, M.Zero {}) -> return ()
                (M.Unit {}, _) -> return () ; (_, M.Unit {}) -> return ()
                _ -> modify $ \ c -> 
                    c { matrix_times = M.insertWith (+) (M.to a, M.from a, M.from b) 1
                                   $ matrix_times c }
             M.times d a b
          }

linear :: L.Dictionary (State Count) (M.Matrix ()) (M.Matrix ()) ()
linear = L.linear matrix
