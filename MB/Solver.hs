module MB.Solver where

import qualified Satchmo.SAT.Mini
import qualified Boolector

class Monad m => Solver m  where
    solve :: m (m a) -> IO (Maybe a)
    
instance Solver Satchmo.SAT.Mini.SAT where
    solve = Satchmo.SAT.Mini.solve

instance Solver Boolector.Boolector where
    solve = Boolector.withBoolector

    
