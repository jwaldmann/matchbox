-- | terms and digrams in such a way that
-- (==) is fast. Implementation uses 
-- unique identifiers, and is super ugly.

module Compress.Cached where

import qualified TPDB.Data as T

import Control.Monad.State.Strict
import Control.Monad ( forM )
import qualified Data.Map.Strict as M

data Pool s = 
    Pool { cache :: ! (M.Map (s, [Node s]) (Node s))
         , value :: ! (M.Map (Node s) (s, [Node s]))
         }

newtype Node s = Node Int deriving ( Eq, Ord )

node :: Ord s
     => s -> [Node s] -> State (Pool s) (Node s)
node f args = do
    p <- get
    case M.lookup (f, args) $ cache p of
        Just n -> return n
        Nothing -> do
            let n = Node $ M.size $ value p
            put $ p { cache = M.insert (f, args) n 
                            $ cache p
                    , value = M.insert n (f, args) 
                            $ value p
                    }
            return n

expand_term n = do
    p <- get
    case value p M.! n of
        (Left v, []) -> return $ T.Var v
        (Right f, ns) -> do
            ts <- forM ns expand_term
            return $ T.Node f ts

expand_rule u = do
    l <- expand_term $ T.lhs u
    r <- expand_term $ T.rhs u  
    return $ u { T.lhs = l, T.rhs = r }

expand_trs s = do
    us <- forM ( T.rules s ) expand_rule
    return $ s { T.rules = us }

build_term :: (Ord v, Ord s)
           => T.Term v s 
      -> State (Pool (Either v s)) 
               (Node (Either v s))
build_term t = case t of
    T.Var v -> node (Left v) []
    T.Node f args -> do
        xs <- forM args build_term
        node (Right f) xs

build_rule u = do
    l <- build_term $ T.lhs u
    r <- build_term $ T.rhs u
    return $ u { T.lhs = l, T.rhs = r }

build_trs s = do
    us <- forM ( T.rules s ) build_rule
    return $ s { T.rules = us }

