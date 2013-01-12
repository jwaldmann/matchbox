module Compress.Simple 
  (compress, nocompress)
where

import Compress.Common
import TPDB.Data
import TPDB.Pretty (Pretty)

import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad ( guard, forM )
import Data.List ( inits, tails, sortBy, minimumBy )
import Data.Function ( on )

-- | main (exported) functions
compress, nocompress
  :: (Ord sym, Ord var, Pretty var, Pretty sym) 
  => [Rule (Term var sym)] 
  -> (Cost, Trees var (Sym sym))
compress rules = comp $ lift $ build $ rules 

nocompress rules = 
    let t = lift $ build rules
    in  ( cost t, t )

-- * constructing Trees from terms

build :: (Ord v, Ord s) 
      => [ Rule (Term v s) ] 
      -> Trees v s 
build ts = Trees { roots = ts, extras = [] }

-- * cost for evaluating substitutions
cost_terms us = sum $ do
    u <- us 
    t <- [ lhs u, rhs u ]
    Node f args <- subterms t
    arg <- args
    return $ case arg of
       Var {} -> 0
       Node {} -> fromIntegral $ S.size $ vars arg

cost_digrams ds = sum $ do
    Dig d <- ds  
    return $ fromIntegral $ child_arity d

-- | the main cost function
cost trees = 
      cost_terms (roots trees) 
    + cost_digrams (extras trees)

digrams :: (Ord var, Ord sym) 
        => Trees var sym -> S.Set (Digram sym)
digrams trees = S.fromList $ do
    u <- roots trees
    t <- [ lhs u, rhs u ]
    Node f fargs <- subterms t
    (i, a) <- zip [1..] fargs
    Node g gargs <- return $ fargs !! (i-1)
    return $ Digram 
       { parent = f, parent_arity = length fargs
       , position = i, child = g
       , child_arity = length gargs }
        
-- * replacement 

-- | brute force compression: 
-- in each step, apply each digram
-- and compute resulting cost,
-- chose one digram that achieves minimal cost,
-- stop if the cost is not reduced.

comp trees = 
    let handle (co,trees) =
            let outs = step (co,trees)
            in case outs of
                (co', trees') : _ | co' < co -> 
                    handle (co', trees')
                _ -> (co, trees)
    in  handle (cost trees, trees)

step :: ( Ord sym, Ord var
              , Pretty var, Pretty sym )
           => (Cost, Trees var (Sym sym))
           -> [(Cost, Trees var (Sym sym)) ]
step (co, trees) = 
    sortBy (compare `on` fst )
           $ for (step_all trees) $ \ d -> (cost d, d)

step_all trees = do
    dig <- S.toList $ digrams trees
    return $ apply_all dig trees 

-- | apply at all non-overlapping positions,
-- start searching for positions from the root (?)
apply_all dig trees = 
    Trees { roots = map (replace_rule dig) 
                  $ roots trees
          , extras = Dig dig 
                   : extras trees
          }

match dig t = do
    Node f fargs <- return t
    guard $ f == parent dig
    let ( pre, this  : post ) = 
           splitAt (position dig - 1) fargs
    Node g gargs <- return this
    guard $ g == child dig
    return ( pre, gargs, post )

replace_rule dig u = 
    u { lhs = replace_all dig $ lhs u
      , rhs = replace_all dig $ rhs u
      }

replace_all dig t0 = case t0 of
    Node f args0 -> 
        let args = map (replace_all dig) args0
            t = Node f args
        in  case match dig t of
                Nothing -> t
                Just (pre, gargs, post) ->
                    Node (Dig dig) 
                        $ pre ++ gargs ++ post
    _ -> t0                           

-- * utilities

for = flip map
splits xs = zip (inits xs) (tails xs)
