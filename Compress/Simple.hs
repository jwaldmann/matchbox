{-# language ConstraintKinds #-}
{-# language NoMonomorphismRestriction #-}

module Compress.Simple 
( compress
, nocompress
, compress_tops
, simple_compress_tops
) where

import Compress.Common
import TPDB.Data
import TPDB.Pretty (Pretty)

import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad ( guard, forM )
import Data.List ( inits, tails, sortBy, minimumBy )
import Data.Function ( on )
import Data.Hashable

import Debug.Trace

type CC sym var 
    = (Ord sym, Hashable sym, Ord var, Pretty var, Pretty sym) 
type Compressor sym var 
    =  [Rule (Term var sym)] 
    -> (Cost, Trees var (Sym sym))

-- | no compression
nocompress :: CC sym var => Compressor sym var
nocompress rules = 
    let t = lift $ build rules
    in  ( cost All t, t )

data Evaluate = Weak_Only | All deriving ( Show )

-- | compression, using a brute-force search
compress :: CC sym var => Compressor sym var
compress = comp All . lift . build 

-- * cost for evaluating substitutions
cost_terms eval us = sum $ do
    u <- us 
    guard $ case eval of
        Weak_Only -> not $ strict u
        All -> True
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
cost eval trees = 
      cost_terms eval (roots trees) 
    + cost_digrams (extras trees)

all_digrams = digrams True
top_digrams = digrams_as_list False

digrams :: CC sym var
        => Bool -> Trees var sym -> S.Set (Digram sym)
digrams everywhere trees = 
    S.fromList $ digrams_as_list everywhere trees

digrams_as_list everywhere trees = do
    u <- roots trees
    t <- [ lhs u, rhs u ]
    Node f fargs <- 
        if everywhere then subterms t else [t]
    (i, a) <- zip [ position_index_start .. ] fargs
    Node g gargs <- return $ fargs !! (i - position_index_start)
    return $ Digram 
       { _digram_hash = hash ( f, i, g )
       , parent = f, parent_arity = length fargs
       , position = i, child = g
       , child_arity = length gargs }

-- * special handling for strict (DP) rules:
-- compress them from the top,
-- not computing any cost.

compress_tops = compress_tops_1 
simple_compress_tops = simple_compress_tops_1 

notrace s x = x

compress_tops_0 trees = 
    case top_digrams trees of
        [] -> trees
        dig : _ -> compress_tops 
            $ notrace (unlines [ "dig: " ++ show dig 
                             , "parent/child" ++ show (parent_arity dig, child_arity dig)
                             ] )
            $ apply_all True dig trees

compress_tops_1 trees = 
    let h us = case us of
            [] -> []
            u : vs -> case top_digrams ( Trees { roots = [u] } ) of
                [] -> u : h vs
                dig : _ -> h 
                    $ notrace (unlines [ "dig: " ++ show dig 
                            , "parent/child" ++ show (parent_arity dig, child_arity dig)
                             ] )
                    $ roots 
                    $ apply_all True dig 
                    $ Trees { roots = us } 
   in   Trees { roots = h $ roots trees }

simple_compress_tops_1 trees = 
    let h us = case us of
            [] -> []
            u : vs -> case top_digrams ( Trees { roots = [u] } ) of
                [] -> u : h vs
                dig : _ -> h 
                    $ notrace (unlines [ "dig: " ++ show dig 
                            , "parent/child" ++ show (parent_arity dig, child_arity dig)
                             ] )
                    $ ( roots 
                      $ apply_all True dig 
                      $ Trees { roots = [u] } 
                      ) ++ vs
   in   Trees { roots = h $ roots trees }

-- * replacement 

-- | brute force compression: 
-- in each step, apply each digram
-- and compute resulting cost,
-- chose one digram that achieves minimal cost,
-- stop if the cost is not reduced.

comp eval trees = 
    let cofun = cost eval
        handle (co,trees) =
            let outs = step cofun (co,trees)
            in case outs of
                (co', trees') : _ | co' < co -> 
                    handle (co', trees')
                _ -> (co, trees)
    in  handle (cofun trees, trees)

type Cofun var sym = Trees var sym -> Cost

step :: ( Ord sym, Hashable sym, Ord var
              , Pretty var, Pretty sym )
           => Cofun var (Sym sym)
           -> (Cost, Trees var (Sym sym))
           -> [(Cost, Trees var (Sym sym)) ]
step cofun (co, trees) = 
    sortBy (compare `on` fst )
           $ for (step_all trees) $ \ d -> (cofun d, d)

step_all trees = do
    dig <- S.toList $ digrams True trees
    return $ apply_all False dig trees 

-- | apply at all non-overlapping positions,
-- start searching for positions from the root (?)
-- if only_top is True, then this must be fast,
apply_all only_top dig trees = 
    Trees { roots = map (replace_rule only_top dig) 
                  $ roots trees
          , extras = Dig dig 
                   : extras trees
          }

match dig t = do
    Node f fargs <- return t
    guard $ f == parent dig
    let ( pre, this  : post ) = 
           splitAt (position dig - position_index_start) fargs
    Node g gargs <- return this
    guard $ g == child dig
    return ( pre, gargs, post )

replace_rule only_top dig u = 
    u { lhs = replace_all only_top dig $ lhs u
      , rhs = replace_all only_top dig $ rhs u
      }

replace_all only_top dig t0 = case t0 of
    Node f args0 -> 
        let args = case only_top of
                True  -> args0
                False -> map (replace_all only_top dig) args0
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
