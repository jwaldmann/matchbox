module Compress.Simple where

import TPDB.Data
import TPDB.Pretty
import TPDB.Plain.Write

import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad ( guard, forM )
import Data.List ( inits, tails, sortBy, minimumBy )
import Data.Function ( on )
import Text.PrettyPrint.HughesPJ


-- | main (exported) functions
compress, nocompress
  :: (Ord sym, Ord var, Pretty var, Pretty sym) 
  => [Rule (Term var sym)] 
  -> (Cost, Trees var (Sym sym))
compress rules = comp $ lift $ build $ rules 

nocompress rules = 
    let t = lift $ build rules
    in  ( cost t, t )

-- * type for storing a Set (list) of rules
-- (rule is pair of trees)

data Trees var sym = 
     Trees { roots :: [ Rule ( Term var sym ) ]
           , extras :: [ sym ]
         }
    deriving ( Eq, Ord )

instance ( Pretty var, Pretty sym ) 
     => Pretty (Trees var sym) where
   pretty ts = vcat  
     [ text "roots:" <+> vcat (map pretty $ roots ts)
     , text "extras:" 
        <+> vcat (map pretty $ extras ts) 
     ]

mapsym f trees =
    trees { roots = map (maprule f) $ roots trees } 

instance ( Pretty var, Pretty sym, Show sym ) 
       => Show (Trees var sym) where
    show = render . pretty

-- * constructing Trees from terms

build :: (Ord v, Ord s) 
      => [ Rule (Term v s) ] 
      -> Trees v s 
build ts = Trees { roots = ts, extras = [] }

-- * cost for evaluating substitutions

data Cost = 
     Cost { m_times_m :: Int
          } deriving (Eq, Ord, Show)

instance Pretty Cost where pretty = text . show

instance Num Cost where
    fromInteger i = Cost { m_times_m = fromInteger i }
    c1 + c2 = Cost { m_times_m = m_times_m c1 + m_times_m c2 
                   }

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

-- * digrams

data Digram sym = Digram
     { parent :: sym
     , position :: Int
     , child :: sym
     , child_arity :: Int
     } deriving ( Eq, Ord )

instance Pretty sym => Pretty (Digram sym) where
    pretty d = brackets $ hcat [ pretty (parent d)
         , text "/", pretty (position d)
         , text "/", pretty (child d)
         , text ".", pretty (child_arity d) ]

instance Pretty sym => Show (Digram sym) where
    show = render . pretty

digrams :: (Ord var, Ord sym) 
        => Trees var sym -> S.Set (Digram sym)
digrams trees = S.fromList $ do
    u <- roots trees
    t <- [ lhs u, rhs u ]
    Node f fargs <- subterms t
    (i, a) <- zip [1..] fargs
    Node g gargs <- return $ fargs !! (i-1)
    return $ Digram 
       { parent = f, position = i, child = g
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

-- *     

data Sym o = Orig o | Dig (Digram (Sym o))  
    deriving (Eq, Ord, Show)
instance Pretty o => Pretty (Sym o) where 
    pretty s = case s of
        Orig o -> pretty o
        Dig dig -> pretty dig

lift :: (Ord var, Ord o) 
     => Trees var o -> Trees var (Sym o)
lift trees = 
    Trees { roots = map (maprule (fmap Orig))
                  $ roots trees 
          , extras = [] }

maprule f u = 
    u { lhs = f $ lhs u, rhs = f $ rhs u }


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
