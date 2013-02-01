module Compress.DP where

import Compress.Common
import Compress.Simple (position_index_start)

import TPDB.Data hiding ( subterms, positions )
import qualified TPDB.Data
import TPDB.DP ( Marked (..))

import TPDB.Plain.Read ( trs )
import TPDB.Plain.Write ()
import TPDB.Pretty

import qualified Data.Set as S
import Control.Monad ( guard )

z001 :: TRS Identifier Identifier
Right z001 = TPDB.Plain.Read.trs 
    "(VAR x)(RULES a(a(b(b(x))))->b(b(b(a(a(a(x)))))))"

-- | cf. corresponding code in TPDB.DP
dp :: Ord s
   => TRS v (Sym s) 
   -> TRS v (Sym (Marked s))
dp s =
   let copy_deep = fmap (fmap Original)
       mark_top (Node (Orig f) args) 
          = Node (Orig (Marked f)) 
          $ map copy_deep args
       os = map ( \ u -> Rule { relation = Weak
                       , lhs = copy_deep $ lhs u  
                       , rhs = copy_deep $ rhs u  
                               } )
           $ rules s
       defined = S.fromList $ do 
                u <- rules s
                let Node f args = expand_top $ lhs u 
                return f
       us = do 
            u <- rules s
            let l = mark_top $ lhs u
            r @ (Node f args) <-
                  map expand_top $ subterms $ rhs u
            guard $ S.member f defined
            return $ u { lhs = l, rhs = mark_top r }
   in RS { rules = us ++ os, separate = separate s } 

          
subterms = map snd . positions

-- | starting from a compressed term,
-- produce list of positions and subterms, 
-- keeping compression for subterms.
positions :: Term v (Sym o) 
         -> [ ( [Int], Term v (Sym o)) ]
positions t = ( [], t ) : case expand_top t of
    Node (Orig o) args -> do
            ( k, arg ) <- zip [ 0 .. ] args
            ( p, t' ) <- positions arg
            return ( k : p , t' )
    _ -> []

-- | expand digrams until the top symbol
-- is an original symbol.
expand_top :: Term v (Sym t) -> Term v (Sym t)
expand_top t = case t of
    Node (Dig d) args -> 
        let ( pre, midpost ) = 
                splitAt (position d - position_index_start) args
            ( mid, post) = splitAt (child_arity d) midpost
        in  expand_top 
            $ Node (parent d)
            $ pre ++ [ Node (child d) mid ] ++ post
    _ -> t
