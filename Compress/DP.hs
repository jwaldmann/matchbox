module Compress.DP where

import Compress.Common

import TPDB.Data hiding ( subterms, positions )
import qualified TPDB.Data
import TPDB.DP ( Marked (..))

import qualified Data.Set as S
import Control.Monad ( guard )

-- | cf. corresponding code in TPDB.DP
dp s =
   let marked (Node f args) = 
          Node (Marked f) $ map (fmap Original) args
       os = map ( \ u -> Rule { relation = Weak
                               , lhs = fmap Original $ lhs u  
                               , rhs = fmap Original $ rhs u  
                               } )
           $ rules s
       defined = S.fromList $ do 
                u <- rules s
                let Node f args = expand_top $ lhs u 
                return f
       us = do 
            u <- rules s
            let l = marked $ lhs u
            r @ (Node f args) <- subterms $ rhs u
            guard $ S.member f defined
            return $ u { lhs = l, rhs = marked r }
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
expand_top t = case t of
    Node (Dig d) args -> 
        let ( pre, midpost ) = splitAt (position d) args
            ( mid, post) = splitAt (child_arity d) midpost
        in  expand_top 
            $ Node (parent d)
            $ pre ++ [ Node (child d) mid ] ++ post
    _ -> t
