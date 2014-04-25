module Compress.DP where

import Compress.Common
import qualified Compress.Simple as CS

import TPDB.Data hiding ( subterms, positions )
import qualified TPDB.Data
import TPDB.DP ( Marked (..))

import TPDB.Plain.Read ( trs )
import TPDB.Plain.Write ()
import TPDB.Pretty

import qualified Data.Set as S
import Control.Monad ( guard )
import Data.Hashable
import Data.List

z001 :: TRS Identifier Identifier
Right z001 = TPDB.Plain.Read.trs 
    "(VAR x)(RULES a(a(b(b(x))))->b(b(b(a(a(a(x)))))))"

-- | compress strict rules from the top.
-- this should be applied after @dp@ (below)
fromtop :: (Hashable s, Ord s, Pretty s, Pretty v, Ord v)
   => TRS v (Sym s)
   -> TRS v (Sym s)
fromtop sys = 
    let (top, deep) = partition strict $ rules sys
        ctop = roots $ CS.compress_tops $ build top
    in  sys { rules = ctop ++ deep }

simple_fromtop sys = 
    let (top, deep) = partition strict $ rules sys
        ctop = roots $ CS.simple_compress_tops 
                     $ build top
    in  sys { rules = ctop ++ deep }



-- | compute DP transform for compressed system,
-- not expanding all digrams.
dp :: (Hashable s, Ord s, Pretty s, Pretty v)
   => TRS v (Sym s) 
   -> TRS v (Sym (Marked s))
dp s =
   let copy_deep = fmap (smap Original)
       mark_top t = case t of
           (Node (Orig f) args) -> 
               Node (Orig (Marked f)) $ map copy_deep args
           _ -> error $ "mark_top: " ++ show (pretty t)
       originals = map ( \ u -> Rule { relation = Weak
                       , lhs = copy_deep $ lhs u  
                       , rhs = copy_deep $ rhs u  
                               } )
           $ rules s
       defined = S.fromList $ do 
                u <- rules s
                let Node f args = expand_top $ lhs u 
                return f
       deepee = do 
            u <- rules s
            let l = mark_top $ expand_top $ lhs u
            r @ (Node f args) <-
                  map expand_top $ subterms $ rhs u
            guard $ S.member f defined
            return $ Rule { relation = Strict,  lhs = l, rhs = mark_top r }
   in RS { rules = deepee ++ originals
         , separate = separate s 
         } 

          
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


lift_marks_trs :: Hashable o
               => TRS v (Sym (Marked o))
           -> TRS v (Marked (Sym o))
lift_marks_trs sys = RS
    { rules = map (fmap $ fmap lift_marks) $ rules sys 
    , separate = separate sys
    }


lift_marks :: Hashable o
           => Sym (Marked o)
           -> Marked (Sym o)
lift_marks s = case s of
     Orig (Marked f) -> Marked (Orig f)
     Orig (Original f) -> Original (Orig f)
     Dig d -> case ( lift_marks $ parent d
                   , lift_marks $ child d ) of
         (Marked f, Original g) -> Marked $ Dig 
             $ hashed $ d { parent = f, child = g }
             
