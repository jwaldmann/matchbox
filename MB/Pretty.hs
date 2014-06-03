{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

module MB.Pretty where

import TPDB.Pretty
import qualified TPDB.DP
import TPDB.Data ( strict, rules, positions, lhs, rhs )


import qualified Satchmo.SMT.Exotic.Semiring.Arctic as A

import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M

import qualified Data.Map as M
import Data.List ( transpose, partition )

import System.IO

pretty_short sys = 
    let h us = 
            let (pre, post) = splitAt 10 us
            in  vcat [ vcat (map pretty pre)
                 , if null post then empty 
                   else nest 4 $ hsep [ pretty (length post), "more", "rules" ]
                 ]
        (s,w) = partition strict $ rules sys
    in  vcat [ h s, h w
             , nest 4 $ hsep [ "total", "size", pretty (system_size sys) ]
             ]

term_size t = length $ positions t
rule_size u = term_size (lhs u) + term_size (rhs u)
system_size s = sum $ map rule_size $ rules s

-- instance Pretty a => Show (TPDB.DP.Marked a) where
--     show = render . pretty

instance (Pretty k, Pretty v) =>  Pretty (M.Map k v) where
    pretty m = "M.Map" <+> vcat ( map pretty $ M.toList m )

instance Pretty a => Pretty (L.Linear a) where
    pretty l = 
        let ls = zipWith 
                    ( \ k m -> beside " " (pretty m) ( text ("* x" ++ show k ++ " +" ) ))
                 [ 1 .. ] ( L.lin l )
        in  besides $ ls ++ [ pretty $ L.abs l ]

-- NOTE strange behaviour for
-- pretty $ M.Matrix (2,2)[[1,2],[3,4]]  -- OK
-- pretty (8,M.Matrix (2,2)[[1,2],[3,4]]) -- WRONG

instance Pretty e => Pretty (M.Matrix e) where
    pretty m = case m of
        M.Zero {} -> "0"
        M.Unit {} -> "I"
        M.Matrix {} -> 
            ( besides $ map vcat  
                    $ transpose 
                    $ zipWith (:) ("[" : repeat "," )
                    $ map (map pretty ) 
                    $ M.contents m ) <+> "]"

besides docs = foldl1 (beside " ") docs

beside sep x y = vcat $ 
    let xs = lines $ render x 
        mx = maximum $ map length xs
        fill s = s ++ replicate (mx - length s) ' '
        ys = lines $ render y
        merge s t = text $ fill s ++ sep ++ t
    in    take (max (length xs) (length ys))
        $ zipWith merge (xs ++ repeat "") (ys ++ repeat "")

-- instance Pretty Integer where pretty = text . show

instance Pretty a => Pretty (A.Arctic a) where
    pretty a = case a of
        A.Minus_Infinite -> "-"
        A.Finite x -> pretty x

eprint = hPutStrLn stderr . show
