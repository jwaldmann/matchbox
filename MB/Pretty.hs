{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

module MB.Pretty where

import TPDB.Pretty
import qualified TPDB.DP

import qualified Satchmo.SMT.Integer as I
import qualified Satchmo.SMT.Linear as L
import qualified Satchmo.SMT.Matrix as M

import Text.PrettyPrint.HughesPJ (render, vcat, hsep, ( <+>), text )
import qualified Data.Map as M
import Data.List ( transpose )

import System.IO

instance Pretty a => Show (TPDB.DP.Marked a) where
    show = render . pretty

instance (Pretty k, Pretty v) =>  Pretty (M.Map k v) where
    pretty m = "M.Map" <+> vcat ( map pretty $ M.toList m )

instance Pretty a => Pretty (L.Linear a) where
    pretty l = 
        let ls = zipWith 
                    ( \ k m -> beside " " (pretty m) ( text ("* x" ++ show k ++ " +" ) ))
                 [ 1 .. ] ( L.lin l )
        in  besides $ ls ++ [ pretty $ L.abs l ]

instance Pretty e => Pretty (M.Matrix e) where
    pretty m = case m of
        M.Zero {} -> "0"
        M.Unit {} -> "I"
        M.Matrix {} -> besides $ map ( vcat . map pretty ) 
                               $ transpose $ M.contents m

besides = foldl1 (beside " ") 

beside sep x y = vcat $ 
    let xs = lines $ render x 
        mx = maximum $ map length xs
        fill s = s ++ replicate (mx - length s) ' '
        ys = lines $ render y
        merge s t = text $ fill s ++ sep ++ t
    in    take (max (length xs) (length ys))
        $ zipWith merge (xs ++ repeat "") (ys ++ repeat "")

instance Pretty Integer where pretty = text . show

eprint = hPutStrLn stderr . show
