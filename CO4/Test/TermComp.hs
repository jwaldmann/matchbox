{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CO4.Test.TermComp where

-- import qualified Prelude as P
-- import           Prelude (($), (-), (*), (.), (!!))

import qualified Data.Maybe as M
import qualified Data.List as L

import           Language.Haskell.TH (runIO)

import qualified Satchmo.Core.SAT.Minisat
import qualified Satchmo.Core.Decode 
import           CO4 hiding (solve)
import           CO4.Prelude 
import           CO4.Util (bitWidth,binaries,fromBinary)
import qualified TPDB.Data as TPDB
import qualified TPDB.Input as TPDB
import qualified TPDB.Pretty as TPDB
import qualified TPDB.Plain.Write as TPDB

$( compileFile [Verbose, ImportPrelude] "CO4/Test/TermComp.standalone.hs" )

uSymbol i = kList i uBool

solve filePath = do
  trs <- TPDB.get_trs filePath

  let l =            length $ symsOfTrs trs
      w = bitWidth $ length $ symsOfTrs trs


  putStrLn $ show $ TPDB.pretty trs
  putStrLn $ show $ varsOfTrs trs
  putStrLn $ show $ symsOfTrs trs

  solution <- solveAndTestP (mapTrs trs) (uList l (uSymbol w)) encMain main

  case solution of
    M.Nothing -> return ()
    M.Just s  -> putStrLn $ concat [ "Mapped solution: "
                                       , show $ map (mapSymbol' trs) s
                                       ]

--mapTrs :: TPDB.TRS TPDB.Identifier TPDB.Identifier -> C.TRS
mapTrs trs = map mapRule $ TPDB.rules trs
  where
    mapRule (TPDB.Rule lhs rhs _ _) = (mapTerm lhs , mapTerm rhs)

    mapTerm term = case term of
      TPDB.Var  v       -> Var $ lookup v vMapping
      TPDB.Node s terms -> Term (lookup s sMapping) $ map mapTerm terms

    vMapping    = zip vars (binaries' $ bitWidth $ length vars) 
    sMapping    = zip syms (binaries' $ bitWidth $ length syms)
    vars        = varsOfTrs trs
    syms        = symsOfTrs trs
    lookup x [] = []
    lookup x xs = M.fromJust $ L.lookup x xs

    binaries' =  binaries

varsOfTrs = foldl1 L.union
          . map (\rule -> L.union (TPDB.lvars $ TPDB.lhs rule)
                                    (TPDB.lvars $ TPDB.rhs rule)) 
          . TPDB.rules
  
symsOfTrs = foldl1 L.union
          . map (\rule -> L.union (TPDB.lsyms $ TPDB.lhs rule)
                                    (TPDB.lsyms $ TPDB.rhs rule)) 
          . TPDB.rules 

mapSymbol' trs symbol = symsOfTrs trs !! (fromBinary symbol)


{-

mapList :: [a] -> List a
mapList []     = Nil
mapList (x:xs) = Cons x $ mapList xs

mapList' :: List a -> [a]
mapList' Nil         = [] 
mapList' (Cons x xs) = x : (mapList' xs)

mapBool :: Bool -> Bool
mapBool False = False
mapBool True  = True

mapBool' :: Bool -> Bool
mapBool' False = False
mapBool' True  = True

-}
