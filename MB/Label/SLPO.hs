{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# language OverloadedStrings #-}

module MB.Label.SLPO where

import           Language.Haskell.TH (runIO)

import qualified Satchmo.Core.SAT.Minisat
import qualified Satchmo.Core.Decode 
import           CO4 hiding (solve)
import           CO4.Prelude

import Data.List ( nub )
import Data.Maybe (maybeToList)
import qualified Data.Map as M
import Control.Monad ( forM,void )
import System.Environment
import GHC.Word (Word8)

import qualified TPDB.Data as TPDB
import qualified TPDB.Input as TPDB
import qualified TPDB.Pretty as TPDB
import qualified TPDB.Plain.Write as TPDB
import qualified TPDB.Plain.Read as TPDB
import TPDB.DP (dp)
import TPDB.Convert (srs2trs, trs2srs)

import qualified Text.PrettyPrint.Leijen.Text as PP
import Data.Text.Lazy (pack)
import System.Console.GetOpt

$( runIO $ configurable [ Verbose
                        , ImportPrelude
                        -- , DumpAll "/tmp/sl" 
                        -- , Profile
                        , Cache
                        ] 
         $ compileFile "MB/Label/SLPO.standalone.hs" )


uTree bits leaf = 
    let t depth = if depth > 0
                 then known 1 2 [ t (depth-1), t (depth-1) ]
                 else known 0 2 [ leaf ]
    in  t bits

cSymbol xs = case xs of
    [] -> known 0 2 []
    x:xs' -> 
        known 1 2 [ known (fromEnum x) 2 []
                  , cSymbol xs' 
                  ]

uModel sym_bits model_bits = uTree sym_bits 
                           $ uTree model_bits 
                           $ kList model_bits uBool

uQuasiPrec bits_for_symbols = 
    known 0 1 [ uBool
              , uTree bits_for_symbols $ uBool
              , uTree bits_for_symbols $ uNat bits_for_symbols 
              ]


uArctic bits = 
    constructors [ Just [], Just [ uNat bits] ]

uMatrix dim elem = 
    kList dim $ kList dim $ elem 

uInter bits_for_symbols dim bfn = known 0 1
    [ -- known 1 1 [] -- just natural
      constructors [ Just [], Just [] ] -- arctic or natural
    , uTree bits_for_symbols ( uMatrix dim $ uArctic bfn ) 
    , uTree bits_for_symbols ( uMatrix dim $ uNat    bfn ) 
    ]

uRemove bits_for_symbols dim bfn = known 0 1
    [ constructors [ Just [], Just [] ] -- LPO or Intepretation
    , uQuasiPrec bits_for_symbols
    , uInter bits_for_symbols dim bfn
    ]

uLab conf srs =
    let sigma = nub $ do u <- srs ;  lhs u ++ rhs u
        width = maximum $ do u <- srs; map length [lhs u,rhs u]
        bits_for_symbols = maximum $ map length sigma 
    in  known 0 1 
           [ uModel bits_for_symbols (bits_for_model conf)
           , kList (number_of_interpretations conf)
                  $ uRemove (bits_for_symbols + bits_for_model conf)
                            (dimension_for_matrices conf) (bits_for_numbers conf)
           , kList (length srs) uBool
           ]


toBin :: Int -> [Bool]
toBin x = 
    if x == 0 then [] else let (d,m) = divMod x 2 in odd m : toBin d

toBin' :: Int -> Int -> [Bool]
toBin' w x = 
    if w > 0 then let (d,m) = divMod x 2 in odd m : toBin' (w-1) d
    else if x == 0 then [] else error "toBin: not enough bits"

fromBin :: [Bool] -> Int
fromBin xs = foldr ( \ x y -> fromEnum x + 2*y ) 0 xs

alphabet :: TPDB.SRS TPDB.Identifier -> [ TPDB.Identifier ]
alphabet sys = nub $ concat 
            $ map (\ u  -> TPDB.lhs u ++ TPDB.rhs u) $ TPDB.rules sys 


data Config =
     Config { use_dp_transform :: Bool
             , bits_for_model :: Int
             , number_of_interpretations :: Int
             , dimension_for_matrices :: Int
             , bits_for_numbers :: Int
             }
    deriving Show

config0 = Config
         { use_dp_transform = False
         , bits_for_model = 1 
         , number_of_interpretations = 2
         , dimension_for_matrices = 2
         , bits_for_numbers = 4
         }

options = [ Option [] ["dp" ] 
             (NoArg ( \ conf -> conf { use_dp_transform = True } ) )
             "use dependency pairs transformation"
          , Option ['m'] ["model"]
             (ReqArg ( \ s conf -> conf { bits_for_model = read s } ) "Int")
             "bits for model"
          , Option ['i'] ["interpretations"]
             (ReqArg ( \ s conf -> conf { number_of_interpretations = read s } ) "Int")
             "number of interpretations"
          , Option ['d'] ["dimension"]
             (ReqArg ( \ s conf -> conf { dimension_for_matrices = read s } ) "Int")
             "matrix dimension"
          , Option ['b'] ["bits"]
             (ReqArg ( \ s conf -> conf { bits_for_numbers = read s } ) "Int")
             "bits for numbers"
          ]


__main = do
    argv <- getArgs
    case getOpt Permute options argv of
        (c,[f],[]) -> do
            let conf = foldl (flip id) config0 c
            solve conf f
        (_,_,errs) -> 
            ioError $ userError $ concat errs ++ usageInfo "SL" options

example = case TPDB.srs "(RULES a a -> a b a)" of 
    Right sys -> solveTPDB config0 sys

solve conf filePath = do
    sys <- TPDB.get_srs filePath 
    case use_dp_transform conf of
            False -> solve_completely conf sys
            True  -> solve_completely conf
                     $ maybe (error "huh") id $ trs2srs $ dp $ srs2trs sys

solve_completely :: ( Ord i, PP.Pretty i )
                 => Main.Config -> TPDB.SRS i -> IO ()
solve_completely conf sys = do
    print $ TPDB.text "input" PP.<+> TPDB.pretty sys
    if null $ TPDB.strict_rules sys
       then do
           print $ PP.text "is (relatively) terminating since there are no (strict) rules"
       else do
           print conf
           out <- solveTPDB conf sys
           case out of
               Nothing -> print $ PP.text "giving up"
               Just sys' -> solve_completely conf sys'

solveTPDB :: (Ord i, PP.Pretty i ) 
          => Main.Config -> TPDB.SRS i -> IO (Maybe (TPDB.SRS i))
solveTPDB conf sys = do

  let sigma = nub $ do u <- TPDB.rules sys ; TPDB.lhs u ++ TPDB.rhs u
      bits_for_symbols = length $ toBin $ length sigma - 1
      m = M.fromList $ zip sigma $ map (toBin' bits_for_symbols) [ 0 .. ]
      m' = M.fromList $ zip (map (toBin' bits_for_symbols) [0..]) sigma
      f xs = map (m M.!) xs ; f' xs = map (m' M.!) xs
      srs = for ( TPDB.rules sys ) $ \ u -> 
          let mode = case TPDB.relation u of 
                  TPDB.Strict -> Strict ; TPDB.Weak -> Weak
          in  Rule mode ( f $ TPDB.lhs u ) ( f $ TPDB.rhs u ) 

      bdt2map t = let h t xs = case t of
                          Leaf y -> [(xs, y)]
                          Branch l r -> h l (xs ++ [False]) ++ h r (xs ++ [True])
                  in  M.fromList $ h t []

      bdt2int t = M.fromList $ do
                  (xs, w) <- M.toList $ bdt2map t
                  v <- maybeToList $ M.lookup xs m'
                  return ( v, bdt2mod w )

      bdt2int' t = M.fromList $ do
                  (xs, w) <- M.toList $ bdt2map t
                  v <- maybeToList $ M.lookup xs m'
                  return ( v, w )

      bdt2mod t = M.fromList $ do
                  (k,v) <- M.toList $ bdt2map t
                  return ( fromBin k, fromBin v )

      mklab xs = do
          let (pre,post) = splitAt bits_for_symbols xs
          case M.lookup pre m'  of
              Nothing -> []
              Just v  -> return $ Labelled { symbol = v, label = post }

      bdt2labelled_int t = M.fromList $ do
          (xs, mat) <- M.toList $ bdt2map t
          l <- mklab xs
          return (l, mat)

  print $ TPDB.pretty sys
  print conf
  -- print srs
  -- print m

  let alloc = uLab conf srs
  solution <- solveAndTestP 
      srs 
      alloc encConstraint constraint

  case solution of
    Nothing -> return Nothing
    Just (Label mod ints remove) -> do
        print $ TPDB.pretty sys
        print $ "model:" PP.<$> PP.indent 4 ( PP.vcat
              $ for  ( M.toList $ bdt2int mod ) $ \ (k, v) -> 
                PP.hsep $ for (M.toList v ) $ \ (from,to) -> 
                    PP.hcat [ PP.pretty to, PP.pretty k, PP.pretty from ] 
              )
        let srs' = labelled srs mod
            mkrule (Rule m l r) = TPDB.Rule { TPDB.relation = case m of
                                         Strict -> TPDB.Strict ; Weak -> TPDB.Strict
                                 , TPDB.lhs = map (head . mklab) l 
                                 , TPDB.rhs = map (head . mklab) r
                                 , TPDB.top = False -- ??
                                 } 
        print $ ( "labelled system:" PP.<$> ) $ PP.indent 4 $ 
            PP.vcat $ for (labelled srs mod) $ \ subsrs -> 
                PP.vcat $ for subsrs $ \ ((lval,rval), u ) -> 
                    TPDB.pretty $ mkrule u
        void $ forM ints $ \ (Remove tag qp int) -> case tag of
            Remove_LPO -> case qp of 
              QP dir del ord -> do
                print $ PP.pretty $ Qup dir (bdt2labelled_int del) 
                                        (bdt2labelled_int ord )
            Remove_Interpretation -> case int of 
              Interpretation tag ai ni -> do
                print $ PP.pretty tag PP.<$> ( PP.indent 4 $ case tag of
                    Arctic_Tag  -> PP.pretty $ bdt2labelled_int ai
                    Natural_Tag -> PP.pretty $ bdt2labelled_int ni
                                             )                  

        let annotated = zip (TPDB.rules sys) remove 
            remaining = TPDB.with_rules sys $ map fst $ filter (not . snd) annotated
        print $ TPDB.pretty annotated
        return $ Just remaining
        
for = flip map

rulemap :: (a -> b) -> TPDB.Rule [a] -> TPDB.Rule [b]
rulemap f u = u { TPDB.lhs = map f $ TPDB.lhs u
                , TPDB.rhs = map f $ TPDB.rhs u
                }

-- * pretty printers

data Qup s = Qup Direction (M.Map s Bool) (M.Map s Nat)

instance (Ord s, PP.Pretty s ) => PP.Pretty (Qup s) where
    pretty (Qup dir del ord) = 
        let deleted = M.keys $ M.filter id del
            ord' = M.filterWithKey ( \ k v -> not $ del M.! k ) ord
            levels = reverse $ map snd $ M.toAscList
                   $ M.fromListWith (++) $ map ( \ (k,v) -> (v,[k]) ) $ M.toList ord'
            plevels = PP.hsep $ PP.punctuate ( " >" ) 
                    $ for levels $ \ xs -> 
                      PP.hsep $ PP.punctuate ( " =" )
                    $ for xs PP.pretty
        in  "LPO" PP.<$> PP.indent 4 ( PP.vcat 
                [ "direction:" PP.<+> PP.pretty dir
                -- , "heights:" PP.<+> PP.pretty ord'
                , "delete symbols:" PP.<+> PP.hsep (map PP.pretty deleted)
                , "precedence:" PP.<+> plevels
                ] )

data Labelled s = Labelled { symbol :: s, label :: [ Bool ] }
    deriving (Eq, Ord)

instance PP.Pretty s => PP.Pretty (Labelled s) where
    pretty ls = PP.pretty (symbol ls) PP.<> PP.pretty (fromBin $ label ls)


instance PP.Pretty Interpretation_Tag where pretty = PP.text . pack . show

instance PP.Pretty Nat where pretty = PP.text . pack . show 

instance PP.Pretty Arctic where
    pretty a  = case a of
        MinusInfinity -> "-"
        Finite f -> PP.text $ pack $ show f


instance PP.Pretty Direction where pretty = PP.text . pack . show

instance (PP.Pretty k, PP.Pretty v) => PP.Pretty (M.Map k v) where
    pretty m = PP.pretty $ M.toList m

