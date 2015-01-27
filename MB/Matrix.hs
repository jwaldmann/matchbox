{-# language OverloadedStrings #-}
{-# language DeriveGeneric #-}
{-# language TupleSections #-}
{-# language ScopedTypeVariables #-}

module MB.Matrix where

import qualified MB.Options as O
import MB.Options (dim, bits, Options)       
import MB.Pretty
import MB.Proof (Interpretation (..), Constraint (..))

import qualified MB.Count

import MB.Solver 

import TPDB.Data
import TPDB.Pretty
import qualified TPDB.DP

import qualified Compress.Common as CC

import qualified SMT.Dictionary as D
import qualified SMT.Semiring as S

import qualified SMT.Linear as L
import qualified SMT.Matrix as M

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List
import Control.Monad ( forM, void, foldM )
import Control.Monad.Identity
import Control.Applicative

import System.IO

import Data.Hashable

-- | note: we are assuming that we get a compressed system.
-- the choice of the compressor should be done outside this module.
-- so we only import Compress.Common (and none of the implementations).
-- We do return an interpretation for the _original_ signature
-- (because that is needed for independent verification)
-- and the remaining rules in the _compressed_ signature
-- (because we might want to avoid re-compression).

{-

handle :: (Show s, Hashable s, Ord v, Show v, Pretty v, Pretty s, Ord s
          , S.Semiring val, Pretty val
          , Solver m
          , Applicative m
          )
       => (Int -> D.Dictionary m num val bool )
       -> D.Dictionary (Either String) val val Bool
       -> Options
       -> TRS v (CC.Sym s)
       -> IO ( Maybe ( Interpretation v s val
                     , TRS v (CC.Sym s)))
       
-}
handle ( encoded :: Int -> D.Dictionary m num val bool) direct 
       opts (sys :: TRS v (CC.Sym s)) = do
    eprint $ pretty_short sys
    eprint $ show opts

    let count = MB.Count.run $ do
          fmap fst $
            system MB.Count.linear MB.Count.matrix MB.Count.elt opts sys
    hPutStrLn stderr $ show count

    out <- solve $ do
        let ldict = L.linear mdict
            mdict = M.matrix idict
            idict = encoded (bits opts)
        (funmap :: M.Map s (L.Linear (M.Matrix num)), con)
               <- system ldict mdict idict opts (sys:: TRS v (CC.Sym s))
        return $ do
          f <- mapdecode (L.decode ldict) funmap
          c <- cdecode ldict mdict con 
          return (f :: M.Map s (L.Linear (M.Matrix val)) , c  )

    case out of
        Just (f,con :: Constraint v s val ) -> do
            eprint $ pretty f
            let mcon = do
                  guard $ O.constraints opts > 0
                  return con
            let ldict = L.linear mdict
                mdict = M.matrix direct
                Right vs = evaluate_rules False
                   (ldict, mdict) (dim opts) (f, con) sys 
            case remaining_compressed False
                   (ldict, mdict) (dim opts) (f, con) sys of
                Right sys' -> return 
                   $ Just ( Interpretation 
                            { dimension = dim opts
                            , domain = D.domain direct
                            , mapping = f
                            , constraint = mcon
                            , values_for_rules = Just vs
                            }
                          , sys' )
                Left err -> error $ render $ vcat
                    [ "verification error"
                    , "input system: " <+> pretty sys
                    , "interpretation: " <+> pretty f
                    , "constraint: " <+> pretty con
                    , "message:" <+> vcat (map text $ lines  err)
                    ]
        Nothing -> return Nothing



cdecode :: (Ord s, Applicative m, Monad m)
        => L.Dictionary m (M.Matrix num) (M.Matrix val) bool
        -> M.Dictionary m num val bool
        -> Constraint v s num
        -> m (Constraint v s val)
cdecode l m con = Constraint
    <$> return (width con)
    <*> L.decode l (restriction con)
    <*> M.decode m (nonemptiness_certificate con)
    <*> mapdecode (mapM (M.decode m)) ( mapping_certificate con )
    <*> forM  ( compatibility_certificate con )
      ( \ (u,ws) -> ( u ,) <$> mapM (M.decode m) ws )


handle_dp :: (Show s, Hashable s, Ord v, Show v, Pretty v, Pretty s, Ord s
          , Pretty val, S.Semiring val
          , Solver m
          , Applicative m
          )
       => (Int -> D.Dictionary m num val bool )
       -> D.Dictionary (Either String) val val Bool
       -> Options
       -> TRS v (CC.Sym (TPDB.DP.Marked s))
       -> IO ( Maybe ( Interpretation v (TPDB.DP.Marked s) val
                     , TRS v (CC.Sym (TPDB.DP.Marked s))))
handle_dp encoded direct opts sys = do
    eprint $ pretty_short sys
    eprint $ show opts

    let count = MB.Count.run $ do
            system_dp MB.Count.linear opts sys
    hPutStrLn stderr $ show count

    out <- solve $ do
        let ldict = L.linear mdict
            mdict = M.matrix idict
            idict = encoded (bits opts) 
        funmap <- system_dp ldict opts sys
        return $ mapdecode (L.decode ldict) $ originals_only funmap

    case out of
        Just f -> do
            eprint $ pretty f
            let con = undefined
            let mdict = M.matrix direct 
                ldict = L.linear mdict
                rc = remaining_compressed True (ldict,mdict) (dim opts) (f,con) sys
            eprint $ pretty rc
            case rc of
                Right sys' -> return 
                   $ Just ( Interpretation 
                            { dimension = dim opts
                            , domain = D.domain direct
                            , mapping = f
                            , constraint = Nothing
                            }
                          , sys' )
                Left err -> error $ render $ vcat
                    [ "verification error"
                    , "input system: " <+> pretty sys
                    , "interpretation: " <+> pretty f
                    , "message:" <+> vcat (map text $ lines  err)
                    ]
        Nothing -> return Nothing
    

-- | check that all rules are weakly decreasing.
-- returns the system with the rules that are not strictly decreasing.
remaining_compressed 
  :: (Pretty num, Pretty k1, Pretty v, Ord k1, Ord v) =>
     Bool
     -> (L.Dictionary (Either String) (M.Matrix num) val1 Bool,
         M.Dictionary (Either String) num val Bool)
     -> Int
     -> (M.Map  k1 (L.Linear (M.Matrix num)),
         Constraint v k1 num)
     -> TRS v (CC.Sym k1)
     -> Either String (TRS v (CC.Sym k1))
remaining_compressed top dicts dim (funmap,con) sys = do
    decrease <- forM ( compatibility_certificate con ) $ \ (u,c) -> do
        True <- traced_rule top dicts dim
             ( funmap , restriction con) ( u, c)
        return u
    let keep u = fmap CC.expand_all u `notElem` decrease
    return $ sys { rules = filter keep $ rules sys }

evaluate_rules top dicts dim (funmap,con) sys = 
  forM ( compatibility_certificate con ) $ \ (u,c) -> do
        evaluate_rule top dicts dim (funmap , restriction con) ( u, c)

remaining top dicts dim (funmap,con) sys = do
    uss <- forM (compatibility_certificate con) $ \ (u,c) -> do
        s <- traced_rule top dicts dim (funmap,restriction con) (u,c) 
        return ( u, s )
    return $ sys { rules = map fst $ filter (not . snd) uss }

traced doc con = case con of
    Right x -> return x
    Left msg -> 
        Left $ show $ vcat [ doc , text msg ]

evaluate_rule top (ldict,_) dim (funmap,_)(u,_) = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term ldict dim funmap varmap $ lhs u
    r <- term ldict dim funmap varmap $ rhs u
    return (u, (l,r))

traced_rule top (ldict,mdict) dim (funmap,res) (u,us) = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term ldict dim funmap varmap $ lhs u
    r <- term ldict dim funmap varmap $ rhs u

    let -- res = restriction con
        [c] = L.lin res ; numc = L.to res
    let b = L.abs res
    sus <- foldM (M.add mdict) (M.Zero (dim,numc)) us
    susb <- M.times mdict sus b
    rhs <- M.add mdict (L.abs r) susb
    ge <- M.weakly_greater mdict (L.abs l) rhs
    gt <- M.strictly_greater mdict (L.abs l) rhs
    traced ( vcat [ "rule:" <+> pretty u
                  , "left:" <+> pretty l
                  , "right: " <+> pretty r
                  ]
           ) $ L.assert ldict [ge] 
    case relation u of
        Strict -> return gt
        Weak   -> case top of
            False -> return gt
            True  -> L.bconstant ldict  False -- cannot remove

mapdecode
  :: (Ord k, Monad m) => (a -> m a1) -> M.Map k a -> m (M.Map k a1)
mapdecode dec f = do
    pairs <- forM ( M.toList f) $ \ (k,v) -> do
        w <- dec v
        return (k,w)
    return $ M.fromList pairs 

originals_only funmap = M.fromList $ do
    ( CC.Orig o, f ) <- M.toList funmap
    return ( o, f )

-- | assert that at least one rule can be removed.
-- returns interpretation of function symbols.
{-
system :: (Ord s, Ord v, Pretty s, Show s, Functor m, Monad m)
       => L.Dictionary m (M.Matrix num) (M.Matrix val) bool
       -> M.Dictionary m num val bool
       -> O.Options
       -> RS s (Term v (CC.Sym s))
       -> m ( M.Map s (L.Linear (M.Matrix num))
            , Constraint v s  num
            )
-}
system dict mdict idict opts sys = do
    let dim = O.dim opts
    let (originals, digrams) = CC.deep_signature  sys
    
    -- restriction (written as linear function, res(x) >= 0)
    let numc = O.constraints opts
    res <- L.any_make dict 1 (numc,dim)

    -- non-emptiness certificate
    emp <- L.make dict 0 (dim,dim)
    femp <- L.substitute dict res [emp]
    nn <- L.nonnegative dict femp
    L.assert dict [ nn ]

    -- interpretation
    opairs <- forM originals $ \ ( f,ar) -> do
        l <- if O.triangular opts
             then L.triangular dict ar (dim , dim)
             else  L.make dict ar (dim , dim)
        s <- L.positive dict l
        L.assert dict [s]
        return (f, l)

    case O.mode opts of
      O.Complexity (Just d) | d < dim -> do
        pss <- forM ( opairs ) $ \ (f,l) -> do
          pss <- forM (L.lin l) $ \ m -> 
            forM (M.diagonal m) $ D.positive idict
          forM (Data.List.transpose pss) (D.or idict)
        ps <- forM (Data.List.transpose pss) (D.or idict)
        ok <- D.atmost idict d ps
        D.assert idict [ok]
      _ -> return ()

    -- mapping certificate
    mapcert <- M.fromList <$> forM opairs ( \ (CC.Orig f,l) -> do
      let [c] = L.lin res
      ws <- forM (L.lin l) $ \ m -> do
        w <- M.make mdict (numc,numc)
        cm <- M.times mdict c m
        wc <- M.times mdict w c
        ge <- M.weakly_greater mdict cm wc
        M.assert mdict [ ge ]
        return w
      let b = L.abs res
      ca <- M.times mdict c $ L.abs l
      lhs <- M.add mdict ca b
      wsb <- forM ws $ \ w -> M.times mdict w b
      rhs <- foldM (M.add mdict) (M.Zero (numc,1)) wsb
      ge <- M.weakly_greater mdict lhs rhs
      M.assert mdict [ ge ]
      return (f, ws)
      )
        
    funmap <- foldM (digger dict) (M.fromList opairs) digrams
    flagcerts <- forM (rules sys) 
             $ rule dict mdict dim funmap res

    let combine =  case O.remove_all opts of
          True -> M.and ; False -> M.or
    good <- combine mdict $ map fst flagcerts
    M.assert mdict [ good ]

    let con = Constraint
           { width = numc
           , restriction = res
           , nonemptiness_certificate = L.abs emp
           , mapping_certificate =  mapcert
           , compatibility_certificate =  map snd flagcerts
           }

    return ( originals_only funmap
           , con)

-- | assert that at least one rule can be removed.
-- returns interpretation of function symbols.
system_dp dict opts sys = do
    let dim = O.dim opts      
    let (originals, digrams) = CC.deep_signature  sys
    opairs <- forM originals $ \ (f,ar) -> do
        let topdim = case f of
                CC.Orig (TPDB.DP.Marked   {}) -> 1
                CC.Orig (TPDB.DP.Original {}) -> dim
        l <- L.make dict ar (topdim , dim)
        -- FIXME: this is a hack:
        when ( L.domain dict == D.Arctic ) $ do
            s <- L.positive dict l -- wrong name
            L.assert dict [s]
        return (f, l)
    funmap <- foldM (digger dict) ( M.fromList opairs ) digrams
    flags <- forM (rules sys) 
             $ rule_dp dict dim funmap
    L.assert dict flags 
    return funmap


digger dict m (CC.Dig d, _) = do
    let get s x = M.findWithDefault ( error
                $ unlines [ unwords [ "missing", s, "of", show d ] 
                        , show $ M.keys m
                        ] ) x m
        p = get "parent"  (CC.parent d) 
        pos = CC.position d - CC.position_index_start
        (pre, this : post) = 
              splitAt pos $ L.lin p
        c = get "child"   (CC.child d) 
    h <- L.substitute dict
        ( L.Linear {L.abs = L.abs p
           , L.lin = [ this ]
           } ) [ c ]
    let fg = L.Linear { L.abs = L.abs h
             , L.lin = pre ++ L.lin h ++ post
             , L.dim = (L.to p, L.from c)
             }
    return $ M.insertWith 
           (error "cannot happen")
           (CC.Dig d) fg m

-- | asserts weak decrease and returns strict decrease
rule
 :: (Ord o, Ord v, Monad m) =>
     L.Dictionary m (M.Matrix num) val bool
     -> M.Dictionary m num val1 t
     -> Int
     -> M.Map (CC.Sym o) (L.Linear (M.Matrix num))
     -> L.Linear (M.Matrix num)
     -> Rule (Term v (CC.Sym o))
     -> m (t, (Rule (Term v o), [M.Matrix num]))
rule dict mdict dim funmap res u = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term dict dim funmap varmap $ lhs u
    r <- term dict dim funmap varmap $ rhs u

    let [c] = L.lin res ; numc = L.to res
    us <- forM (zip (L.lin l) (L.lin r)) $ \ (lm,rm) -> do
      u <- M.make mdict (dim, numc)
      uc <- M.times mdict u c
      rhs <- M.add mdict rm uc
      ge <- M.weakly_greater mdict lm rhs
      M.assert mdict [ge]
      return u

    let b = L.abs res
    sus <- foldM (M.add mdict) (M.Zero (dim,numc)) us
    susb <- M.times mdict sus b
    rhs <- M.add mdict (L.abs r) susb
    ge <- M.weakly_greater mdict (L.abs l) rhs
    M.assert mdict [ge]
    gt <- M.strictly_greater mdict (L.abs l) rhs
    
    return (gt, ( fmap CC.expand_all u,us))

-- | asserts weak decrease and 
-- returns strict decrease (for strict rules)
rule_dp dict dim funmap u = do
    let vs = S.union (vars $ lhs u) (vars $ rhs u)
        varmap = M.fromList $ zip (S.toList vs) [0..]
    l <- term dict dim funmap varmap $ lhs u
    r <- term dict dim funmap varmap $ rhs u
    w <- L.weakly_greater dict l r
    L.assert dict [w] 
    case relation u of
        Strict -> L.strictly_greater dict l r
        Weak   -> L.bconstant dict False

term dict dim funmap varmap t = case t of
    Var v -> return 
        $ projection dim (M.size varmap) (varmap M.! v)
    Node f [] -> do
        let a = L.abs $ funmap M.! f 
        return $ L.Linear
               { L.abs = a
               , L.lin = replicate (M.size varmap) 
                       $ M.Zero (M.to a ,dim)
               }
    Node f args -> do
        gs <- forM args $ term dict dim funmap varmap 
        L.substitute dict (funmap M.! f) gs

-- TODO: move this to Satchmo.SMT.Linear
projection dim n i = 
   L.Linear { L.abs = M.Zero (dim,1)
            , L.lin = do
                   k <- [ 0 .. n-1]
                   return $ if k == i
                          then M.Unit (dim,dim)
                          else M.Zero (dim,dim)
            }

