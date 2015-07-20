{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}
{-# language BangPatterns #-}

module MB.Closure.Enumerate where

import qualified MB.Closure.Option as O

import Data.Hashable
import qualified MB.Closure.Data as D
import qualified Data.HashSet as H
import qualified Data.PQueue.Prio.Min as Q
import Data.Foldable (foldr')
import Control.Monad ( guard )
import Control.Applicative
import Data.Monoid 

import qualified Data.Map.Strict as M
import TPDB.Data 

import TPDB.Pretty

fromSRS :: (Hashable c, Ord c)
        => SRS c ->  [(D.S, D.S)] 
fromSRS sys = snd $ fromSRS_withmap sys

fromSRS_withmap :: (Hashable c, Ord c)
        => SRS c -> ( (M.Map c Char, M.Map Char c ), [(D.S, D.S)] )
fromSRS_withmap sys = 
  let sigma = H.fromList $ do u <- rules sys ; lhs u ++ rhs u
      fore = M.fromList $ zip ( H.toList sigma ) ['a' .. ]
      back = M.fromList $ zip ['a' .. ] $ H.toList sigma
      pack s = D.pack $ map (fore M.!) s
  in  ( (fore,back)
    , do
       u <- rules sys
       return ( pack $ lhs u, pack $ rhs u )
    )

hw1 = [ ("bc", "abb"), ("ba", "acb") ]
g03 = [ ("0000","0011"), ("1001","0010")]
g04 = [ ("0000","0101"),("0101","0010")]
g08 = [ ("0000","0110"), ("1001","0010")]
g10 = [ ("0000","0111"), ("1001","0010")]
b18 = [ ("aba","bba"),("bbb","ba"),("bb","aaa")]

test1 = take 1 $ loops hw1
test2 = take 1 $ loops g03
test3 = take 1 $ loops g08
test4 = take 1 $ loops g10

loops rules = do
  c <- enumerate O.Both Nothing rules
  guard $ looping c
  return c

looping c = or $ do
  t <- D.tails $ D.target c
  return $ D.isPrefixOf (D.source c) t

data Certificate = Cycle_Loop
  { u :: D.S, v :: D.S
  , p :: Int, q :: Int, r :: Int, s :: Int
  , closure :: D.OC
  }
  | Standard_Loop { closure :: D.OC }

instance Pretty Certificate where pretty = pretty_with True


pretty_with full z@Standard_Loop{} = vcat
    [ "looping SRS derivation"
    , D.pretty_with full $ closure z
    ]
pretty_with full z@Cycle_Loop{} = vcat
    [ "cycle-looping SRS derivation"
    , if full then vcat 
       [ text $ "from  source = u^" ++ show (p z) ++ " v^" ++ show (q z)
       , text $ "  to  target = v^" ++ show (r z) ++ " u^" ++ show (s z)
       , text $ "where u = " ++ show (u z)
       , text $ "      v = " ++ show (v z)
       ] else mempty
    , D.pretty_with full $ closure z
    ]

brief :: Certificate -> Doc
brief = pretty_with False

loop_certificates c = do
   guard $ looping c
   return $ Standard_Loop { closure = c }

cycle_loop_certificates c = do
   (sl,sr) <- D.splits $ D.source c
   guard $ not $ D.null sl
   guard $ not $ D.null sr
   let (uu,pp) = root sl ; (vv,qq) = root sr
   i <- [ 0 , D.length vv .. D.length $ D.target c ]
   let (tl,tr) = D.splitAt i $ D.target c
   rr <- exponentof vv tl
   ss <- exponentof uu tr  
   guard $  (pp == ss && qq <= rr) 
         || (pp <= ss && qq == rr)
   return $ Cycle_Loop
     { u = uu, v = vv , p = pp, q = qq, r = rr, s = ss
     , closure = c
     }

divides s t = 0 == mod t s

root s | D.null s = (s,1)
root s = head $ do
  i <- [ 1 .. D.length s ]
  guard $ 0 == mod (D.length s) i
  let (b,y) = D.splitAt i s
  e <- succ <$> exponentof b y
  return (b,e)

exponentof b s | D.null b = do
  guard $ D.null s
  return 1
exponentof b s = if D.null s then return 0 else do
  let (x,y) = D.splitAt (D.length b) s
  guard $ b == x
  succ <$> exponentof b y
    
enumerate dirs mw rules =  
  work_fc (map D.rule $ zip [0..] rules) $ \ x y -> do
    f <- case dirs  of
        O.Both -> [ D.lefts , D.insides , D.rights  ]
        O.Left -> [ D.lefts , D.insides  ]
        O.Right ->          [ D.insides, D.rights  ]
    f mw x y

work_fc base combine =
  let go !done !todo = case Q.minView todo of
        Nothing -> []
        Just (x,xs) ->
          if H.member x done
          then go done xs
          else (x :)  $ go (H.insert x done)
                 $ foldr (\e q -> Q.insert (D.size e) e q) xs
                 $ do b <- base ; combine x b
  in  go H.empty $ Q.fromList $ map (\b -> (D.size b,b)) $ base

