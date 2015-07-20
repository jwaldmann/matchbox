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

import qualified Data.Map.Strict as M
import TPDB.Data 

fromSRS :: (Hashable c, Ord c)
        => SRS c -> [(D.S, D.S)]
fromSRS sys = do
  let sigma = H.fromList $ do u <- rules sys ; lhs u ++ rhs u
      m = M.fromList $ zip ( H.toList sigma ) ['a' .. ]
      pack s = D.pack $ map (m M.!) s
  u <- rules sys
  return ( pack $ lhs u, pack $ rhs u )

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
  { a :: D.S, b :: D.S
  , p :: Int, q :: Int, r :: Int, s :: Int
  , closure :: D.OC
  }
  | Standard_Loop { closure :: D.OC }

instance Show Certificate where
  show z@Standard_Loop{} = unlines
    [ "is non-terminating because of looping SRS derivation"
    , show $ closure z
    ]
  show z@Cycle_Loop{} = unlines
    [ "is cycle-non-terminating because of SRS derivation"
    , "from  source = a^" ++ show (p z) ++ " b^" ++ show (q z)
    , "  to  target = b^" ++ show (r z) ++ " a^" ++ show (s z)
    , "where a = " ++ show (a z)
    , "      b = " ++ show (b z)
    , show $ closure z
    ]

loop_certificates c = do
   guard $ looping c
   return $ Standard_Loop { closure = c }

cycle_loop_certificates c = do
   (sl,sr) <- D.splits $ D.source c
   guard $ not $ D.null sl
   guard $ not $ D.null sr
   let (slb,sle) = root sl ; (srb,sre) = root sr
   i <- [ 0 , D.length srb .. D.length $ D.target c ]
   let (tl,tr) = D.splitAt i $ D.target c
   tle <- exponentof srb tl
   tre <- exponentof slb tr  
   guard $ tle >= sre 
         && tre >= sle
         && (divides sre  tle || divides sle tre )
   return $ Cycle_Loop
     { a = slb, b = srb , p = sle, q = sre, r = tle, s = tre
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

