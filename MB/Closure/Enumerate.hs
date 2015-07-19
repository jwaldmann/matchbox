{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

module MB.Closure.Enumerate where

import qualified MB.Closure.Option as O

import Data.Hashable
import MB.Closure.Data
import qualified Data.HashSet as S
import qualified Data.PQueue.Min as Q
import Data.Foldable (foldr')
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Control.Monad ( guard )

import qualified Data.Map.Strict as M
import TPDB.Data 

fromSRS :: (Hashable c, Ord c)
        => SRS c -> [(B.ByteString, B.ByteString)]
fromSRS sys = do
  let sigma = S.fromList $ do u <- rules sys ; lhs u ++ rhs u
      m = M.fromList $ zip ( S.toList sigma ) ['a' .. ]
      pack s = C.pack $ map (m M.!) s
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
  c <- enumerate O.Both rules
  guard $ looping c
  return c

looping c = or $ do
  t <- B.tails $ target c
  return $ B.isPrefixOf (source c) t

data Certificate = Cycle_Loop
  { p :: B.ByteString  , q :: B.ByteString
  , a :: Int, b :: Int, c:: Int, d :: Int
  ,  closure :: OC
  }
  | Standard_Loop { closure :: OC }

instance Show Certificate where
  show z@Standard_Loop{} = unlines
    [ "is non-terminating because of looping derivation"
    , show $ closure z
    ]
  show z@Cycle_Loop{} = unlines
    [ "is cycle-non-terminating because of SRS derivation"
    , "from s =  p^" ++ show (a z) ++ " q^" ++ show (b z)
    , "  to t =  q^" ++ show (c z) ++ " p^" ++ show (d z)
    , "where p = " ++ show (p z)
    , "      q = " ++ show (q z)
    , show $ closure z
    ]

loop_certificates c = do
   guard $ looping c
   return $ Standard_Loop { closure = c }

cycle_loop_certificates c = do
   (sl,sr) <- splits $ source c
   guard $ not $ B.null sl
   guard $ not $ B.null sr
   let (slb,sle) = root sl ; (srb,sre) = root sr
   i <- [ 0 , B.length srb .. B.length $ target c ]
   let (tl,tr) = B.splitAt i $ target c
   tle <- exponentof srb tl
   tre <- exponentof slb tr
   guard $ tle >= sre && tre >= sle
   return $ Cycle_Loop
     { p = slb, a = sle, q = srb, b = sre, c = tle, d = tre
     , closure = c
     }


-- G045: 0000 -> 0101, 0101 -> 0010

-- 00101 -> 00010 ~ 00001 -> 01011-> 00101

-- 00001 -> 01011-> 00101 -> 00010

root s | B.null s = (s,1)
root s = head $ do
  i <- [ 1 .. B.length s ]
  guard $ 0 == mod (B.length s) i
  let (b,y) = B.splitAt i s
  e <- succ <$> exponentof b y
  return (b,e)

exponentof b s | B.null b = do
  guard $ B.null s
  return 1
exponentof b s = if B.null s then return 0 else do
  let (x,y) = B.splitAt (B.length b) s
  guard $ b == x
  succ <$> exponentof b y
    
enumerate dirs rules =  
  work_fc (map rule rules) $ \ x y -> do
    f <- case dirs  of
        O.Both -> [ lefts, insides, rights ]
        O.Left -> [ lefts, insides ]
        O.Right ->       [ insides, rights ]
    f x y

work_fc :: (Ord a, Hashable a)
           =>  [a] -> (a -> a -> [a]) -> [a]
work_fc base combine =
  let go done todo = case Q.minView todo of
        Nothing -> []
        Just (x,xs) ->
          if S.member x done
          then go done xs
          else (x :)  $ go (S.insert x done)
                 $ foldr' Q.insert xs
                 $ do b <- base ; combine x b
  in  go S.empty $ Q.fromList base

enumerate_ocs rules =
  work_oc (map rule rules) $ \ x y -> do
     f <- [lefts,rights,insides,outsides]
     f x y  ++ f y x

work_oc :: (Ord a, Hashable a)
           =>  [a] -> (a -> a -> [a]) -> [a]
work_oc base combine =
  let go done todo = case Q.minView todo of
        Nothing -> []
        Just (x,xs) ->
          if S.member x done
          then go done xs
          else (x :)  $ go (S.insert x done)
                 $ foldr Q.insert xs
                 $ do d <- S.toList done ; combine d x
  in  go (S.fromList base) 
        $ Q.fromList $ do x <- base ; y <- base ; combine x y
        
