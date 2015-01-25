module SMT.Satchmo.Natural where

import Prelude hiding ( not, and, or )
import qualified Prelude
import Control.Monad (when)


import SMT.Dictionary

import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code
import qualified Satchmo.Boolean as B

import qualified Satchmo.Binary as Bin
import qualified Satchmo.Binary.Op.Fixed  

import Control.Monad ( forM )
import Control.Applicative
import qualified Data.Map.Strict as M

dict :: Int 
  -> Dictionary Satchmo.SAT.Mini.SAT Bin.Number Integer B.Boolean
dict bits = Dictionary
    { info = unwords [ "binary", "bits:", show bits, "(fixed)" ]
    , domain = SMT.Dictionary.Int
    , nbits = bits
    , number = Bin.number bits
    , smallnumber = Bin.number 1
    , any_number = Bin.number bits
    , decode = Satchmo.Code.decode
    , nconstant = Bin.constant
    , boolean = B.boolean
    , bconstant = B.constant
    , add = \ x y -> Bin.make <$> plus bits (Bin.bits x) (Bin.bits y)
    , times = \ x y -> Bin.make <$> times0 bits (Bin.bits x) (Bin.bits y)
    , dot_product = undefined -- Satchmo.Binary.Op.Fixed.dot_product bits
    , positive = \ n -> B.or $ Bin.bits n
    , nonnegative = \ n -> B.constant True
    , gt = Bin.gt
    , ge = Bin.ge
    , neq = Bin.eq
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    }

times0 bits [] ys = return []
times0 bits xs [] = return []
times0 bits (x:xs) ys = do
    z : zs <- forM ys $ \ y -> B.and [x,y]
    later <- times0 (bits-1) xs ys
    (:) <$> return z <*> plus (bits - 1) zs later

times1 bits [] ys = return []
times1 bits xs [] = return []
times1 bits (x:xs) ys = do
    z : zs <- forM ys $ \ y -> B.and [x,y]
    later <- times1 (bits-1) ys xs
    (:) <$> return z <*> plus (bits - 1) zs later

times2 bits xs ys = do
    zss <- forM (zip [0..] xs) $ \ (i,x) ->
          forM (zip [0..] ys) $ \ (j,y) -> do
             z <- B.and[x,y] ; return ((i+j),[z])
    let start = M.fromListWith (++) $ concat zss
    let reduce m = case M.minViewWithKey m of
          Nothing -> return []
          Just ((i,zs),m') ->
            if i <= bits then case zs of
                (p : q : r : ss) | False  -> do
                    (r,c) <- full_adder p q r
                    reduce -- $ M.insert i (ss ++ [r])
                           $ M.insert i (r : ss )
                           $ M.insertWith (++) (i+1) [c]
                           $ m'                    
                (p : q : rs) -> do
                    (r,c) <- half_adder p q
                    reduce $ M.insert i (rs ++ [r])
                           -- $ M.insert i (r : rs )
                           $ M.insertWith (++) (i+1) [c]
                           $ m'
                [z] -> do
                    later <- reduce m' ; return $ z : later
            else do
                forM zs $ \ z -> B.assert [B.not z]
                reduce m'
    reduce $ start

plus bits xs ys = do
    let go    0 c xs ys = do
            forM ( c : xs ++ ys ) $ \ z -> B.assert [ B.not z ]
            return []
        go bits c [] [] = do
            return [c]
        go bits c (x:xs) [] = do
            (r,c) <- half_adder c x
            (:) <$> return r <*> go (bits-1) c xs []
        go bits c [] (y:ys) = do
            (r,c) <- half_adder c y
            (:) <$> return r <*> go (bits-1) c [] ys
        go bits c (x:xs) (y:ys) = do
            (r,c) <- full_adder x y c
            rs <- go (bits-1) c xs ys
            return $ r : rs
    z <- B.constant False
    go bits z xs ys

-- | (result, carry)
-- 0 extra vars, 7 clauses    
half_adder x y = (,) <$>  B.fun2 (/=) x y <*> B.and [x, y]

full_adder = full_adder_0

-- | (result, carry)
-- 3 extra vars, 17 clauses
full_adder_0 x y z = do
    (r1,c1) <- half_adder x y
    (r,c2) <- half_adder r1 z
    c <- B.or [c1,c2]
    when False $ do
        B.assert [ B.not r, B.not c, x ]
        B.assert [ B.not r, B.not c, y ]
        B.assert [ B.not r, B.not c, z ]
    when False $ do
        B.assert [ r, c, B.not x ]
        B.assert [ r, c, B.not y ]
        B.assert [ r, c, B.not z ]
    return (r,c)

-- | no extra vars, 16 clauses
full_adder_1 x y z = do
    r <- B.fun3 (\a b c -> odd $ sum $ map fromEnum [a,b,c]) x y z
    c <- B.fun3 (\a b c -> (> 1) $ sum $ map fromEnum [a,b,c]) x y z
    return (r,c)

-- | 3 extra vars, 21 clauses
full_adder_2 x y z = do
    r <- B.fun3 (\a b c -> odd $ sum $ map fromEnum [a,b,c]) x y z
    c <- sequence [ B.and [x,y] , B.and[y,z], B.and[z,x] ] >>= B.or
    return (r,c)

full_adder_3 p1 p2 p3 = do
    p4 <- B.boolean ; p5 <- B.boolean
    B.assert [B.not p2,p4,p5]
    B.assert [p2,B.not p4,B.not p5]
    B.assert [B.not p1,B.not p3,p5]
    B.assert [B.not p1,B.not p2,B.not p3,p4]
    B.assert [B.not p1,B.not p2,p3,B.not p4]
    B.assert [B.not p1,p2,p3,p4]
    B.assert [p1,p3,B.not p5]
    B.assert [p1,B.not p2,B.not p3,B.not p4]
    B.assert [p1,p2,B.not p3,p4]
    B.assert [p1,p2,p3,B.not p4]
    return ( p4, p5 )
