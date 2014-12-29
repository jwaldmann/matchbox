module SMT.Satchmo.Integer.Guarded where

import Prelude hiding ( not, and, or )
import qualified Prelude
import Control.Monad (when)


import SMT.Dictionary

import qualified Satchmo.SAT.Mini
import qualified Satchmo.Code
import qualified Satchmo.Boolean as B

import qualified Satchmo.Binary as Bin
import qualified Satchmo.Binary.Op.Fixed  

import Control.Monad ( forM, replicateM )
import Control.Applicative
import qualified Data.Map.Strict as M
import Data.Function (on )       

data Number = Number { bits :: [B.Boolean], guards :: [B.Boolean] }

guarded [] = return $ Number { bits = [], guards = [] }     
guarded bs = do
    let work [b] = return [b]
        work (b:bs) = do
            gs <- work bs
            g <- B.or [ b, head gs ]
            return $ g : gs
    gs <- work bs
    return $ Number { bits = bs, guards = gs }

get_guard n i =
    if i < length (guards n)
    then return $ guards n !! i
    else B.constant False
    
unknown bits = do
    bs <- replicateM bits B.boolean
    guarded bs
    
dict :: Int 
  -> Dictionary Satchmo.SAT.Mini.SAT Number Integer B.Boolean
dict w = Dictionary
    { info = unwords [ "binary", "bits:", show w, "(fixed, with guards)" ]
    , domain = SMT.Dictionary.Int
    , nbits = w
    , number = unknown w
    , decode = Satchmo.Code.decode . Bin.make . bits
    , nconstant = \ n -> guarded =<< fmap Bin.bits ( Bin.constant n )
    , boolean = B.boolean
    , bconstant = B.constant
    , add = \ x y -> do
        n <- guarded =<<  plus w (bits x) (bits y)
        forM (zip3 (guards x) (guards y) (guards n)) $ \ (x,y,z) -> do
             B.assert [ B.not x, z ] ; B.assert [ B.not y, z ]
        forM (zip3 (guards x) (guards y) (tail $ guards n)) $ \ (x,y,z') -> do
             B.assert [ x, y, B.not z' ] 
        return n
    , times = \ x y -> do
        n <- guarded =<< times0 w (bits x) (bits y)
        zss <- forM (zip [0..] $ guards x) $ \ (i,x) ->
            forM (zip [0..] $ guards y) $ \ (j,y) -> do
                z <- B.and[x,y] ; return (i+j, [z])
        let m = M.fromListWith (++) $ concat zss
        forM (M.toList m) $ \ (i,zs) -> do
            o <- B.or zs
            g <- get_guard n i ; B.assert [ B.not o, g ]
            g' <- get_guard n $ i + 2 ; B.assert [ B.not g', o ]
        return n
    , dot_product = undefined -- Satchmo.Binary.Op.Fixed.dot_product w
    , positive = \ n -> B.or $ bits n
    , gt = \ x y -> do
          out <- ( Bin.gt `on` ( Bin.make . bits ) ) x y
          forM ( zip (guards x) (guards y) ) $ \ (x,y) -> do
              B.assert [ B.not x, y,       out ]
              B.assert [ x, B.not y, B.not out ]
          return out
    , ge = \ x y -> do
          out <- ( Bin.ge `on` ( Bin.make . bits ) ) x y
          forM ( zip (guards x) (guards y) ) $ \ (x,y) -> do
              B.assert [ B.not x, y,       out ]
              B.assert [ x, B.not y, B.not out ]
          return out
    , neq = Bin.eq `on` ( Bin.make . bits )
    , and = B.and, or = B.or, not = return . B.not, beq = B.equals2, assert = B.assert
    }

times0 w [] ys = return []
times0 w xs [] = return []
times0 w (x:xs) ys = do
    z : zs <- forM ys $ \ y -> B.and [x,y]
    later <- times0 (w-1) xs ys
    (:) <$> return z <*> plus (w - 1) zs later

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

plus w xs ys = do
    let go    0 c xs ys = do
            forM ( c : xs ++ ys ) $ \ z -> B.assert [ B.not z ]
            return []
        go w c [] [] = do
            return [c]
        go w c (x:xs) [] = do
            (r,c) <- half_adder c x
            (:) <$> return r <*> go (w-1) c xs []
        go w c [] (y:ys) = do
            (r,c) <- half_adder c y
            (:) <$> return r <*> go (w-1) c [] ys
        go w c (x:xs) (y:ys) = do
            (r,c) <- full_adder x y c
            rs <- go (w-1) c xs ys
            return $ r : rs
    z <- B.constant False
    go w z xs ys

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


       
