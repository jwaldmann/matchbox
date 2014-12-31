module SMT.Boolector.Arctic.Unary where

import qualified SMT.Dictionary as D
import qualified SMT.Semiring.Arctic as A
       
import qualified Boolector as B

import Control.Monad ( forM )
import Control.Applicative
import qualified Data.Map.Strict as M

-- | number X is represented as bitvector with (X+1) ones,
-- starting from LSB:
-- minf = 0..0 , 0 = 10..0, 1 = 110 .. 0, 2 = 1110 .. 0

dict :: Int 
     -> D.Dictionary B.Boolector A ( A.Arctic Integer ) B.Node
dict bits = D.Dictionary
    { D.info = "Boolector.Arctic.Unary"
    , D.domain = D.Arctic
    , D.number = A <$> B.var bits
    , D.nbits = bits
    , D.nconstant = \ v -> case v of
         A.Minus_Infinite -> A <$> B.zero bits
         A.Finite n -> A <$> B.unsignedInt (pred $ 2 ^ succ n) bits
    , D.decode = \ a -> do
         f <- B.val $ contents a
         if 0 == f then return A.Minus_Infinite
         else let h f = if f > 0 then succ $ h $ div f 2 else -1
              in  return $ A.Finite $ h f
    , D.add = \ x y -> do
         A <$> (contents x B.|| contents y)
    , D.times = \ x y -> do
{-
         f <- B.and =<< sequence [ finite x, finite y ]
         bs <- forM ( zip [0..] $ tail $ contents x) $ \(i,x)->
               forM ( zip [0..] $ tail $ contents y) $ \(j,y)->
               do z <- B.and [x,y,f]; return (i+j,[z])
         let (lo,hi) = splitAt (bits-1)
               $ map snd $ M.toAscList 
               $ M.fromListWith (++) $ concat bs
         forM hi $ \ zs -> forM zs $ \ z -> 
             B.assert =<< B.not z
         A <$> sequence ( return f : map B.or lo )
-}
         undefined
    , D.positive = finite
    , D.gt = \ x y -> do
         ny <- B.not $ contents y
         regular <- B.and [contents x, ny] >>= B.redor
         special <- infinite y
         B.or [ regular, special ]
    , D.ge = \ x y -> do
         nx <- B.not $ contents x
         B.and [nx, contents y] >>= B.redor >>= B.not
    , D.neq = \ x y -> undefined 

    , D.boolean = B.var 1
    , D.bconstant = \ b -> if b then B.true else B.false
    , D.and = B.and
    , D.or = B.or
    , D.not = B.not
    , D.beq = B.iff
    , D.assert = \ bs -> B.assert =<< B.or bs
    }

data A = A { contents :: B.Node }

finite n = B.slice (contents n) 0 0
infinite n = finite n >>= B.not


