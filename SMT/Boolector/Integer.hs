module SMT.Boolector.Integer where

import qualified SMT.Dictionary as D
       
import qualified Boolector as B
import Control.Applicative

dict :: Int 
     -> D.Dictionary B.Boolector N ( Integer ) B.Node
dict bits = D.Dictionary
    { D.info = "Boolector.Integer.Binary"
    , D.domain = D.Int
    , D.number = do
         n <- B.var bits
         z <- B.zero bits
         B.assert =<< B.sgte n z
         return $ N n
    , D.any_number = N <$> B.var bits
    , D.smallnumber = do
         prefix <- B.zero $ bits - 1
         bit <- B.var 1
         N <$> B.concat prefix bit
    , D.nbits = bits
    , D.nconstant = \ n -> N <$> B.int (fromIntegral n) bits
    , D.decode = \ a -> B.signedVal $ contents a
    , D.add = \ x y -> do
         a <- B.add (contents x) (contents y)
         o <- B.saddo (contents x) (contents y)
         B.assert =<< B.not o
         return $ N a
    , D.times = \ x y -> do
         m <- B.mul (contents x) (contents y)
         o <- B.smulo (contents x) (contents y)
         B.assert =<< B.not o
         return $ N m
    , D.positive = \ x -> do
         z <- B.zero bits
         B.sgt (contents x) z
    , D.nonnegative = \ x -> do
         z <- B.zero bits
         B.sgte (contents x) z
    , D.gt = \ x y -> do
         B.sgt (contents x) (contents y) 
    , D.ge = \ x y -> do
         B.sgte (contents x) (contents y) 
    , D.neq = \ x y -> do
         B.eq (contents x) (contents y) 
    , D.boolean = B.var 1
    , D.bconstant = \ b -> if b then B.true else B.false
    , D.and = B.and
    , D.or = B.or
    , D.not = B.not
    , D.beq = B.iff
    , D.assert = \ bs -> B.assert =<< B.or bs
    }

data N = N { contents :: B.Node }


