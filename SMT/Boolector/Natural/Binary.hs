module SMT.Boolector.Natural.Binary where

import qualified SMT.Dictionary as D
       
import qualified Boolector as B
import Control.Applicative

dict :: Int 
     -> D.Dictionary B.Boolector N ( Integer ) B.Node
dict bits = D.Dictionary
    { D.info = "Boolector.Arctic.Binary"
    , D.domain = D.Int
    , D.number = N <$> B.var bits
    , D.nbits = bits
    , D.nconstant = \ n -> N <$> B.unsignedInt (fromIntegral n) bits
    , D.decode = \ a -> B.val $ contents a
    , D.add = \ x y -> do
         a <- B.add (contents x) (contents y)
         o <- B.uaddo (contents x) (contents y)
         B.assert =<< B.not o
         return $ N a
    , D.times = \ x y -> do
         m <- B.mul (contents x) (contents y)
         o <- B.umulo (contents x) (contents y)
         B.assert =<< B.not o
         return $ N m
    , D.positive = \ x -> B.redor $ contents x
    , D.gt = \ x y -> do
         B.ugt (contents x) (contents y) 
    , D.ge = \ x y -> do
         B.ugte (contents x) (contents y) 
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


