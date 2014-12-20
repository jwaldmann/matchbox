module Boolector.Arctic.Binary where

import qualified Satchmo.SMT.Dictionary as D
import qualified Satchmo.SMT.Exotic.Semiring.Arctic as A
       
import qualified Boolector as B
import Control.Applicative

dict :: Int 
     -> D.Dictionary B.Boolector A ( A.Arctic Integer ) B.Node
dict bits = D.Dictionary
    { D.info = "Boolector.Arctic.Binary"
    , D.domain = D.Arctic
    , D.number = A <$> B.var 1 <*> B.var bits
    , D.nbits = bits
    , D.nconstant = \ v -> case v of
         A.Minus_Infinite -> A <$> B.true  <*> B.zero bits
         A.Finite n -> A <$> B.false <*> B.int (fromIntegral n) bits
    , D.decode = \ a -> do
         m <- B.bval $ minf a
         if m then return A.Minus_Infinite
         else A.Finite <$> B.signedVal ( contents a )
    , D.add = \ x y -> do
         g <- B.and =<< sequence [ finite x, finite y, B.sgt (contents x) (contents y) ]
         take_left <- g B.|| minf y
         s <- B.cond take_left (contents x) (contents y)
         m <- minf x B.&& minf y
         return $ A m s
    , D.times = \ x y -> do
         s <- B.add   (contents x) (contents y)
         o <- B.saddo (contents x) (contents y)
         m <- minf x B.|| minf y
         B.assert =<< B.implies o m
         return $ A m s
    , D.positive = \ x -> do
         B.and =<< sequence [ B.not $ minf x, B.not =<< B.slice (contents x) (bits-1) (bits-1) ]
    , D.gt = \ x y -> do
         g <- B.and =<< sequence [ finite x, finite y, B.sgt (contents x) (contents y) ]
         g B.|| minf y
    , D.ge = \ x y -> do
         g <- B.and =<< sequence [ finite x, finite y, B.sgte (contents x) (contents y) ]
         g B.|| minf y
    , D.neq = \ x y -> do
         c <- B.and =<< sequence [ finite x, finite y, B.eq (contents x) (contents y) ]
         e <- minf x B.&& minf y
         c B.|| e
    , D.boolean = B.var 1
    , D.bconstant = \ b -> if b then B.true else B.false
    , D.and = B.and
    , D.or = B.or
    , D.not = B.not
    , D.beq = B.iff
    , D.assert = \ bs -> B.assert =<< B.or bs
    }

data A = A { minf :: B.Node, contents :: B.Node }

finite x = B.not $ minf x
