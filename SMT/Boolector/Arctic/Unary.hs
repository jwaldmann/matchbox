module Boolector.Arctic.Unary where

import qualified Satchmo.SMT.Dictionary as D
import qualified Satchmo.SMT.Exotic.Semiring.Arctic as A
       
import qualified Boolector as B
import Control.Applicative

-- | number X is represented as bitvector with (X+1) ones,
-- starting from LSB. 

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
         f <- B.bval $ contents a
         if 0 == f then return A.Minus_Infinite
         else let h f = if f > 0 then succ $ h $ div f 2 else -1
              in  return $ A.Finite $ h f
    , D.add = \ x y -> do
         A <$> (contents x B.|| contents y)
    , D.times = \ x y -> do
         s <- B.add   (contents x) (contents y)
         o <- B.uaddo (contents x) (contents y)
         m <- minf x B.|| minf y
         B.assert =<< B.implies o m
         return $ A m s
    , D.positive = \ x -> B.slice (contents x) 0 0 
    , D.gt = \ x y -> do
         delta <- B.
         g <- B.and =<< sequence [ finite x, finite y, B.ugt (contents x) (contents y) ]
         g B.|| minf y
    , D.ge = \ x y -> do
         g <- B.and =<< sequence [ finite x, finite y, B.ugte (contents x) (contents y) ]
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

data A = A { contents :: B.Node }


