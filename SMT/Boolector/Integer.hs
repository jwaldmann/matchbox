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
    , D.atmost = atmost
    }

data N = N { contents :: B.Node }

-- implementation copied from Satchmo.
-- Can Boolector to this better in some built-in way?


atleast k xs = B.not <$> atmost (k-1) xs
        
atmost_block k [] = do
    t <- B.true
    return $ replicate (k+1) t
atmost_block k (x:xs) = do
    cs <- atmost_block k xs
    f <- B.false
    sequence $ do
        (p,q) <- zip cs ( f : cs )
        return $ B.cond x q p

atmost k xs = do
    cs <- atmost_block k xs
    return $ cs !! k
        
exactly_block k [] = do
    t <- B.true
    f <- B.false
    return $ t : replicate k f
exactly_block k (x:xs) = do
    f <- B.false
    cs <- exactly_block k xs
    sequence $ do
        (p,q) <- zip cs ( f : cs )
        return $ B.cond x q p 

exactly k xs = do
    cs <- exactly_block k xs
    return $ cs !! k
