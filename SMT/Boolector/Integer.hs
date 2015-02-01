-- | signed integers.
-- with operations that accept operands of different bit lengths.
-- the output bit length is the max of the input bit lengths.

module SMT.Boolector.Integer where

import qualified SMT.Dictionary as D
       
import qualified Boolector as B
import Control.Applicative

dict :: Int 
     -> D.Dictionary B.Boolector N ( Integer ) B.Node
dict bits = D.Dictionary
    { D.info = "Boolector.Integer.Binary"
    , D.domain = D.Int
    , D.number = awed "number" $ do
         n <- B.var bits
         z <- B.zero bits
         B.assert =<< B.sgte n z
         return $ N bits n
    , D.any_number = awed "any_number" $ N bits <$> B.var bits
    , D.small_nn_number = awed "small_nn_number" $ do
         prefix <- B.zero 1
         bit <- B.var 1
         N 2 <$> B.concat prefix bit
    , D.small_number = awed "small_number" $ do
         n <- B.var 2
         m <- B.int (-2) 2 
         B.assert =<< B.sgt n m
         return $ N 2 n
    , D.nbits = bits
    , D.nconstant = \ n -> awed ( "nconstant" ++ show n ) $ N bits <$> B.int (fromIntegral n) bits
    , D.decode = \ a -> B.signedVal $ contents a
    , D.add = sextend $ \ x y -> do
         assert_equal_width "add" x y
         a <- B.add (contents x) (contents y)
         o <- B.saddo (contents x) (contents y)
         B.assert =<< B.not o
         return $ N (width x) a
    , D.times = sextend $ \ x y -> do
         assert_equal_width "times" x y
         m <- B.mul (contents x) (contents y)
         o <- B.smulo (contents x) (contents y)
         B.assert =<< B.not o
         return $ N (width x) m
    , D.positive = \ x -> do
         z <- B.zero (width x)
         B.sgt (contents x) z
    , D.nonnegative = \ x -> do
         z <- B.zero (width x)
         B.sgte (contents x) z
    , D.gt = sextend $ \ x y -> do
         assert_equal_width "gt" x y
         B.sgt (contents x) (contents y) 
    , D.ge = sextend $ \ x y -> do
         assert_equal_width "ge" x y
         B.sgte (contents x) (contents y) 
    , D.neq = sextend $ \ x y -> do
         assert_equal_width "neq" x y
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

uextend x y action = do
  let wx = width x ; wy = width y ; w = max wx wy
  ex <- N w <$> B.uext (contents x) (w - wx)
  ey <- N w <$> B.uext (contents y) (w - wy)
  action ex ey

sextend action = \ x y -> do
  let wx = width x ; wy = width y ; w = max wx wy
  aw ("sextend.x " ++ show (wx,wy,w) )  x
  aw ("sextend.y" ++ show (wx,wy,w) )  y
  ex <- N w <$> B.sext (contents x) (w - wx)
  aw ("sextend.ex " ++ show (wx,wy,w) )  ex
  ey <- N w <$> B.sext (contents y) (w - wy)
  aw ("sextend.ey" ++ show (wx,wy,w) )  ey
  action ex ey

assert_equal_width msg x y =
  if width x == width y then return ()
  else error $ unwords
       [ "SMT.Boolector.Integer:assert_equal_width", msg, show (width x, width y) ]

awed msg action = do x <- action ; aw msg x ; return x

aw msg x = do
  w <- B.getWidth $ contents x
  if w == width x then return ()
    else error $ unwords
         [ "SMT.Boolector.Integer:aw", msg, "claimed", show (width x), "actual", show w ]

data N = N { width :: Int , contents :: B.Node }

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
