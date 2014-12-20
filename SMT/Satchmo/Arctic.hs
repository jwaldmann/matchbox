{-# language FlexibleInstances #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}

module Satchmo.SMT.Exotic.Arctic where

-- import Satchmo.SMT.Exotic.Dict
import Satchmo.SMT.Dictionary  hiding ( Arctic )
import qualified Satchmo.SMT.Dictionary  as D

import Language.SMTLIB

import Prelude hiding ( not, and, or )

import qualified Data.Map as M

import qualified Satchmo.Unary.Op.Flexible as X
import qualified Satchmo.Unary as N
import qualified Satchmo.Boolean as B

import qualified Satchmo.Code as C
import Satchmo.SAT.Mini (SAT)
import Control.Monad (forM, guard, when)

import qualified Satchmo.SMT.Exotic.Semiring.Arctic as A


data Arctic = Arctic { contents :: N.Number
                     }

minus_infinite = B.not . head . N.bits . contents

make c = do
    return $ Arctic { contents = c }

dict :: Int 
     -> Dictionary SAT Arctic ( A.Arctic Integer ) B.Boolean
dict bits = Dictionary { domain = D.Arctic 
  , number = do
    c <- N.number bits
    make c
  , nconstant = \ n -> do
        t <- B.constant True ; f <- B.constant False
        let nu k = N.make $ replicate k t ++ replicate (bits - k) f
        return $ Arctic $ nu $ fromInteger $ case n of
             A.Minus_Infinite -> 0
             A.Finite c -> c+1
  , decode = \ a -> do
        c <- C.decode $ contents a
        return $ if 0 == c then A.Minus_Infinite else A.Finite (c-1)
  , positive = \ x -> return $ B.not $ minus_infinite x
  , ge = \ l r -> N.ge ( contents l ) ( contents r ) 
  , gt = \ l r ->
    B.monadic B.or [ return $ minus_infinite r
                   , N.gt ( contents l ) ( contents r ) 
                   ]
  , add = \ x y -> do 
    c <- X.maximum $ map contents [x,y]
    make c
  , times = \ s t -> do
          m <- B.or [ minus_infinite s, minus_infinite t ]
          let a = contents s ; b = contents t
          let width = length $ N.bits a
          when ( length ( N.bits b ) /= width ) 
               $ error "Arctic.times: different bit widths"
          pairs <- sequence $ do
              (i,x) <- zip [0 .. ] $ N.bits a
              (j,y) <- zip [0 .. ] $ N.bits b
              guard $ i+j <= width
              return $ do z <- B.and [x,y] ; return (i+j, [z])
          cs <- forM ( map snd $ M.toAscList $ M.fromListWith (++) pairs ) B.or
          -- overflow is not allowed
          B.assert [ B.not $ last cs ]
          ds <- forM (init cs) $ \ c -> B.and [ B.not m, c ]
          make $ N.make ds

    , boolean = B.boolean
    , bconstant = B.constant
    , and = B.and
    , or = B.or
    , not = return . B.not 
    , beq = B.equals2
    , assert = B.assert
  }

