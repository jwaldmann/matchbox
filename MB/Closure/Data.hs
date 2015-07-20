-- | overlap closures for string rewriting,
-- representation using strict Bytestrings

{-# language BangPatterns #-}

module MB.Closure.Data

( OC () , size, source, target
, rule, lefts, rights, insides, outsides
, splits, assert_leq
)
       
where

import qualified Data.ByteString as B
import Data.Monoid
import Data.Hashable
import Control.Monad ( guard )
import Prelude hiding ( Either (..))
import Data.Function (on)

type S = B.ByteString

data OC = OC { source :: ! S
             , target :: ! S
             , hashcode :: ! Int
             , steps :: ! Int
             , size :: ! Int
             , reason :: ! Reason
             }
          deriving Show

-- | Ord and Eq instance only use source and target
-- (and, for efficiency, hashcode and size derived from this)
essence c = (size c, hashcode c, source c, target c)

instance Eq OC where (==) = (==) `on` essence
instance Ord OC where
  compare c d =
    let csize   = compare (size c) (size d)
        chash   = compare (hashcode c) (hashcode d)
        csource = compare (source c) (source d)
        ctarget = compare (target c) (target d)
        chain c1 c2 = case c1 of EQ -> c2 ; _ -> c1
    in  chain csize $ chain chash $ chain ctarget csource 

instance Hashable OC where
  hashWithSalt = error "OC.hashWithSalt"
  hash = hashcode

data Reason = Rule | Overlap !Position !Reason !Reason
  deriving Show

-- | kind and offset for overlap
data Position =
   Left !Int | Right !Int | Inside !Int | Outside !Int
  deriving Show

make r s t p = OC
  { reason = r
  , source = s
  , target = t
  , hashcode = hash (s,t)
  , steps = p
  -- note on size: this is used in the priority queue.
  -- we want small left-hand sides (sources)
  -- because they are much more likely to start a loop
  , size = B.length s + truncate ( logBase 2 $ fromIntegral $ B.length t )
  }

overlap p c d s t =
  make (Overlap p (reason c) (reason d)) s t (steps c + steps d)

rule (l, r) = make Rule l r 1

splits s = zip (B.inits s) (B.tails s)

assert_leq x mw = guard $ case mw of
  Just w -> x <= w
  Nothing -> True

lefts mw c d = do
  i <- [ 1 .. min (B.length $ target c)(B.length $ source d) ]
  assert_leq (B.length (target c) + B.length (target d) - i) mw
  let (!c1,!c2) = B.splitAt i $ target c
  let (!d1,!d2) = splitAtEnd i $ source d
  guard $ c1 == d2
  return $ overlap (Left i) c d (d1 <> source c) (target d <> c2) 

rights mw c d = do
  i <- [ 1 .. min (B.length $ target c)(B.length $ source d)]
  assert_leq (B.length (target c) + B.length (target d) - i) mw
  let (!c1,!c2) = splitAtEnd i $ target c
  let (!d1,!d2) = B.splitAt i $ source d
  guard $ c2 == d1
  return $ overlap (Right i) c d (source c <> d2) (c1 <> target d) 

splitAtEnd i s = B.splitAt (B.length s - i) s

insides mw c d = do
  assert_leq (B.length (target c) + B.length (target d) - B.length (source d)) mw  
  i <- [ 0 .. B.length (target c) - B.length (source d)]
  let (!c1,!c2) = B.splitAt i $ target c
  let (!c21,!c22) = B.splitAt (B.length $ source d) c2
  guard $ c21 == source d
  return $ overlap (Inside i) c d (source c) (c1 <> target d <> c22) 

outsides mw c d = do
  assert_leq (B.length (target d)) mw
  i <- [ 0 .. B.length (source d) - B.length (target c)]
  let (!d1,!d2) = B.splitAt i $ source d
  let (!d21,!d22) = B.splitAt (B.length $ target c) d2
  guard $ d21 == target c
  return $ overlap (Outside i) c d (d1 <> source c <> d22) (target d) 

