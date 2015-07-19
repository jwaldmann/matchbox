-- | overlap closures for string rewriting,
-- representation using strict Bytestrings

module MB.Closure.Data

( OC () , size, source, target
, rule, lefts, rights, insides, outsides
, splits
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
instance Ord OC where compare = compare `on` essence

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
  , size = B.length s 
  }

overlap p c d s t =
  make (Overlap p (reason c) (reason d)) s t (steps c + steps d)

rule (l, r) = make Rule l r 1

splits s = zip (B.inits s) (B.tails s)

lefts c d = do
  i <- [ 1 .. min (B.length $ target c)(B.length $ source d)]
  let (c1,c2) = B.splitAt i $ target c
  let (d1,d2) = B.splitAt i $ source d
  guard $ c1 == d2
  return $ overlap (Left i) c d (d1 <> source c) (target d <> c2) 

rights c d = do
  i <- [ 1 .. min (B.length $ target c)(B.length $ source d)]
  let (c1,c2) = splitAtEnd i $ target c
  let (d1,d2) = B.splitAt i $ source d
  guard $ c2 == d1
  return $ overlap (Right i) c d (source c <> d2) (c1 <> target d) 

splitAtEnd i s = B.splitAt (B.length s - i) s

insides c d = do
  i <- [ 0 .. B.length (target c) - B.length (source d)]
  let (c1,c2) = B.splitAt i $ target c
  let (c21,c22) = B.splitAt (B.length $ source d) c2
  guard $ c21 == source d
  return $ overlap (Inside i) c d (source c) (c1 <> target d <> c22) 

outsides c d = do
  i <- [ 0 .. B.length (source d) - B.length (target c)]
  let (d1,d2) = B.splitAt i $ source d
  let (d21,d22) = B.splitAt (B.length $ target c) d2
  guard $ d21 == target c
  return $ overlap (Outside i) c d (d1 <> source c <> d22) (target d) 

