{-# language CPP #-}

-- | forward/overlap closures for string rewriting,
--
-- with hard-coded representation
-- (not [a], but ByteString or Text)
-- 
-- NOTE: the actual representation type should be hidden
-- (do not leak outside this module)
-- so it can be exchanged easily.
-- This is the reason for the exports below.
-- see MB.Closure.Enumerate for a usage example.

{-# language BangPatterns #-}
{-# language OverloadedStrings #-}
{-# language NoMonomorphismRestriction #-}

module MB.Closure.Data

( OC () , S (), size, source, target
, rule, lefts, rights, insides, outsides
, splits, splitAt, null, length, isPrefixOf, tails, pack
, assert_leq
, pretty_with
)
       
where

import Prelude hiding ( Either (..), length, null, splitAt )
import qualified Prelude

import Data.Monoid
import Data.Hashable
import Control.Monad ( guard )
import Data.Function (on)

#define BS 1
#define TEXT 0
#define LIST 0

#if (BS)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C

import Data.ByteString.Search.KMP (indices)
-- import Data.ByteString.Search (indices)
-- import Data.ByteString.Search.DFA (indices)
#endif

import TPDB.Pretty hiding ((<>))

-- import qualified Data.ByteString.Lazy as B
-- import qualified Data.ByteString.Lazy.Char8 as C

#if (TEXT)
import qualified Data.Text as B
-- import qualified Data.Text.Lazy as B
#endif

#if (LIST)
import qualified Data.List as B
#endif

#if (BS)
type S = B.ByteString
#endif

#if (TEXT)
type S = B.Text
#endif

#if (LIST)
type S = [Char]
#endif

#if (BS)
instance Pretty B.ByteString where pretty = text . C.unpack
#endif

#if (BS)
pack = C.pack
#endif

#if (TEXT)
instance Pretty B.Text where pretty = text . B.unpack
pack = B.pack
#endif

#if (LIST)
pack = id
#endif

length = B.length
null = B.null
splitAt = B.splitAt
isPrefixOf = B.isPrefixOf
tails = B.tails

data OC = OC { source :: ! S
             , target :: ! S
             , hashcode :: ! Int
             , steps :: ! Int
             , size :: ! Int
             , reason :: ! Reason
             }
          deriving Show

instance Pretty OC where  pretty = pretty_with True

pretty_with full c = "Closure" <+> vcat 
    [ "source :" <+> ( pretty $ source c )
    , "target :" <+> ( pretty $ target c )
    , "steps  :" <+> ( pretty $ steps c )
    , if full then "reason :" <+> ( pretty $ reason c )
      else mempty
    ]

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

data Reason = Rule !Int | Overlap !Position !Reason !Reason
  deriving Show

instance Pretty Reason where
  pretty r = case r of
    Rule i -> "Rule" <+> pretty i
    Overlap p r1 r2 -> vcat 
      [ "Overlap" <+> pretty p 
      , " " <> vcat [ pretty r1, pretty r2 ] 
      ]

-- | kind and offset for overlap
data Position =
   Left !Int | Right !Int | Inside !Int | Outside !Int
  deriving Show

instance Pretty Position where
  pretty p = text $ show p

make r s t p = OC
  { reason = r
  , source = s
  , target = t
  , hashcode = hash (s,t)
  , steps = p
  -- note on size: this is used in the priority queue.
  -- we want small left-hand sides (sources)
  -- because they are much more likely to start a loop
  , size = ( fromIntegral $ length s)
         + ( truncate $ logBase 2 $ succ $ fromIntegral $ length t )
  }

overlap p c d s t =
  make (Overlap p (reason c) (reason d)) s t (steps c + steps d)

rule (i, (l, r)) = make (Rule i) l r 1

splits s = zip (B.inits s) (B.tails s)

assert_leq x mw = guard $ case mw of
  Just w -> x <= fromIntegral w
  Nothing -> True

lefts mw c d = do
  i <- [ 1 .. min (B.length $ target c)(B.length $ source d) ]
  assert_leq (B.length (target c) + B.length (target d) - i) mw
  let (!c1,!c2) = B.splitAt i $ target c
  let (!d1,!d2) = splitAtEnd i $ source d
  guard $ c1 == d2
  return $ overlap (Left $ fromIntegral i) c d
    (d1 <> source c) (target d <> c2) 

rights mw c d = do
  i <- [ 1 .. min (B.length $ target c)(B.length $ source d)]
  assert_leq (B.length (target c) + B.length (target d) - i) mw
  let (!c1,!c2) = splitAtEnd i $ target c
  let (!d1,!d2) = B.splitAt i $ source d
  guard $ c2 == d1
  return $ overlap (Right $ fromIntegral i) c d
    (source c <> d2) (c1 <> target d) 

splitAtEnd i s = B.splitAt (B.length s - i) s

insides mw c d = do
  assert_leq (B.length (target c) + B.length (target d) - B.length (source d)) mw  
  -- i <- [ 0 .. B.length (target c) - B.length (source d)]
  i <- indices (source d) (target c)
  let (!c1,!c2) = B.splitAt i $ target c
  let (!c21,!c22) = B.splitAt (B.length $ source d) c2
  -- guard $ c21 == source d
  return $ overlap (Inside $ fromIntegral i) c d
    (source c) (c1 <> target d <> c22) 

outsides mw c d = do
  assert_leq (B.length (target d)) mw
  i <- [ 0 .. B.length (source d) - B.length (target c)]
  let (!d1,!d2) = B.splitAt i $ source d
  let (!d21,!d22) = B.splitAt (B.length $ target c) d2
  guard $ d21 == target c
  return $ overlap (Outside $ fromIntegral i) c d
    (d1 <> source c <> d22) (target d) 

#if (TEXT || LIST)
-- Data.Text.indices cannot be used because it goes for
-- nonoverlapping occurences
indices s t = do
  i <- [ 0 .. B.length t ]
  guard $ B.isPrefixOf s $ B.drop i t
  return i
#endif
    
