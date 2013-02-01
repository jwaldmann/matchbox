{-# language DeriveGeneric #-}

module Compress.Common
where

import TPDB.Data
import TPDB.Pretty
import TPDB.Plain.Write ()
import Text.PrettyPrint.HughesPJ

import qualified Data.Set as S

import Data.Hashable 
import GHC.Generics

-- | Digram type
data Digram sym = Digram
     { _digram_hash :: Int 
   -- ^ NOTE: this value comes first
   -- in order to speed up the derived Eq and Ord
   -- instances. For this to work properly,
   -- @hashed@ must be applied to each Digram
   -- after construction
     , parent       :: ! sym
     , parent_arity :: ! Int
     , position     :: ! Int
     , child        :: ! sym
     , child_arity  :: ! Int
     } deriving ( Eq, Ord )

essence d = ( parent d, position d, child d )

hashed :: Hashable s => Digram s -> Digram s
hashed d = d 
    { _digram_hash = Data.Hashable.hash $! essence d }

instance Hashable sym => Hashable (Digram sym) where
    hashWithSalt s d = hash (s, _digram_hash d)

dmap f d = hashed
             $ d { parent = f $ parent d
                 , child  = f $ child  d
                 }

-- | URGH: we must call "hashable" here, but we can't
-- (because of the "Hashable" constraint)
-- instance Functor Digram where fmap = dmap

instance Pretty sym => Pretty (Digram sym) where
    pretty d = brackets $ hcat [ pretty (parent d)
             , text "/", pretty (position d)
             , text "/", pretty (child d)
             , text ".", pretty (child_arity d) 
             -- just for debugging the hashing:
             -- , text "#", pretty (_digram_hash d)
             ]

instance Pretty sym => Show (Digram sym) where
    show = render . pretty

isOverlappable :: (Eq sym) => Digram sym -> Bool
isOverlappable dig = parent dig == child dig

-- | Type for storing a set (list) of rules (rule is pair of trees)
data Trees var sym = 
     Trees { roots  :: [ Rule ( Term var sym ) ]
           , extras :: [ sym ]
         }
    deriving ( Eq, Ord )

instance ( Pretty var, Pretty sym ) => Pretty (Trees var sym) where
   pretty ts = vcat  
     [ text "roots:"  <+> vcat (map pretty $ roots ts)
     , text "extras:" <+> vcat (map pretty $ extras ts) 
     ]

instance ( Pretty var, Pretty sym, Show sym ) 
       => Show (Trees var sym) where
    show = render . pretty

-- | Returns all terms of all trees
terms :: Trees var sym -> [Term var sym]
terms = fromRules . roots

-- | Cost type
data Cost = Cost { m_times_m :: Int } deriving (Eq, Ord, Show)

instance Pretty Cost where pretty = text . show

instance Num Cost where
    fromInteger i = Cost { m_times_m = fromInteger i }
    c1 + c2       = Cost { m_times_m = m_times_m c1 + m_times_m c2 }
    _ * _         = error "Can not multiply costs"
    abs _         = error "Can not apply 'abs' to costs"
    signum _      = error "Can not apply 'signum' to costs"

-- | Symbol type
data Sym o = Orig o | Dig (Digram (Sym o))  
    deriving (Eq, Ord, Show, Generic)

instance Hashable o => Hashable (Sym o) where
    hashWithSalt s c = case c of
        Orig o -> hashWithSalt s $ hashWithSalt (0::Int) o
        Dig  d -> hashWithSalt s $ hashWithSalt (1::Int) d

-- see remark on Functor Digram
-- instance Functor Sym where fmap = smap
smap f s = case s of
        Orig o -> Orig $ f o
        Dig  d -> Dig $ dmap (smap f) d

instance Pretty o => Pretty (Sym o) where 
    pretty s = case s of
        Orig o  -> pretty o
        Dig dig -> pretty dig

-- * Utilities

instance Functor Rule where
  fmap f u = u { lhs = f $ lhs u, rhs = f $ rhs u }


-- | Returns left/right-hand sides of a list of rules
fromRules :: [Rule a] -> [a]
fromRules = concatMap (\rule -> [lhs rule, rhs rule])

-- | Lifts trees' functions symbols to @Sym@
lift :: (Ord var, Ord o) => Trees var o -> Trees var (Sym o)
lift trees = 
    Trees { roots  = map (fmap (fmap Orig)) $ roots trees 
          , extras = [] 
          }

-- | Constructing trees from terms
build :: (Ord v, Ord s) => [ Rule (Term v s) ] -> Trees v s 
build ts = Trees { roots = ts, extras = [] }

