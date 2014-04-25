{-# language NoMonomorphismRestriction #-}

module Compress.Common
where

import TPDB.Data
import TPDB.Pretty
import TPDB.Plain.Write ()
-- import Text.PrettyPrint.HughesPJ

import qualified Data.Set as S

import Data.Hashable 

import Control.Monad.RWS.Strict
import Data.List ( partition )

-- | Digram type
data Digram sym = Digram
     { _digram_hash :: ! Int 
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

-- | the leftmost child has this index:
position_index_start = 1

essence d = ( parent d, position d, child d )

hashed :: Hashable s => Digram s -> Digram s
hashed d = d 
    { _digram_hash = Data.Hashable.hash $! essence d }

instance Hashable sym => Hashable (Digram sym) where
    hashWithSalt s d = hashWithSalt s $ _digram_hash d

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
    deriving (Eq, Ord, Show)

instance Hashable o => Hashable (Sym o) where
    hashWithSalt s c = case c of
        Orig o -> hashWithSalt s $ hashWithSalt (0::Int) o
        Dig  d -> hashWithSalt s $ hashWithSalt (1::Int) d

smap f s = case s of
        Orig o -> Orig $ f o
        Dig  d -> Dig $ dmap (smap f) d

-- see remark on Functor Digram
-- instance Functor Sym where fmap = smap

instance Pretty o => Pretty (Sym o) where 
    pretty s = case s of
        Orig o  -> pretty o
        Dig dig -> pretty dig

-- | expand all digrams, completely
expand_all :: Term v (Sym o) -> Term v o
expand_all t = case expand_top t of
    Node (Orig o) args -> 
        Node o $ map expand_all args
    Var v -> Var v

expand_all_trs :: TRS v (Sym o) -> TRS v o
expand_all_trs sys = RS
    { rules = map (fmap expand_all) $ rules sys 
    , separate = separate sys
    }

    
-- | expand digrams until the top symbol
-- is an original symbol.
expand_top :: Term v (Sym t) -> Term v (Sym t)
expand_top t = case t of
    Node (Dig d) args -> 
        let ( pre, midpost ) = 
                splitAt (position d - position_index_start) args
            ( mid, post) = splitAt (child_arity d) midpost
        in  expand_top 
            $ Node (parent d)
            $ pre ++ [ Node (child d) mid ] ++ post
    _ -> t

-- | list of all function symbols (including nested digrams)
-- with arity
-- in dependency order (members of nested digrams occur first),
all_symbols = all_symbols_1

all_symbols_0 :: ( Ord s )
            => [ Term v (Sym s) ] 
            -> [ (Sym s, Int) ]
all_symbols_0 ts = 
    let symbol f a = do
            done <- get
            when ( S.notMember f done ) $ do
                 put $! S.insert f done
                 case f of
                     Orig o -> return ()
                     Dig d  -> do
                          symbol (parent d) (parent_arity d)
                          symbol (child  d) (child_arity  d)
                 tell $! [(f,a)]
        term t = forM_ ( subterms t ) $ \ t -> case t of 
                Var {} -> return ()
                Node f args -> do symbol f (length args) ; forM_ args term
    in  snd $ evalRWS ( forM_ ts term ) () S.empty 

-- this is rewritten to be (++) free
all_symbols_1 ts =
    let -- note: output these in dependency order (nested symbols first)
        sym (s,a) out = case s of
             Orig o -> (s,a) : out
             Dig  d -> sym (parent d, parent_arity d) 
                     $ sym (child  d, child_arity d)  
                     $ (s,a) : out
        terms ts out = case ts of
            [] -> out
            t : ts -> term t $ terms ts out
        term t out = case t of
            Node s args -> sym (s, length args) $ terms args out
            Var {} -> out
        uniq known xs = case xs of
           [] -> []
           x : xs -> if S.member x known
                     then uniq known xs
                     else x : uniq (S.insert x known) xs
    in  uniq S.empty $ terms ts []

deep_signature sys 
    = partition  ( \ s -> case s of (Orig {}, _) -> True ; _ -> False )
    $ all_symbols $ fromRules $ rules sys

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

