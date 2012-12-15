{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}

import TPDB.Data
import TPDB.DP
import TPDB.Pretty
import TPDB.Plain.Write
import TPDB.Plain.Read
import TPDB.Input ( get_trs )

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad ( forM, void )
import Prelude hiding (abs)
import System.Environment
import Text.PrettyPrint.HughesPJ
import qualified Text.Parsec
import Data.List ( sortBy )
import Data.Function (on)

for = flip map

-- * test drivers (main functions)

{- Eric:   ... Definition der Kostenfunktion eines Terms t. 
Zuerst habe ich mir überlegt, dass es eigentlich nichts anderes als
die Anzahl der inneren Knoten in Dag(t) ist, aber dann habe ich
f(g(h(x),i(x)), g(h(x),h(x)))
betrachtet. Der Dag hat zwar nur fünf Knoten, aber ich glaube man
braucht sechs Multiplikationen. Das h(x) ist einmal rechtes, einmal
linkes Kind, kann deswegen also eigentlich einmal weniger zusammengelegt
werden
-}

eric1 = run [ read_term_with_variables ["x"] "f(g(h(x),i(x)), g(h(x),h(x)))" 
           ]

-- | read TRS from file, in TPDB formats: .srs, .trs, .xtc
main = do
   [ file ] <- getArgs
   sys <- get_trs file  
   print $ pretty sys
   -- NOTE: for typical test case, should consider TPDB.DP.dp sys instead
   run $ rules sys >>= \ u -> [ lhs u, rhs u ]

-- * test helpers

run :: (Ord var, Pretty var, Ord sym, Pretty sym, Show sym)
    => [Term var sym] -> IO ()
run terms = do

   let dag = build terms
   print dag

   let terms' = unbuild dag
   -- forM terms' $ print . pretty
   when ( terms /= terms' ) $ error "decompression error"

   print $ cost_map dag
   print $ cost dag

   void $ trace_compression  dag
   
read_term_with_variables :: [ String ] -> String -> Term Identifier Identifier
read_term_with_variables vs s = 
    case Text.Parsec.parse reader "input" s of
        Right t -> pokes t $ do
            let svs = S.fromList vs
            (p, Node f []) <- positions t
            guard $ S.member (show f) svs
            return (p, Var f)

-- * the DAG data type

newtype Addr = Addr Int deriving (Eq, Ord, Enum)
instance Pretty Addr where pretty (Addr a) = pretty a
instance Show Addr where show = render . pretty

type Node var sym = Either var (sym, [Addr]) 

data DAG var sym = 
     DAG { roots :: [ Addr ]
         , table :: M.Map Addr ( Node var sym) 
         , nodes :: M.Map (Node var sym) Addr
         , digs  :: S.Set (Digram sym)
         , next :: Addr
         }

mapsym f dag = 
    let m = flip M.map (table dag) $ either Left $ \ (s, addrs) -> Right (f s, addrs)
    in  DAG { roots = roots dag
         , table = m
         , nodes = M.fromList $ do (k,v) <- M.toList m; return (v,k)
         , next  = next dag
         , digs = undefined
         }


instance ( Pretty var, Pretty sym , Show sym ) => Pretty (DAG var sym) where
    pretty d = 
        let ds = text "digrams" <+> vcat ( for (S.toList $ digs d) pretty )
            ns = text "nodes" <+> vcat ( for (M.toList $ table d) $ \ (k,v) -> 
                    pretty k <+> equals <+> case v of
                        Left v -> pretty v
                        Right (s, addrs) -> pretty s <+> hsep ( map pretty addrs ) )
            rs = text "roots" <+> hsep ( for (roots d  ) pretty )
        in  text "DAG" <+> vcat [ rs, ns, ds ]

instance ( Pretty var, Pretty sym, Show sym ) => Show (DAG var sym) where
    show = render . pretty

dag0 :: DAG var sym
dag0 =  DAG { roots = [], table = M.empty, nodes = M.empty, next = Addr 0
            , digs = S.empty } 

fold :: ( var -> a ) -> ( sym -> [a] -> a ) 
         -> DAG var sym -> M.Map Addr a
fold var sym = fold_with_addr (const var) (const sym)

fold_with_addr :: ( Addr -> var -> a ) -> ( Addr -> sym -> [a] -> a ) 
         -> DAG var sym -> M.Map Addr a
fold_with_addr var sym dag =  
    let -- only works for Data.Map, not for Data.Map.Strict ?
        m = flip M.mapWithKey (table dag) $ \ k -> \ case 
                Left v -> var k v
                Right (s, cs) -> sym k s $ map (m M.!) cs
    in  m

garbage_collect :: DAG v s -> DAG v s
garbage_collect d = 
    let successors = 
            fold_with_addr ( \ a _ -> S.singleton a )
                ( \ a s cs -> S.insert a $ S.unions cs ) d
        living = S.unions $ for (roots d) ( successors M.! )
    in  d { table = M.filterWithKey ( \ a v -> S.member a living ) $ table d 
          , nodes = M.filterWithKey ( \ v a -> S.member a living ) $ nodes d 
          }

-- * constructing DAG from terms

build :: (Ord v, Ord s) => [ Term v s ] -> DAG v s 
build ts = flip execState dag0 $ do
      addrs <- forM ts build_term
      modify $ \ d -> d { roots = addrs }

unbuild dag = 
    let m = fold Var Node dag
    in  for (roots dag) ( m  M.! )

fresh :: (Ord var, Ord sym )
      => Node var sym -> State (DAG var sym) Addr
fresh n = do
    d <- get
    put $ d { table = M.insert (next d) n $ table d 
            , nodes = M.insert n (next d) $ nodes d
            , next = succ (next d)
            }
    return $ next d

cached :: (Ord var, Ord sym )
      => Node var sym -> State (DAG var sym) Addr
cached n = do
   d <- get
   case M.lookup n $ nodes d of
       Nothing -> fresh n
       Just a  -> return a

build_term :: (Ord var, Ord sym)
           => Term var sym -> State (DAG var sym) Addr
build_term t = cached =<< case t of
    Var v -> return $ Left v
    Node s ts -> do
             addrs <- forM ts build_term
             return $ Right (s, addrs )

-- * (symbolic) linear functions

data LF sym = PROJ Int Int
        | SUB  Int sym [ LF sym ]  deriving ( Show, Eq, Ord )

-- * cost for evaluating substitutions in a dag

data Cost = 
     Cost { m_times_m :: Int
          } deriving (Eq, Ord, Show)

instance Pretty Cost where pretty = text . show

instance Num Cost where
    fromInteger i = Cost { m_times_m = fromInteger i }
    c1 + c2 = Cost { m_times_m = m_times_m c1 + m_times_m c2 
                   }

cost_map dag = M.fromList $ do
    let vars = fold ( \ v -> S.singleton v )
                    ( \ s vs -> S.unions vs )
                    dag
        arg_cost = flip M.mapWithKey (table dag) $ \ k v -> case v of
            Left _  -> 0
            Right _ -> fromIntegral $ S.size $ vars M.! k 
    (k, Right (s,addrs)) <- M.toList $ table dag
    return ( k, sum $ map (arg_cost M.!) addrs )
            
cost :: Ord var => DAG var sym -> Cost
cost dag = sum ( for (S.toList $ digs dag ) $ \ d -> fromIntegral ( child_arity d))
    + sum ( M.elems $ cost_map dag )



isLeft :: Either a b -> Bool
isLeft = either (const True) (const False )

-- * digrams

data Digram sym = Digram
     { parent :: sym
     , position :: Int
     , child :: sym
     , child_arity :: Int
     } deriving ( Eq, Ord )

instance Pretty sym => Pretty (Digram sym) where
    pretty d = parens $ hsep [ text "Digram" , pretty (parent d)
                      , pretty (position d), pretty (child d), text "Arity"
                      , pretty (child_arity d) ]

instance Pretty sym => Show (Digram sym) where
    show = render . pretty

digrams :: (Ord var, Ord sym) 
        => DAG var sym -> S.Set (Digram sym)
digrams dag = S.fromList $ do
    (k, Right (f, fargs)) <- M.toList $ table dag
    (i, a) <- zip [1..] fargs
    case table dag M.! a of
        Left _ -> []
        Right (g, gargs) -> return 
              $ Digram { parent = f, position = i, child = g
                       , child_arity = length gargs }
        
-- * replacement 

step dag = do
    dig <- S.toList $ digrams dag
    return $ replace_all dag dig 

trace_compression dag = do
    let handle (co,dag) = do
            outs <- trace_step (co,dag)
            case outs of
                (co', dag') : _ | co' < co -> handle (co', dag')
                _ -> return (co, dag)
    out <- handle (cost dag, Main.lift dag)
    putStrLn $ replicate 50 '*'
    print $ pretty out

trace_step (co, dag) = do
    putStrLn $ replicate 50 '*'
    print $ pretty dag
    print $ co
    putStrLn $ replicate 50 '*'
    let candidates = sortBy (compare `on` fst )
                   $ for (step dag) $ \ d -> (cost d, d)
    forM candidates ( print . pretty )
    return candidates
    

data Sym o = Orig o | Dig (Digram (Sym o))  
    deriving (Eq, Ord, Show)
instance Show o => Pretty (Sym o) where pretty = text . show

lift :: (Ord var, Ord o) => DAG var o -> DAG var (Sym o)
lift dag = ( mapsym Orig dag ) { digs = S.empty }


replace_all dag dig =
    let occs = nonoverlapping_occurences dag dig
        dag' = foldl (replace_at dig) dag $ S.toList occs
    in  (garbage_collect dag') { digs = S.insert dig $ digs dag' }

replace_at dig dag k = 
    let Right (f', fargs) = table dag M.! k
        (pre, this : post) = splitAt (position dig - 1) fargs
        Right (g', gargs) = table dag M.! this
    in  dag { table = M.insert k (Right (Dig dig, pre ++ gargs ++ post )) 
                    $ table dag
            , nodes = undefined
            }

nonoverlapping_occurences
  :: Eq t => DAG var t -> Digram t -> S.Set Addr
nonoverlapping_occurences dag dig = 
    let m = M.fromList $ do
            (k, Right (f, addrs)) <- M.toList $ table dag
            let a =  addrs !! (position dig - 1)
                g_ok = case  table dag M.! a of
                    Right (g, _) |  g == child dig ->  not $ m M.! a
                    _ -> False
            return ( k,  f == parent dig && g_ok )
    in  M.keysSet $ M.filter id m

