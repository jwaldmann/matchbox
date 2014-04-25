module Compress.PaperIter.Common
where

import           Control.Exception (assert)
import           Control.Monad (liftM,foldM)
import           Control.Monad.ST
import qualified Data.Set as S
import qualified Data.Map as M
import           Data.List (delete,maximumBy,union,(\\))
import           Data.STRef
import           TPDB.Data (Position,Rule,lhs,rhs)
import           TPDB.Data.Term (Term (..),vars)
import           Compress.Common (Trees(Trees),Digram)
import qualified Compress.Common as C
import           Compress.Paper.Costs (Costs(costs))

-- * Terms

data TermS s var sym = VarS var
                     | NodeS { symbol        :: sym
                             , weight        :: Int 
                             , parent        :: Maybe (TermSRef s var sym)
                             , indexOfParent :: Int
                             , children      :: [TermSRef s var sym] 
                             }

type TermSRef s var sym = STRef s (TermS s var sym)

arity :: TermS s var sym -> Int
arity termS = case termS of
  NodeS {} -> length $ children termS
  _        -> error "Compress.PaperIter.Common.arity"

fromTerm :: (Ord var) => Term var sym -> ST s (TermSRef s var sym)
fromTerm = go Nothing 0
  where
    go parent indexOfParent term = case term of
      Var v     -> newSTRef $ VarS v
      Node n ns -> do
        this <- newSTRef undefined
        ns'  <- mapM (uncurry $ go $ Just this) $ zip [0..] ns

        writeSTRef this $ NodeS n (S.size $ vars term) parent indexOfParent ns'
        return this

toTerm :: TermSRef s var sym -> ST s (Term var sym)
toTerm ref = readSTRef ref >>= \termS -> case termS of
  VarS v   -> return $ Var v
  NodeS {} -> mapM toTerm (children termS) >>= return . Node (symbol termS)

onTermS :: (TermS s var sym -> a) -> TermSRef s var sym -> ST s a
onTermS f ref = readSTRef ref >>= return . f

modifyTermS :: (TermS s var sym -> TermS s var sym) 
            -> TermSRef s var sym -> ST s ()
modifyTermS = flip modifySTRef

peekS :: TermSRef s var sym -> Position -> ST s (TermSRef s var sym)
peekS ref position = case position of
  []   -> return ref
  p:ps -> do termS <- readSTRef ref
             case termS of
                NodeS {} -> peekS (children termS !! p) ps
                _        -> error "Compression.PaperIter.Common.peekS"

varsS :: (Ord var) => TermSRef s var sym -> ST s (S.Set var)
varsS ref = readSTRef ref >>= \termS -> case termS of
  VarS v   -> return $ S.singleton v
  NodeS {} -> liftM S.unions $ mapM varsS $ children termS

-- * Digrams

data DigramData s var sym = DigramData 
                          { saving     :: Int
                          , occurences :: [TermSRef s var sym]
                          } deriving (Eq)

type DigramMap s var sym = M.Map (Digram sym) (DigramData s var sym)

instance Show (DigramData s var sym) where
  show dd = concat [ "DigramData { saving = ", show $ saving dd
                   ,            ", |occurences| = ", show $ length $ occurences dd
                   ,            "}"
                   ]

childRef :: Digram sym -> TermSRef s var sym -> ST s (TermSRef s var sym)
childRef digram ref = peekS ref [C.position digram]

digramData :: Digram sym -> [TermSRef s var sym] 
           -> ST s (DigramData s var sym)
digramData digram occs = do
  sav <- savingsOfDigram digram occs
  return $ DigramData sav occs
  where
    savingsOfDigram digram refs = do
      s <- liftM sum $ mapM (weightOfDigramAtRef digram) refs
      return $ s - (costs digram)

    weightOfDigramAtRef digram ref = childRef digram ref >>= onTermS weight

fromDigramOccurences :: (Ord sym) => [(Digram sym, TermSRef s var sym)] 
                     -> ST s [(Digram sym, DigramData s var sym)]
fromDigramOccurences = mapM mkDigramData
                     . M.toList 
                     . M.fromListWith union
                     . map (\(dig,occ) -> (dig,[occ]))
  where
    mkDigramData (digram,occs) = do
      dd <- digramData digram occs 
      return (digram,dd)

bestDigram :: (Ord sym) => DigramMap s var sym -> ( ( Digram sym
                                                    , DigramData s var sym
                                                    )
                                                  , DigramMap s var sym )
bestDigram digrams = 
  let assocs = M.toList digrams
      max    = maximumBy (\a b -> compare (saving $ snd a) (saving $ snd b)) assocs
  in
    (max, M.delete (fst max) digrams)

-- * Trees

data TreesS s var sym = TreesS { roots   :: [ Rule (TermSRef s var sym) ]
                               , extras  :: [ sym ]
                               , digrams :: DigramMap s var sym 
                               }

termRefs :: TreesS s var sym -> [TermSRef s var sym]
termRefs = concatMap (\rule -> [lhs rule, rhs rule]) . roots

fromTrees :: (Ord var) => Trees var sym -> ST s (TreesS s var sym)
fromTrees trees = do
  rs <- mapM (\rule -> do lhs' <- fromTerm $ lhs rule
                          rhs' <- fromTerm $ rhs rule
                          return $ rule { lhs = lhs'
                                        , rhs = rhs'
                                        }
             ) $ C.roots trees
  return $ TreesS rs (C.extras trees) M.empty

toTrees :: TreesS s var sym -> ST s (Trees var sym)
toTrees treesS = do
  rs <- mapM (\rule -> do lhs' <- toTerm $ lhs rule
                          rhs' <- toTerm $ rhs rule
                          return $ rule { lhs = lhs'
                                        , rhs = rhs'
                                        }
             ) $ roots treesS
  return $ Trees rs $ extras treesS

deleteOccurences :: (Ord sym) => [(Digram sym, TermSRef s var sym)]
                              -> TreesS s var sym 
                              -> ST s (TreesS s var sym)
deleteOccurences = 
  flip $ foldM (\treesS (d,ref) -> deleteOccurence ref d treesS)

deleteOccurence :: (Ord sym) => TermSRef s var sym 
                             -> Digram sym 
                             -> TreesS s var sym 
                             -> ST s (TreesS s var sym)
deleteOccurence occ dig treesS = case M.lookup dig $ digrams treesS of
  Nothing -> return treesS
  Just old -> do
    new  <- digramData dig $ delete occ $ occurences old
    return $ if null $ occurences new
             then treesS { digrams = M.delete dig     $ digrams treesS }
             else treesS { digrams = M.insert dig new $ digrams treesS }

zipRoots :: Trees var sym -> TreesS s var sym 
         -> [(Term var sym, TermSRef s var sym)]
zipRoots trees treesS = zip (C.fromRules $ C.roots trees)
                            (C.fromRules $   roots treesS)

alignDigramChainInTreesS :: (Ord sym)
                         => Digram sym -> TermSRef s var sym 
                         -> TreesS s var sym 
                         -> ST s (TreesS s var sym)
alignDigramChainInTreesS digram ref treesS = do
  digramData' <- alignDigramChain digram ref occs
  return $ treesS { digrams = M.insert digram digramData' $ digrams treesS }
  where
    occs = case M.lookup digram $ digrams treesS of
              Just d -> occurences d
              _      -> []

alignDigramChain :: (Eq sym)
                 => Digram sym -> TermSRef s var sym -> [TermSRef s var sym] 
                 -> ST s (DigramData s var sym)
alignDigramChain digram digramRef occs = assert (C.isOverlappable digram) $ do
  topOcc            <- getTopOccurence digramRef
  chainOccs         <- collectOccurences topOcc [] 
  let nonOverlapping = dropOdds chainOccs
      occs'          = nonOverlapping ++ (occs \\ chainOccs)

  digramData digram occs'
  where
    getTopOccurence ref = do
      f <- readSTRef ref
      case parent f of
        Just pRef | indexOfParent f == C.position digram -> do
          p <- readSTRef pRef
          if symbol p == C.parent digram
            then getTopOccurence pRef
            else return ref

        _ -> return ref


    collectOccurences ref occs = do
      f <- readSTRef ref
      if C.position digram < length (children f)
        then do
          gRef <- childRef digram ref 
          g    <- readSTRef gRef
          case g of
            NodeS {} | symbol g == C.child digram -> 
              collectOccurences gRef $ occs ++ [ref]
            _ -> return occs
        else return occs

    dropOdds (x:_:zs) = x : (dropOdds zs)
    dropOdds zs       = zs
