module Compress.PaperIter.TreeRePair
where

import           Control.Monad (liftM,foldM,forM_)
import           Control.Monad.ST
import           Data.List (delete)
import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Maybe (catMaybes)
import           Data.STRef
import           TPDB.Pretty (Pretty)
import           Compress.Common (Trees,Sym(Dig),terms,position)
import qualified Compress.Common as C
import           Compress.PaperIter.Common
import           Compress.Paper.Digram (allDigrams,nonOverlappingOccurences)
import           Debug.Trace (traceShow)

-- |Runs tree re-pair algorithm 
treeRePair :: (Ord var, Ord sym
              , Pretty sym, Pretty var, Show sym, Show var {- delete this -}) 
           => Trees var (Sym sym) -> Trees var (Sym sym)
treeRePair trees = runST $ initialize trees >>= step >>= toTrees

initialize :: (Ord var, Ord sym) 
           => Trees var (Sym sym) -> ST s (TreesS s var (Sym sym))
initialize trees = do
  treesS <- fromTrees trees
  ds     <- mkDigramMap treesS
  return $ treesS { digrams = ds }

  where 
    mkDigramMap treesS = do
      datas <- mapM (mkDigramData treesS) $ S.toList $ allDigrams $ terms trees
      return $ M.fromList datas

    mkDigramData treesS digram = do 
      occs <- liftM concat $ mapM (mkOccurences digram) $ zipRoots trees treesS
      dd   <- digramData digram occs
      return (digram,dd)

    mkOccurences digram (term, termSRef) = mapM (peekS termSRef) occurencesInTerm
      where
        occurencesInTerm = nonOverlappingOccurences digram term

step :: (Ord sym, Pretty sym, Pretty var, Show sym, Show var {- delete this -}) 
     => TreesS s var (Sym sym) -> ST s (TreesS s var (Sym sym))
step treesS = traceShow (M.toList $ digrams treesS) $ do
  trees <- toTrees treesS
  traceShow (trees) $ 
    if M.null (digrams treesS) || saving digramData <= 0 
       then return treesS
       else traceShow digram (replaceByDigram treesS' digram digramData >>= step)
  where 
    ((digram, digramData), digrams') = bestDigram $ digrams treesS
    treesS'                          = treesS { digrams = digrams' }

replaceByDigram :: (Ord sym
                    , Pretty sym, Pretty var, Show sym, Show var {- delete this -}) 
                => TreesS s var (Sym sym) -> C.Digram (Sym sym) 
                -> DigramData s var (Sym sym) 
                -> ST s (TreesS s var (Sym sym))
replaceByDigram treesS digram digramData = do
  -- 1. Retrive all digram occurences that should be deleted
  occsToDelete <- liftM concat $ mapM deleteOverlappingDigrams occs

  -- 2. Delete them
  treesS' <- deleteOccurences occsToDelete treesS 

  -- 3. Replace @digram@ at all its occurences
  mapM_ replaceAtOccurence occs

  -- 4. Align all digram chains
  treesS'' <- foldM (flip alignDigramChains) treesS' occs

  -- 5. Retrieve all new digrams
  newDigrams     <- liftM concat $ mapM getNewDigrams occs
  newDigramDatas <- fromDigramOccurences newDigrams

  -- 6. Add @digram@ to extras and update digram map
  return $ treesS'' { extras  = (Dig digram) : extras treesS''
                    , digrams = digrams treesS'' `M.union` (M.fromList newDigramDatas)
                    }
  where
    occs = occurences digramData

    -- |Deletes all occurences of overlapping digrams
    deleteOverlappingDigrams ref = 
      liftM concat $ mapM (\f -> f ref) [ deleteOverlappingParentDigram       
                                        , deleteOverlappingNeighbourDigrams   
                                        , deleteOverlappingChildrenDigrams   
                                        ]

    -- |Replaces @digram@ at @ref@
    replaceAtOccurence ref = do
      f <- readSTRef ref
      g <- childRef digram ref >>= readSTRef

      let fs                  = children f
          gs                  = children g
          (preFs, _ : postFs) = splitAt (position digram) fs

          newChildren         = preFs ++ gs ++ postFs
          newNode             = f { symbol   = Dig digram
                                  , children = newChildren
                                  }
      
      writeSTRef ref newNode

      forM_ (zip [0..] newChildren) $ \(i,childRef) ->
        modifyTermS (\termS -> case termS of
                        NodeS {} -> termS { parent        = Just ref 
                                          , indexOfParent = i
                                          }
                        _        -> termS
                    ) childRef

    -- |Aligns all digram chains that either contain @ref@ or one of its subterms.
    -- This adds new overlappable digrams to @treesS@ that were not present before.
    -- Therefor @getNewDigrams@ must not retrieve them again.
    alignDigramChains ref treesS = alignDigramChainsAt ref treesS 
                               >>= alignChildrenDigramChains ref 

    -- |Retrieves all new (non-overlappable) digrams
    getNewDigrams ref = do 
      newParentDigram <- getParentDigram ref 
      newDigrams      <- liftM (map $ \d -> (d,ref)) $ getAllDigrams ref
      return $ filter (not . C.isOverlappable . fst)
             $ (maybe [] return newParentDigram) ++ newDigrams

    -- |Deletes the occurences of all digrams that overlap the parent of the currently
    -- replaced digram @digram@ with their child.
    deleteOverlappingParentDigram ref = do
      parentDigram <- getParentDigram ref 
      case parentDigram of
        Just (pDig,pRef) | pDig /= digram -> return [(pDig,pRef)]
        _                                 -> return []

    -- |Deletes the occurences of all digrams that overlap the parent of the currently
    -- replaced digram @digram@ with their parent.
    deleteOverlappingNeighbourDigrams ref = do
      f <- readSTRef ref
      liftM concat $ mapM (deleteDigramOccurence ref) 
                   $ delete (C.position digram) [ 0 .. (length $ children f) - 1 ]

    -- |Deletes the occurences of all digrams that overlap the child of the currently
    -- replaced digram @digram@.
    deleteOverlappingChildrenDigrams ref = do
      gRef <- childRef digram ref
      g    <- readSTRef gRef
      liftM concat $ mapM (deleteDigramOccurence gRef) [ 0 .. (length $ children g) - 1 ]

    -- |Deletes the occurence of digram (@ref@, @i@, @i@-th subterm of @ref@)
    deleteDigramOccurence ref i = do
      mD <- getDigram ref i 
      case mD of
        Just d | d /= digram -> return [(d,ref)]
        _                    -> return []

    -- |Aligns all digram chains that contain a subterm of @ref@ 
    alignChildrenDigramChains ref treesS = do
      f    <- readSTRef ref
      foldM (flip alignDigramChainsAt) treesS $ children f

    -- |Aligns all digram chains that contain @ref@
    alignDigramChainsAt ref treesS = do
      start <- readSTRef ref
      case start of
        VarS  {} -> return treesS
        NodeS {} -> foldM (flip $ alignDigramChainAt ref) treesS 
                          [ 0 .. (length $ children start) - 1 ]

    -- |Aligns a digram chain that contains the digram (@ref@, @j@, @j@-th subterm of @ref@)
    -- in @treesS@.
    -- Does nothing if this digram is not overlappable.
    alignDigramChainAt ref j treesS = do
      childDigram <- getDigram ref j 
      case childDigram of
        Just cDig | C.isOverlappable cDig -> alignDigramChainInTreesS cDig ref treesS
        _                                 -> return treesS

    -- |Returns the digram with @ref@ as child.
    -- Returns nothing if @ref@ has no parent term.
    getParentDigram ref = do
      f <- readSTRef ref
      case parent f of
        Nothing   -> return Nothing
        Just pRef -> do
          p <- readSTRef pRef
          return $ Just ( C.Digram (symbol p) (arity p) (indexOfParent f)
                                   (symbol f) (arity f)
                        , pRef )

    -- |Returns the digram with @ref@ as parent and its @i@-th subterm as child.
    -- Returns nothing if
    -- 1. parent or child is a variable or
    -- 2. the term at @ref@ has no @i@-th subterm
    getDigram ref i = do
      f    <- readSTRef ref
      case f of
        VarS  {} -> return Nothing
        NodeS {} -> 
          if i >= length (children f)
          then return Nothing
          else do
            g <- peekS ref [i] >>= readSTRef
            return $ case g of
              VarS  {} -> Nothing
              NodeS {} -> Just $ C.Digram (symbol f) (arity f) i (symbol g) (arity g)

    -- |Returns all digrams with @ref@ as parent
    getAllDigrams ref = do
      f <- readSTRef ref
      liftM catMaybes $ mapM (getDigram ref) [ 0 .. (length $ children f) - 1 ]
