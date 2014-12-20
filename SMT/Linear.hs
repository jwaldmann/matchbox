module SMT.Linear where

import qualified SMT.Dictionary as D
import qualified SMT.Matrix as M
import qualified SMT.Semiring as S

import Control.Monad ( forM )
import Data.List ( transpose )

import Prelude hiding ( abs )

data Linear a = 
     Linear { dim :: (Int,Int)
            , abs :: a , lin :: [a] 
            }
   deriving Show

to = fst . dim ; from = snd . dim

data Dictionary m num val bool =
     Dictionary { domain :: D.Domain
                , make :: Int -> (Int,Int) 
                      -> m (Linear num)
                , decode :: 
                    Linear num -> m (Linear val) 
                , substitute ::
                      Linear num -> [Linear num]
                      -> m (Linear num)
                , weakly_monotone :: 
                      Linear num -> m bool
                , strictly_monotone :: 
                      Linear num -> m bool
                , positive :: 
                      Linear num -> m bool
                , weakly_greater :: Linear num 
                      -> Linear num -> m bool 
                , strictly_greater :: Linear num 
                      -> Linear num -> m bool 
                , and :: [ bool ] -> m bool
                , assert :: [ bool ] -> m ()
                , bconstant :: Bool -> m bool
                } 

linear :: Monad m
       => M.Dictionary m num val bool
       -> Dictionary m (M.Matrix num) (M.Matrix val) bool
linear d = Dictionary
    { domain = M.domain d
    , make = \ ar (to, from) -> do
        ms <- forM [ 1 .. ar ] $ \ i -> 
            M.make d (to,from)
        a <- M.make d (to, 1)
        return $ Linear { dim=(to,from)
                        , abs = a, lin = ms }
    , decode = \ f -> do
        a <- M.decode d $ abs f
        ls <- forM (lin f) $ M.decode d 
        return $ Linear { dim = dim f
                        , abs = a, lin = ls }
    , substitute = \ f gs -> do
        as <- strictZipWithM "sub.1"
             (M.times d) (lin f) (map abs gs)
        a <- M.bfoldM (M.add d) $ abs f : as
        ls <- forM (transpose $ map lin gs) 
            $ \ ms -> do
                out <- strictZipWithM "sub.2"
                      (M.times d) (lin f) ms
                M.bfoldM (M.add d) out
        return $ Linear 
               { dim = (to f, case gs of
                   [] -> error "missing .from in substitute"
                   g : _ -> from g )
               , abs = a, lin = ls
               }   
    , positive = \ f -> case M.domain d of
        D.Int -> do
            ms <- forM ( lin f ) $ M.positive d
            M.and d ms
        D.Arctic -> do
            a <- M.positive d $ abs f
            ms <- forM ( lin f ) $ M.positive d
            M.or d $ a : ms
{-
    , strictly_monotone = \ f -> do
        ms <- forM ( lin f ) $ M.strictly_monotone d
        M.and d ms
    , weakly_monotone = \ f -> do
        ms <- forM ( lin f ) $ M.weakly_monotone d
        M.and d ms
-}
    , strictly_greater = \ f g -> case M.domain d of
        D.Int -> do
          a <- M.strictly_greater d (abs f) (abs g)
          ls <- strictZipWithM "strictly_greater.Int"
              (M.weakly_greater d) (lin f) (lin g)
          M.and d $ a : ls
        D.Arctic -> do
          ls <- strictZipWithM "strictly_greater.Arctic"
           (M.strictly_greater d) 
                    (abs f : lin f) (abs g : lin g)
          M.and d $ ls
      , weakly_greater = \ f g -> do
          ls <- strictZipWithM "weakly_greater"
             (M.weakly_greater d) 
                    (abs f : lin f) (abs g : lin g)
          M.and d $ ls

    , SMT.Linear.and = M.and d
    , SMT.Linear.assert = M.assert d
    , SMT.Linear.bconstant = M.bconstant d

    }

strictZipWithM msg f xs ys = 
    if length xs /= length ys 
    then error $ unwords [ "strictZipWithM", msg
                         , show (length xs,length ys)
                         ]
    else zipWithM f xs ys
    
zipWithM f xs ys = case (xs,ys) of
    (x:xs, y:ys) -> do
        zs <- zipWithM f xs ys
        z <- f x y
        return $ z : zs
    _ -> return []
