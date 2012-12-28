import TPDB.Data
import TPDB.DP
import TPDB.Pretty
import TPDB.Plain.Write
import TPDB.Plain.Read
import TPDB.Input ( get_trs )

import System.Environment
import System.Directory

import qualified Data.Set as S
import Data.Function ( on )
import Data.List ( sortBy, isSuffixOf, isPrefixOf )
import Control.Monad ( forM )

data Stat = Stat 
          { path :: FilePath
          , size :: Int
          , variables :: Int
          }
    deriving Show       

main = do
    tops <- getArgs
    paths <- collect tops
    stats <- forM paths $ \ p -> do
        sys <- get_trs p
        let tsize = length . subterms
        return $ Stat 
               { path = p
               , size = sum $ map tsize $ 
                    do u <- rules sys ; [lhs u, rhs u]
               , variables = maximum 
                    $ map (S.size . vars )
                    $ do u <- rules sys; [lhs u, rhs u]
               }                                   
    print $ take 10 
          $ sortBy ( compare `on` size ) stats

collect fs = do
    let special d = isPrefixOf "." d
    fss <- forM fs $ \ f -> do
        d <- doesDirectoryExist f
        if d 
        then do
           fs <- getDirectoryContents f
           collect $ map ( ( f ++ "/" ) ++ )
                   $ filter (not . special) fs
        else if isSuffixOf ".xml" f ||
                isSuffixOf ".trs" f ||
                isSuffixOf ".srs" f
             then return [f]
             else return []
    return $ concat fss
