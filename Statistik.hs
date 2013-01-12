import TPDB.Data
import TPDB.DP
import TPDB.Pretty
import TPDB.Plain.Write
import TPDB.Plain.Read
import TPDB.Input ( getE_trs )

import System.Environment
import System.Directory
import System.IO

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
    statss <- forM paths $ \ p -> do
        let tsize = length . subterms
        esys <- getE_trs p 
        return $ case esys of
            Right sys -> return $ Stat 
               { path = p
               , size = sum $ map tsize $ 
                    do u <- rules sys ; [lhs u, rhs u]
               , variables = maximum $ (0 : )
                    $ map (S.size . vars )
                    $ do u <- rules sys; [lhs u, rhs u]
               } 
            Left err -> []
    let stats = concat statss
        top prop = print $ take 10 
          $ sortBy ( flip compare `on` prop ) stats
    top size
    top variables

collect fs = do
    let special d = isPrefixOf "." d
    fss <- forM fs $ \ f -> do
        d <- doesDirectoryExist f
        if d 
          then do
             hPutStr stderr f
             fs <- getDirectoryContents f
             out <- collect $ map ( ( f ++ "/" ) ++ )
                     $ filter (not . special) fs
             hPutStrLn stderr $ " " ++ show (length out)
             return out
          else if isSuffixOf ".xml" f ||
                  isSuffixOf ".trs" f ||
                  isSuffixOf ".srs" f
               then return [f]
               else return []
    return $ concat fss
