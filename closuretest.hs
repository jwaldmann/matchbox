import qualified  MB.Closure.Option as O
import MB.Closure.Enumerate

import TPDB.Plain.Write
import TPDB.Plain.Read
import TPDB.Pretty (pretty)
import TPDB.Data

import Control.Monad ( forM_ )

main = O.main_with >>= workf

workf conf = do
  s <- readFile $ O.problem conf
  case srs s of
    Left err -> error err
    Right t -> work conf t

work conf sys = do
  let rules = fromSRS sys
      cs = enumerate (O.directions conf) (O.width conf)
                     ( fromSRS sys )
  print conf    
  putStrLn $ "original: " ++ show (pretty sys)
  putStrLn $ "renamed : " ++ show rules
  mapM_ print $ take 1 $ do
    c <- cs
    loop_certificates c ++
      if O.cyclic conf then cycle_loop_certificates c else [] 


