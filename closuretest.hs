import qualified  MB.Closure.Option as O
import MB.Closure.Enumerate

import TPDB.Plain.Write
import TPDB.Plain.Read
import TPDB.Pretty (pretty)
import TPDB.Data
import TPDB.Input (get_srs)
import TPDB.Pretty (pretty)

import Control.Monad ( forM_ )

main = O.main_with >>= workf

workf conf = do
  s <- get_srs $ O.problem conf
  work conf s

work conf sys = do
  let rules = fromSRS sys
      cs = enumerate (O.directions conf) (O.width conf)
                     ( fromSRS sys )
  print conf    
  putStrLn $ "original: " ++ show (pretty sys)
  putStrLn $ "renamed : " ++ show rules
  
  let certs = do
        c <- cs
        loop_certificates c ++
          if O.cyclic conf 
          then cycle_loop_certificates c 
          else []
               
  mapM_ (print . pretty) $ take 1 $ certs


