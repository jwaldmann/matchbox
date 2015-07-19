import MB.Closure.Enumerate
import System.Environment

import TPDB.Plain.Write
import TPDB.Plain.Read
import TPDB.Pretty (pretty)
import TPDB.Data

import Control.Monad ( forM_ )
import Options.Applicative

data Config =
  Config { cycling :: Bool
         , problem :: FilePath
         }
  deriving Show

opts = info (helper <*> config)
   ( fullDesc
     <> progDesc "enumerate forward closures for (cycle) nontermination"
   )

config = Config
  <$> switch ( long "cyclic" <> short 'c' )
  <*> strArgument
    ( help "file name (containing SRS in ASCII syntax)"
      <> metavar "FILE"
    )

main_with = execParser opts

main = main_with >>= workf

workf conf = do
  s <- readFile $ problem conf
  case srs s of
    Left err -> error err
    Right t -> work conf t

work conf sys = do
  let rules = fromSRS sys
      cs = enumerate_fcs ( fromSRS sys )
  print conf    
  putStrLn $ "original: " ++ show (pretty sys)
  putStrLn $ "renamed : " ++ show rules
  mapM_ print $ take 1 $ do
    c <- cs
    loop_certificates c ++
      if cycling conf then cycle_loop_certificates c else [] 


