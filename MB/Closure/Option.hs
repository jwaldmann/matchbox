module MB.Closure.Option

where

import Options.Applicative
import Prelude hiding (Either (..))

data Directions = Left | Both | Right
  deriving (Eq, Ord, Show, Enum, Bounded)

data Config =
  Config { cyclic :: Bool
         , directions :: Directions
         , width :: Maybe Int
         , problem :: FilePath
         }
  deriving Show

opts = info (helper <*> config)
   ( fullDesc
     <> progDesc "enumerate forward closures for (cycle) nontermination"
   )

config = Config
  <$> switch ( long "cyclic" <> short 'c' )
  <*> (     flag Right Left ( long "left" <> short 'l' )
        <|> flag Right Right ( long "right" <> short 'r' )
        <|> flag Right Both ( long "both" <> short 'b' )
      )
  <*> option (Just <$> auto) 
      ( long "width" <> short 'w' <> value Nothing )
  <*> strArgument
    ( help "file name (containing SRS in ASCII syntax)"
      <> metavar "FILE"
    )

main_with = execParser opts
