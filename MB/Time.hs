module MB.Time where

import Data.Time ( getCurrentTime, diffUTCTime )
import qualified Data.Time.Clock as C
import TPDB.Pretty

data Time = Time { start :: C.UTCTime , end :: C.UTCTime }

instance Pretty Time where
  pretty t = text "found in"
            <+> (text $ show $ C.diffUTCTime (end t) (start t) )
            <+> text "from" <+> (text $ show $ start t)
            <+> text "to"   <+> (text $ show $ end   t)

