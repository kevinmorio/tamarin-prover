-- |
-- DeepSec backend entry point.
module Export.DeepSec (prettyDeepSecTheory) where

import Export.ProVerif qualified as ProVerif
import Export.Types
import Theory (OpenTheory)

prettyDeepSecTheory :: Int -> OpenTheory -> IO (Either ExportError ExportResult)
prettyDeepSecTheory = ProVerif.prettyDeepSecTheory

