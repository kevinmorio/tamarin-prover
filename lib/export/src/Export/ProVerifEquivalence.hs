-- |
-- ProVerif observational-equivalence backend entry point.
module Export.ProVerifEquivalence (prettyProVerifEquivTheory) where

import Export.ProVerif qualified as ProVerif
import Export.Types
import Sapic.Typing (TypingEnvironment)
import Theory (OpenTheory)

prettyProVerifEquivTheory ::
  (OpenTheory, TypingEnvironment) ->
  IO (Either ExportError ExportResult)
prettyProVerifEquivTheory = ProVerif.prettyProVerifEquivTheory

