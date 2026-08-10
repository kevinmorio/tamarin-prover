-- |
-- Explicit semantic outcomes and prepared values for ProVerif properties.
module Export.ProVerif.Property
  ( PreparedFormula (..),
    PreparedAxiomProperty (..),
    PropertyOutcome (..),
  )
where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Theory (LNFormula)

data PreparedFormula = PreparedFormula
  { preparedFormula :: LNFormula,
    preparedTimeOrigins :: Map.Map String String,
    preparedHadTimepointSplit :: Bool
  }

data PreparedAxiomProperty = PreparedAxiomProperty
  { preparedAxiomBeforeCompletion :: [LNFormula],
    preparedAxiomFormulas :: [PreparedFormula],
    preparedAxiomCompletionTriggers :: Set.Set String
  }

data PropertyOutcome a
  = PropertyEmitted a
  | PropertyOmitted String
  | PropertyExcluded

