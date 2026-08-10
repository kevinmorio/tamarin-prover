-- |
-- Explicit semantic outcomes and prepared values for ProVerif properties.
module Export.ProVerif.Property
  ( PreparedFormula (..),
    QueryPolarity (..),
    QueryRecombination (..),
    PreparedQueryFormula (..),
    PreparedQueryProperty (..),
    PreparedAxiomProperty (..),
    PreparedRestrictionProperty (..),
    PropertyOutcome (..),
  )
where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Theory (LNFormula)

data QueryPolarity
  = DirectResult
  | InvertResult
  deriving (Eq, Ord, Show)

data QueryRecombination
  = ConjoinQueryResults
  | DisjoinQueryResults
  deriving (Eq, Ord, Show)

data PreparedQueryFormula = PreparedQueryFormula
  { preparedQueryBody :: PreparedFormula,
    preparedQueryPolarity :: QueryPolarity,
    preparedQueryUseOriginRuleIds :: Bool
  }

data PreparedQueryProperty = PreparedQueryProperty
  { preparedQueryFormulas :: [PreparedQueryFormula],
    preparedQueryRecombination :: Maybe QueryRecombination,
    preparedQueryCompletionTriggers :: Set.Set String
  }

data PreparedFormula = PreparedFormula
  { preparedFormula :: LNFormula,
    preparedTimeOrigins :: Map.Map String String,
    preparedHadTimepointSplit :: Bool,
    preparedRuleIdNames :: Map.Map String String
  }

data PreparedAxiomProperty = PreparedAxiomProperty
  { preparedAxiomFormulas :: [PreparedFormula],
    preparedAxiomCompletionTriggers :: Set.Set String,
    preparedAxiomApproximation :: Maybe String
  }

data PreparedRestrictionProperty = PreparedRestrictionProperty
  { preparedRestrictionFormulas :: [PreparedFormula],
    preparedRestrictionWasRewritten :: Bool,
    preparedRestrictionApproximation :: Maybe String
  }

data PropertyOutcome a
  = PropertyEmitted a
  | PropertyOmitted String
  | PropertyExcluded
