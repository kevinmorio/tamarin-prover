-- |
-- Aggregated instrumentation consumed by both property and rule rendering.
module Export.ProVerif.Instrumentation
  ( InstrumentationPlan (..),
    instrumentationPropertyEvents,
  )
where

import Data.Set qualified as Set

data InstrumentationPlan = InstrumentationPlan
  { instrumentationCompletionEvent :: String,
    instrumentationRuleIdEvents :: Set.Set String,
    instrumentationCompletionTriggers :: Set.Set String
  }
  deriving (Eq, Show)

instrumentationPropertyEvents :: InstrumentationPlan -> Set.Set String
instrumentationPropertyEvents plan
  | Set.null plan.instrumentationCompletionTriggers = plan.instrumentationRuleIdEvents
  | otherwise =
      Set.insert plan.instrumentationCompletionEvent plan.instrumentationRuleIdEvents

