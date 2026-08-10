-- |
-- Backend-neutral SAPIC export context shared by target renderers.
module Export.Sapic
  ( Translation (..),
    TranslationContext (..),
    emptyTC,
    emptyTypeEnv,
    exportModule,
  )
where

import Data.Data (Data, Typeable)
import Data.Map.Strict qualified as Map
import Sapic.Typing (TypingEnvironment (..))
import Theory (LVar, Predicate)
import Theory.Module (ModuleType (..))

data Translation
  = ProVerif
  | DeepSec
  deriving (Ord, Eq, Typeable, Data)

exportModule :: Translation -> ModuleType
exportModule ProVerif = ModuleProVerif
exportModule DeepSec = ModuleDeepSec

data TranslationContext = TranslationContext
  { trans :: Translation,
    attackerChannel :: Maybe LVar,
    hasBoundStates :: Bool,
    hasUnboundStates :: Bool,
    predicates :: [Predicate],
    replicationBound :: Int,
    skipReuseLemmas :: Bool,
    skipSourceLemmas :: Bool,
    skipRestrictions :: Bool,
    skipPrecise :: Bool
  }
  deriving (Eq, Ord)

emptyTC :: TranslationContext
emptyTC =
  TranslationContext
    { trans = ProVerif,
      attackerChannel = Nothing,
      hasBoundStates = False,
      hasUnboundStates = False,
      predicates = [],
      replicationBound = 3,
      skipReuseLemmas = False,
      skipSourceLemmas = False,
      skipRestrictions = False,
      skipPrecise = False
    }

emptyTypeEnv :: TypingEnvironment
emptyTypeEnv = TypingEnvironment {vars = Map.empty, events = Map.empty, funs = Map.empty}
