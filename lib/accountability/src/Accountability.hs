-- Copyright   : (c) 2019-2022 Robert Künnemann, Kevin Morio & Yavor Ivanov
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from OpenTheories to OpenTheories with accountability lemmas

module Accountability (
       module Accountability.Generation
     , translate
) where
import Control.Monad.Catch (MonadThrow (throwM), MonadCatch)
import Theory (OpenTheory, theoryAccLemmas, caseTestToPredicate, theoryCaseTests)
import Data.Maybe (mapMaybe)
import Control.Monad (unless, foldM)
import Accountability.Generation
import Theory.Text.Parser (liftedAddLemma)
import Theory.Text.Parser.Signature (liftedAddPredicate)
import Accountability.Exceptions


------------------------------------------------------------------------------
-- Translating open theories containing accountability lemmas
------------------------------------------------------------------------------

-- | Translates the accountability lemmas in an open theory 
translate :: (Monad m, MonadThrow m, MonadCatch m) => OpenTheory -> m OpenTheory
translate thy = do
    let undef = mapMaybe undefinedCaseTests (theoryAccLemmas thy)
    unless (null undef) (throwM (CaseTestsUndefined undef :: AccException))

    let withoutFreeVars = mapMaybe containsNoFreeVar (theoryCaseTests thy)
    unless (null withoutFreeVars) (throwM (CaseTestNoFreeVar withoutFreeVars :: AccException))

    let withFreeTemps = mapMaybe containsFreeTempVar (theoryCaseTests thy)
    unless (null withFreeTemps) (throwM (CaseTestsFreeTempVar withFreeTemps :: AccException))

    accLemmas <- mapM generateAccountabilityLemmas (theoryAccLemmas thy)
    thy' <- foldM liftedAddLemma thy (concat accLemmas)
    let casePredicates = mapMaybe caseTestToPredicate (theoryCaseTests thy)
    foldM liftedAddPredicate thy' casePredicates


