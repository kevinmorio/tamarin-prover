{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- FIXME: for functions prove
{-# LANGUAGE FlexibleContexts     #-}
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Simon Meier <iridcode@gmail.com>
-- Portability : GHC only
--
-- Theory datatype and transformations on it.
module Theory (
  -- * Axioms
    Axiom(..)
  , AxiomAttribute(..)
  , axName
  , axFormula

  -- * Lemmas
  , LemmaAttribute(..)
  , TraceQuantifier(..)
  , Lemma
  , lName
  , DiffLemma
  , lDiffName
  , lDiffProof
  , lTraceQuantifier
  , lFormula
  , lAttributes
  , lProof
  , unprovenLemma
  , skeletonLemma
  , skeletonDiffLemma
  , isLeftLemma
  , isRightLemma
--   , isBothLemma
  , addLeftLemma
  , addRightLemma

  -- * Theories
  , Theory(..)
  , DiffTheory(..)
  , TheoryItem(..)
  , DiffTheoryItem(..)
  , thyName
  , thySignature
  , thyCache
  , thyItems
  , diffThyName
  , diffThySignature
  , diffThyCacheLeft
  , diffThyCacheRight
  , diffThyDiffCacheLeft
  , diffThyDiffCacheRight
  , diffThyItems
  , diffTheoryLemmas
  , diffTheorySideLemmas
  , diffTheoryDiffRules
  , diffTheoryDiffLemmas
  , theoryRules
  , theoryLemmas
  , theoryAxioms
  , diffTheoryAxioms
  , diffTheorySideAxioms
  , addAxiom
  , addLemma
  , addAxiomDiff
  , addLemmaDiff
  , addDiffLemma
  , removeLemma
  , removeLemmaDiff
  , removeDiffLemma
  , lookupLemma
  , lookupDiffLemma
  , lookupLemmaDiff
  , addComment
  , addDiffComment
  , addStringComment
  , addFormalComment
  , addFormalCommentDiff
  , cprRuleE
  , filterSide
  , addDefaultDiffLemma
  , addProtoRuleLabels
  , removeProtoRuleLabels
  , addIntrRuleLabels

  -- ** Open theories
  , OpenTheory
  , OpenDiffTheory
--  , EitherTheory
  , EitherOpenTheory
  , EitherClosedTheory
  , defaultOpenTheory
  , defaultOpenDiffTheory
  , addProtoRule
  , addProtoDiffRule
  , applyPartialEvaluation
  , applyPartialEvaluationDiff
  , addIntrRuleACs
  , addIntrRuleACsDiffBoth
  , addIntrRuleACsDiffLeft
  , addIntrRuleACsDiffRight
  , normalizeTheory

  -- ** Closed theories
  , ClosedTheory
  , ClosedDiffTheory
  , ClosedRuleCache(..) -- FIXME: this is only exported for the Binary instances
  , closeTheory
  , closeDiffTheory
  , openTheory
  , openDiffTheory

  , ClosedProtoRule(..)

  , getLemmas
  , getDiffLemmas
  , getIntrVariants
  , getProtoRuleEs
  , getProtoRuleEsDiff
  , getProofContext
  , getProofContextDiff
  , getDiffProofContext
  , getClassifiedRules
  , getDiffClassifiedRules
  , getInjectiveFactInsts
  , getDiffInjectiveFactInsts

  , getCaseDistinction
  , getDiffCaseDistinction

  -- ** Proving
  , ProofSkeleton
  , DiffProofSkeleton
  , proveTheory
  , proveDiffTheory

  -- ** Lemma references
  , lookupLemmaProof
  , modifyLemmaProof
  , lookupLemmaProofDiff
  , modifyLemmaProofDiff
  , lookupDiffLemmaProof
  , modifyDiffLemmaProof
  
  -- * Pretty printing
  , prettyFormalComment
  , prettyLemmaName
  , prettyAxiom
  , prettyLemma
  , prettyDiffLemmaName
  , prettyClosedTheory
  , prettyClosedDiffTheory
  , prettyOpenTheory
  , prettyOpenDiffTheory

  , prettyClosedSummary
  , prettyClosedDiffSummary

  , prettyIntruderVariants
  , prettyTraceQuantifier

  -- * Convenience exports
  , module Theory.Model
  , module Theory.Proof
--   , module Theory.Constraint.Solver.Types

  ) where

-- import           Debug.Trace

import           Prelude                             hiding (id, (.))

import           Data.Binary
import           Data.DeriveTH
import           Data.Foldable                       (Foldable, foldMap)
import           Data.List
import           Data.Maybe
import           Data.Monoid                         (Sum(..))
import qualified Data.Set                            as S
import           Data.Traversable                    (Traversable, traverse)

import           Control.Basics
import           Control.Category
import           Control.DeepSeq
import           Control.Monad.Reader
import qualified Control.Monad.State                 as MS
import           Control.Parallel.Strategies

import           Extension.Data.Label                hiding (get)
import qualified Extension.Data.Label                as L

import           Theory.Model
import           Theory.Proof
import           Theory.Text.Pretty
import           Theory.Tools.AbstractInterpretation
import           Theory.Tools.InjectiveFactInstances
import           Theory.Tools.LoopBreakers
import           Theory.Tools.RuleVariants
-- import           Theory.Constraint.Solver.Types

------------------------------------------------------------------------------
-- Specific proof types
------------------------------------------------------------------------------

-- | Proof skeletons are used to represent proofs in open theories.
type ProofSkeleton    = Proof ()

-- | Convert a proof skeleton to an incremental proof without any sequent
-- annotations.
skeletonToIncrementalProof :: ProofSkeleton -> IncrementalProof
skeletonToIncrementalProof = fmap (fmap (const Nothing))

-- | Convert an incremental proof to a proof skeleton by dropping all
-- annotations.
incrementalToSkeletonProof :: IncrementalProof -> ProofSkeleton
incrementalToSkeletonProof = fmap (fmap (const ()))

-- | Proof skeletons are used to represent proofs in open theories.
type DiffProofSkeleton    = DiffProof ()

-- | Convert a proof skeleton to an incremental proof without any sequent
-- annotations.
skeletonToIncrementalDiffProof :: DiffProofSkeleton -> IncrementalDiffProof
skeletonToIncrementalDiffProof = fmap (fmap (const Nothing))

-- | Convert an incremental proof to a proof skeleton by dropping all
-- annotations.
incrementalToSkeletonDiffProof :: IncrementalDiffProof -> DiffProofSkeleton
incrementalToSkeletonDiffProof = fmap (fmap (const ()))

------------------------------------------------------------------------------
-- Commented sets of rewriting rules
------------------------------------------------------------------------------

-- | A protocol rewriting rule modulo E together with its possible assertion
-- soundness proof.
type OpenProtoRule = ProtoRuleE

-- | A closed proto rule lists its original rule modulo E, the corresponding
-- variant modulo AC, and if required the assertion soundness proof.
data ClosedProtoRule = ClosedProtoRule
       { _cprRuleE  :: ProtoRuleE             -- original rule modulo E
       , _cprRuleAC :: ProtoRuleAC            -- variant modulo AC
       }
       deriving( Eq, Ord, Show )

type OpenRuleCache = [IntrRuleAC]

data ClosedRuleCache = ClosedRuleCache
       { _crcRules            :: ClassifiedRules
       , _crcUntypedCaseDists :: [CaseDistinction]
       , _crcTypedCaseDists   :: [CaseDistinction]
       , _crcInjectiveFactInsts  :: S.Set FactTag
       }
       deriving( Eq, Ord, Show )


$(mkLabels [''ClosedProtoRule, ''ClosedRuleCache])

instance HasRuleName ClosedProtoRule where
    ruleName = ruleName . L.get cprRuleE


-- Relation between open and closed rule sets
---------------------------------------------

-- | All intruder rules of a set of classified rules.
intruderRules :: ClassifiedRules -> [IntrRuleAC]
intruderRules rules = do
    Rule (IntrInfo i) ps cs as <- joinAllRules rules
    return $ Rule i ps cs as

-- | Open a rule cache. Variants and precomputed case distinctions are dropped.
openRuleCache :: ClosedRuleCache -> OpenRuleCache
openRuleCache = intruderRules . L.get crcRules

-- | Open a protocol rule; i.e., drop variants and proof annotations.
openProtoRule :: ClosedProtoRule -> OpenProtoRule
openProtoRule = L.get cprRuleE

-- | Close a protocol rule; i.e., compute AC variant and typing assertion
-- soundness sequent, if required.
closeProtoRule :: MaudeHandle -> OpenProtoRule -> ClosedProtoRule
closeProtoRule hnd ruE = ClosedProtoRule ruE (variantsProtoRule hnd ruE)

-- | Close a rule cache. Hower, note that the
-- requires case distinctions are not computed here.
closeRuleCache :: [LNGuarded]        -- ^ Axioms to use.
               -> [LNGuarded]        -- ^ Typing lemmas to use.
               -> SignatureWithMaude -- ^ Signature of theory.
               -> [ClosedProtoRule]  -- ^ Protocol rules with variants.
               -> OpenRuleCache      -- ^ Intruder rules modulo AC.
               -> Bool               -- ^ Diff or not
               -> ClosedRuleCache    -- ^ Cached rules and case distinctions.
closeRuleCache axioms typAsms sig protoRules intrRulesAC isdiff = -- trace ("closeRuleCache: " ++ show classifiedRules) $
    ClosedRuleCache
        classifiedRules untypedCaseDists typedCaseDists injFactInstances
  where
    ctxt0 = ProofContext
        sig classifiedRules injFactInstances UntypedCaseDist [] AvoidInduction
        (error "closeRuleCache: trace quantifier should not matter here") isdiff

    -- inj fact instances
    injFactInstances =
        simpleInjectiveFactInstances $ L.get cprRuleE <$> protoRules

    -- precomputing the case distinctions: we make sure to only add safety
    -- axioms. Otherwise, it wouldn't be sound to use the precomputed case
    -- distinctions for properties proven using induction.
    safetyAxioms     = filter isSafetyFormula axioms
    untypedCaseDists = precomputeCaseDistinctions ctxt0 safetyAxioms
    typedCaseDists   = refineWithTypingAsms typAsms ctxt0 untypedCaseDists

    -- classifying the rules
    rulesAC = (fmap IntrInfo                      <$> intrRulesAC) <|>
              ((fmap ProtoInfo . L.get cprRuleAC) <$> protoRules)

    anyOf ps = partition (\x -> any ($ x) ps)

    (nonProto, proto) = anyOf [isDestrRule, isConstrRule] rulesAC
    (constr, destr)   = anyOf [isConstrRule] nonProto

    -- and sort them into ClassifiedRules datastructure for later use in proofs
    classifiedRules = ClassifiedRules
      { _crConstruct  = constr
      , _crDestruct   = destr
      , _crProtocol   = proto
      }


------------------------------------------------------------------------------
-- Axioms (Trace filters)
------------------------------------------------------------------------------

-- | An attribute for a 'Axiom'.
data AxiomAttribute =
         LHSAxiom
       | RHSAxiom
       | BothAxiom
       deriving( Eq, Ord, Show )

-- | An axiom describes a property that must hold for all traces. Axioms are
-- always used as lemmas in proofs.
data Axiom = Axiom
       { _axName    :: String
       , _axFormula :: LNFormula
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''Axiom])


------------------------------------------------------------------------------
-- Lemmas
------------------------------------------------------------------------------

-- | An attribute for a 'Lemma'.
data LemmaAttribute =
         TypingLemma
       | ReuseLemma
       | InvariantLemma
       | LHSLemma
       | RHSLemma
--        | BothLemma
       deriving( Eq, Ord, Show )

-- | A 'TraceQuantifier' stating whether we check satisfiability of validity.
data TraceQuantifier = ExistsTrace | AllTraces
       deriving( Eq, Ord, Show )

-- | A lemma describes a property that holds in the context of a theory
-- together with a proof of its correctness.
data Lemma p = Lemma
       { _lName            :: String
       , _lTraceQuantifier :: TraceQuantifier
       , _lFormula         :: LNFormula
       , _lAttributes      :: [LemmaAttribute]
       , _lProof           :: p
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''Lemma])

-- | A diff lemma describes a correspondence property that holds in the context of a theory
-- together with a proof of its correctness.
data DiffLemma p = DiffLemma
       { _lDiffName            :: String
--        , _lTraceQuantifier :: TraceQuantifier
--        , _lFormula         :: LNFormula
--        , _lAttributes      :: [LemmaAttribute]
       , _lDiffProof           :: p
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''DiffLemma])

-- Instances
------------

instance Functor Lemma where
    fmap f (Lemma n qua fm atts prf) = Lemma n qua fm atts (f prf)

instance Foldable Lemma where
    foldMap f = f . L.get lProof

instance Traversable Lemma where
    traverse f (Lemma n qua fm atts prf) = Lemma n qua fm atts <$> f prf

instance Functor DiffLemma where
    fmap f (DiffLemma n prf) = DiffLemma n (f prf)

instance Foldable DiffLemma where
    foldMap f = f . L.get lDiffProof

instance Traversable DiffLemma where
    traverse f (DiffLemma n prf) = DiffLemma n <$> f prf

-- Lemma queries
----------------------------------

-- | Convert a trace quantifier to a sequent trace quantifier.
toSystemTraceQuantifier :: TraceQuantifier -> SystemTraceQuantifier
toSystemTraceQuantifier AllTraces   = ExistsNoTrace
toSystemTraceQuantifier ExistsTrace = ExistsSomeTrace

-- | True iff the lemma can be used as a typing lemma.
isTypingLemma :: Lemma p -> Bool
isTypingLemma lem =
     (AllTraces == L.get lTraceQuantifier lem)
  && (TypingLemma `elem` L.get lAttributes lem)

-- | True iff the lemma is a LHS lemma.
isLeftLemma :: Lemma p -> Bool
isLeftLemma lem =
     (LHSLemma `elem` L.get lAttributes lem)

-- | True iff the lemma is a RHS lemma.
isRightLemma :: Lemma p -> Bool
isRightLemma lem =
     (RHSLemma `elem` L.get lAttributes lem)

-- -- | True iff the lemma is a Both lemma.
-- isBothLemma :: Lemma p -> Bool
-- isBothLemma lem =
--      (BothLemma `elem` L.get lAttributes lem)

-- Lemma construction/modification
----------------------------------

-- | Create a new unproven lemma from a formula modulo E.
unprovenLemma :: String -> [LemmaAttribute] -> TraceQuantifier -> LNFormula
              -> Lemma ProofSkeleton
unprovenLemma name atts qua fm = Lemma name qua fm atts (unproven ())

skeletonLemma :: String -> [LemmaAttribute] -> TraceQuantifier -> LNFormula
              -> ProofSkeleton -> Lemma ProofSkeleton
skeletonLemma name atts qua fm = Lemma name qua fm atts

-- | Create a new unproven diff lemma.
unprovenDiffLemma :: String
              -> DiffLemma DiffProofSkeleton
unprovenDiffLemma name = DiffLemma name (diffUnproven ())

skeletonDiffLemma :: String -> DiffProofSkeleton -> DiffLemma DiffProofSkeleton
skeletonDiffLemma name = DiffLemma name


-- | The case-distinction kind allowed for a lemma
lemmaCaseDistKind :: Lemma p -> CaseDistKind
lemmaCaseDistKind lem
  | TypingLemma `elem` L.get lAttributes lem = UntypedCaseDist
  | otherwise                                = TypedCaseDist

-- | Adds the LHS lemma attribute.
addLeftLemma :: Lemma p -> Lemma p
addLeftLemma lem =
     L.set lAttributes (LHSLemma:(L.get lAttributes lem)) lem

-- | Adds the RHS lemma attribute.
addRightLemma :: Lemma p -> Lemma p
addRightLemma lem =
     L.set lAttributes (RHSLemma:(L.get lAttributes lem)) lem

------------------------------------------------------------------------------
-- Theories
------------------------------------------------------------------------------

-- | A formal comment is a header together with the body of the comment.
type FormalComment = (String, String)

-- | A theory item built over the given rule type.
data TheoryItem r p =
       RuleItem r
     | LemmaItem (Lemma p)
     | AxiomItem Axiom
     | TextItem FormalComment
     deriving( Show, Eq, Ord, Functor )

-- | A diff theory item built over the given rule type.
--   This includes
--   - Diff Rules, which are then decomposed in either rules for both sides
--   - the Diff Lemmas, stating observational equivalence
--   - the either lemmas and axioms, statung properties about either side
--   - and comments
data DiffTheoryItem r r2 p p2 =
       DiffRuleItem r
     | EitherRuleItem (Side, r2)
     | DiffLemmaItem (DiffLemma p)
     | EitherLemmaItem (Side, Lemma p2)
     | EitherAxiomItem (Side, Axiom)
     | DiffTextItem FormalComment
     deriving( Show, Eq, Ord, Functor )

-- | A theory contains a single set of rewriting rules modeling a protocol
-- and the lemmas that
data Theory sig c r p = Theory {
         _thyName      :: String
       , _thySignature :: sig
       , _thyCache     :: c
       , _thyItems     :: [TheoryItem r p]
       }
       deriving( Eq, Ord, Show )

$(mkLabels [''Theory])

       
-- | A diff theory contains a set of rewriting rules with diff modeling two instances
data DiffTheory sig c r r2 p p2 = DiffTheory {
         _diffThyName           :: String
       , _diffThySignature      :: sig
       , _diffThyCacheLeft      :: c
       , _diffThyCacheRight     :: c
       , _diffThyDiffCacheLeft  :: c
       , _diffThyDiffCacheRight :: c
       , _diffThyItems          :: [DiffTheoryItem r r2 p p2]
       }
       deriving( Eq, Ord, Show )

       
$(mkLabels [''DiffTheory])

-- | Open theories can be extended. Invariants:
--   1. Lemma names are unique.
type OpenTheory =
    Theory SignaturePure [IntrRuleAC] OpenProtoRule ProofSkeleton

-- | Open diff theories can be extended. Invariants:
--   1. Lemma names are unique.
type OpenDiffTheory =
    DiffTheory SignaturePure [IntrRuleAC] OpenProtoRule OpenProtoRule DiffProofSkeleton ProofSkeleton
    
-- | Closed theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedTheory =
    Theory SignatureWithMaude ClosedRuleCache ClosedProtoRule IncrementalProof

-- | Closed Diff theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedDiffTheory =
    DiffTheory SignatureWithMaude ClosedRuleCache OpenProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof

-- | Either Therories can be Either a normal or a diff theory

-- type EitherTheory = Either Theory  DiffTheory
type EitherOpenTheory = Either OpenTheory OpenDiffTheory
type EitherClosedTheory = Either ClosedTheory ClosedDiffTheory

type OpenDiffTheoryItem =
    DiffTheoryItem OpenProtoRule OpenProtoRule DiffProofSkeleton ProofSkeleton


-- Shared theory modification functions
---------------------------------------


filterSide :: Side -> [(Side, a)] -> [a]
filterSide s l = case l of
                    x:xs -> if (fst x) == s then (snd x):(filterSide s xs) else (filterSide s xs)
                    []   -> []

-- | Fold a theory item.
foldTheoryItem
    :: (r -> a) -> (Axiom -> a) -> (Lemma p -> a) -> (FormalComment -> a)
    -> TheoryItem r p -> a
foldTheoryItem fRule fAxiom fLemma fText i = case i of
    RuleItem ru   -> fRule ru
    LemmaItem lem -> fLemma lem
    TextItem txt  -> fText txt
    AxiomItem ax  -> fAxiom ax
    
-- | Fold a theory item.
foldDiffTheoryItem
    :: (r -> a) -> ((Side, r2) -> a) -> (DiffLemma p -> a) -> ((Side, Lemma p2) -> a) -> ((Side, Axiom) -> a) -> (FormalComment -> a)
    -> DiffTheoryItem r r2 p p2 -> a
foldDiffTheoryItem fDiffRule fEitherRule fDiffLemma fEitherLemma fAxiom fText i = case i of
    DiffRuleItem ru   -> fDiffRule ru
    EitherRuleItem (side, ru) -> fEitherRule (side, ru)
    DiffLemmaItem lem -> fDiffLemma lem
    EitherLemmaItem (side, lem) -> fEitherLemma (side, lem)
    EitherAxiomItem (side, ax)  -> fAxiom (side, ax)
    DiffTextItem txt  -> fText txt

-- | Map a theory item.
mapTheoryItem :: (r -> r') -> (p -> p') -> TheoryItem r p -> TheoryItem r' p'
mapTheoryItem f g =
    foldTheoryItem (RuleItem . f) AxiomItem (LemmaItem . fmap g) TextItem

-- | Map a diff theory item.
mapDiffTheoryItem :: (r -> r') -> ((Side, r2) -> (Side, r2')) -> (DiffLemma p -> DiffLemma p') -> ((Side, Lemma p2) -> (Side, Lemma p2')) -> DiffTheoryItem r r2 p p2 -> DiffTheoryItem r' r2' p' p2'
mapDiffTheoryItem f g h i =
    foldDiffTheoryItem (DiffRuleItem . f) (EitherRuleItem . g) (DiffLemmaItem . h) (EitherLemmaItem . i) EitherAxiomItem DiffTextItem

-- | All rules of a theory.
theoryRules :: Theory sig c r p -> [r]
theoryRules =
    foldTheoryItem return (const []) (const []) (const []) <=< L.get thyItems

-- | All diff rules of a theory.
diffTheoryDiffRules :: DiffTheory sig c r r2 p p2 -> [r]
diffTheoryDiffRules =
    foldDiffTheoryItem return (const []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All rules of a theory.
diffTheorySideRules :: Side -> DiffTheory sig c r r2 p p2 -> [r2]
diffTheorySideRules s =
    foldDiffTheoryItem (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All left rules of a theory.
leftTheoryRules :: DiffTheory sig c r r2 p p2 -> [r2]
leftTheoryRules =
    foldDiffTheoryItem (const []) (\(x, y) -> if (x == LHS) then [y] else []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

-- | All right rules of a theory.
rightTheoryRules :: DiffTheory sig c r r2 p p2 -> [r2]
rightTheoryRules =
    foldDiffTheoryItem (const []) (\(x, y) -> if (x == RHS) then [y] else []) (const []) (const []) (const []) (const []) <=< L.get diffThyItems

    
-- | All axioms of a theory.
theoryAxioms :: Theory sig c r p -> [Axiom]
theoryAxioms =
    foldTheoryItem (const []) return (const []) (const []) <=< L.get thyItems

-- | All lemmas of a theory.
theoryLemmas :: Theory sig c r p -> [Lemma p]
theoryLemmas =
    foldTheoryItem (const []) (const []) return (const []) <=< L.get thyItems

-- | All axioms of a theory.
diffTheoryAxioms :: DiffTheory sig c r r2 p p2 -> [(Side, Axiom)]
diffTheoryAxioms =
    foldDiffTheoryItem (const []) (const []) (const []) (const []) return (const []) <=< L.get diffThyItems

-- | All axioms of one side of a theory.
diffTheorySideAxioms :: Side -> DiffTheory sig c r r2 p p2 -> [Axiom]
diffTheorySideAxioms s =
    foldDiffTheoryItem (const []) (const []) (const []) (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheoryLemmas :: DiffTheory sig c r r2 p p2 -> [(Side, Lemma p2)]
diffTheoryLemmas =
   foldDiffTheoryItem (const []) (const []) (const []) return (const []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheorySideLemmas :: Side -> DiffTheory sig c r r2 p p2 -> [Lemma p2]
diffTheorySideLemmas s =
    foldDiffTheoryItem (const []) (const []) (const []) (\(x, y) -> if (x == s) then [y] else []) (const []) (const []) <=< L.get diffThyItems

-- | All lemmas of a theory.
diffTheoryDiffLemmas :: DiffTheory sig c r r2 p p2 -> [DiffLemma p]
diffTheoryDiffLemmas =
    foldDiffTheoryItem (const []) (const []) return (const []) (const []) (const []) <=< L.get diffThyItems

    -- | Add a new axiom. Fails, if axiom with the same name exists.
addAxiom :: Axiom -> Theory sig c r p -> Maybe (Theory sig c r p)
addAxiom l thy = do
    guard (isNothing $ lookupAxiom (L.get axName l) thy)
    return $ modify thyItems (++ [AxiomItem l]) thy

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addLemma :: Lemma p -> Theory sig c r p -> Maybe (Theory sig c r p)
addLemma l thy = do
    guard (isNothing $ lookupLemma (L.get lName l) thy)
    return $ modify thyItems (++ [LemmaItem l]) thy

-- | Add a new axiom. Fails, if axiom with the same name exists.
addAxiomDiff :: Side -> Axiom -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addAxiomDiff s l thy = do
    guard (isNothing $ lookupAxiomDiff s (L.get axName l) thy)
    return $ modify diffThyItems (++ [EitherAxiomItem (s, l)]) thy

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addLemmaDiff :: Side -> Lemma p2 -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addLemmaDiff s l thy = do
    guard (isNothing $ lookupLemmaDiff s (L.get lName l) thy)
    return $ modify diffThyItems (++ [EitherLemmaItem (s, l)]) thy

-- | Add a new lemma. Fails, if a lemma with the same name exists.
addDiffLemma :: DiffLemma p -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
addDiffLemma l thy = do
    guard (isNothing $ lookupDiffLemma (L.get lDiffName l) thy)
    return $ modify diffThyItems (++ [DiffLemmaItem l]) thy
    
-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemma :: String -> Theory sig c r p -> Maybe (Theory sig c r p)
removeLemma lemmaName thy = do
    _ <- lookupLemma lemmaName thy
    return $ modify thyItems (concatMap fItem) thy
  where
    fItem   = foldTheoryItem (return . RuleItem)
                             (return . AxiomItem)
                             check
                             (return . TextItem)
    check l = do guard (L.get lName l /= lemmaName); return (LemmaItem l)

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeLemmaDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
removeLemmaDiff s lemmaName thy = do
    _ <- lookupLemmaDiff s lemmaName thy
    return $ modify diffThyItems (concatMap fItem) thy
  where
    fItem   = foldDiffTheoryItem (return . DiffRuleItem)
                                 (return . EitherRuleItem)
                                 (return . DiffLemmaItem)
                                 check
                                 (return . EitherAxiomItem)
                                 (return . DiffTextItem)
    check (s', l) = do guard (L.get lName l /= lemmaName || s'/=s); return (EitherLemmaItem (s, l))

-- | Remove a lemma by name. Fails, if the lemma does not exist.
removeDiffLemma :: String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffTheory sig c r r2 p p2)
removeDiffLemma lemmaName thy = do
    _ <- lookupDiffLemma lemmaName thy
    return $ modify diffThyItems (concatMap fItem) thy
  where
    fItem   = foldDiffTheoryItem (return . DiffRuleItem)
                                 (return . EitherRuleItem)
                                 check
                                 (return . EitherLemmaItem)
                                 (return . EitherAxiomItem)
                                 (return . DiffTextItem)
    check l = do guard (L.get lDiffName l /= lemmaName); return (DiffLemmaItem l)

-- | Find the axiom with the given name.
lookupAxiom :: String -> Theory sig c r p -> Maybe Axiom
lookupAxiom name = find ((name ==) . L.get axName) . theoryAxioms

-- | Find the lemma with the given name.
lookupLemma :: String -> Theory sig c r p -> Maybe (Lemma p)
lookupLemma name = find ((name ==) . L.get lName) . theoryLemmas

-- | Find the axiom with the given name.
lookupAxiomDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe Axiom
lookupAxiomDiff s name = find ((name ==) . L.get axName) . (diffTheorySideAxioms s)

-- | Find the lemma with the given name.
lookupLemmaDiff :: Side -> String -> DiffTheory sig c r r2 p p2 -> Maybe (Lemma p2)
lookupLemmaDiff s name = find ((name ==) . L.get lName) . (diffTheorySideLemmas s)

-- | Find the lemma with the given name.
lookupDiffLemma :: String -> DiffTheory sig c r r2 p p2 -> Maybe (DiffLemma p)
lookupDiffLemma name = find ((name ==) . L.get lDiffName) . diffTheoryDiffLemmas

-- | Add a comment to the theory.
addComment :: Doc -> Theory sig c r p -> Theory sig c r p
addComment c = modify thyItems (++ [TextItem ("", render c)])

-- | Add a comment to the diff theory.
addDiffComment :: Doc -> DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
addDiffComment c = modify diffThyItems (++ [DiffTextItem ("", render c)])

-- | Add a comment represented as a string to the theory.
addStringComment :: String -> Theory sig c r p -> Theory sig c r p
addStringComment = addComment . vcat . map text . lines

addFormalComment :: FormalComment -> Theory sig c r p -> Theory sig c r p
addFormalComment c = modify thyItems (++ [TextItem c])

addFormalCommentDiff :: FormalComment -> DiffTheory sig c r r2 p p2 -> DiffTheory sig c r r2 p p2
addFormalCommentDiff c = modify diffThyItems (++ [DiffTextItem c])


------------------------------------------------------------------------------
-- Open theory construction / modification
------------------------------------------------------------------------------

-- | Default theory
defaultOpenTheory :: Bool -> OpenTheory
defaultOpenTheory flag = Theory "default" (emptySignaturePure flag) [] []

-- | Default diff theory
defaultOpenDiffTheory :: Bool -> OpenDiffTheory
defaultOpenDiffTheory flag = DiffTheory "default" (emptySignaturePure flag) [] [] [] [] []

-- Add the default Diff lemma to an Open Diff Theory
addDefaultDiffLemma:: OpenDiffTheory -> OpenDiffTheory
addDefaultDiffLemma thy = fromMaybe thy $ addDiffLemma (unprovenDiffLemma "Observational_equivalence") thy

-- Add the rule labels to an Open Diff Theory
addProtoRuleLabels:: OpenDiffTheory -> OpenDiffTheory
addProtoRuleLabels thy =
    modify diffThyItems (map addRuleLabel) thy
  where
    addRuleLabel :: OpenDiffTheoryItem -> OpenDiffTheoryItem
    addRuleLabel (DiffRuleItem rule) = DiffRuleItem $ addDiffLabel rule ("DiffProto" ++ (getRuleName rule))
    addRuleLabel x                   = x
    
-- Add the rule labels to an Open Diff Theory
addIntrRuleLabels:: OpenDiffTheory -> OpenDiffTheory
addIntrRuleLabels thy =
    modify diffThyCacheLeft (map addRuleLabel) $ modify diffThyDiffCacheLeft (map addRuleLabel) $ modify diffThyDiffCacheRight (map addRuleLabel) $ modify diffThyCacheRight (map addRuleLabel) thy
  where
    addRuleLabel :: IntrRuleAC -> IntrRuleAC
    addRuleLabel rule = addDiffLabel rule ("DiffIntr" ++ (getRuleName rule))

-- Add the rule labels to an Open Diff Theory
removeProtoRuleLabels:: OpenDiffTheory -> OpenDiffTheory
removeProtoRuleLabels thy =
    modify diffThyItems (map removeRuleLabel) thy
  where
    removeRuleLabel :: OpenDiffTheoryItem -> OpenDiffTheoryItem
    removeRuleLabel (DiffRuleItem rule) = DiffRuleItem $ removeDiffLabel rule ("DiffProto" ++ (getRuleName rule))
    removeRuleLabel x                   = x

    
-- | Open a theory by dropping the closed world assumption and values whose
-- soundness dependens on it.
openTheory :: ClosedTheory -> OpenTheory
openTheory  (Theory n sig c items) =
    Theory n (toSignaturePure sig) (openRuleCache c)
      (map (mapTheoryItem openProtoRule incrementalToSkeletonProof) items)

-- | Open a theory by dropping the closed world assumption and values whose
-- soundness dependens on it.
openDiffTheory :: ClosedDiffTheory -> OpenDiffTheory
openDiffTheory  (DiffTheory n sig c1 c2 c3 c4 items) =
    DiffTheory n (toSignaturePure sig) (openRuleCache c1) (openRuleCache c2) (openRuleCache c3) (openRuleCache c4)
      (map (mapDiffTheoryItem id (\(x, y) -> (x, (openProtoRule y))) (\(DiffLemma s p) -> (DiffLemma s (incrementalToSkeletonDiffProof p))) (\(x, Lemma a b c d e) -> (x, Lemma a b c d (incrementalToSkeletonProof e)))) items)

      
-- | Find the open protocol rule with the given name.
lookupOpenProtoRule :: ProtoRuleName -> OpenTheory -> Maybe OpenProtoRule
lookupOpenProtoRule name =
    find ((name ==) . L.get rInfo) . theoryRules

-- | Find the open protocol rule with the given name.
-- REMOVE
-- lookupOpenDiffProtoRule :: Side -> ProtoRuleName -> OpenDiffTheory -> Maybe OpenProtoRule
-- lookupOpenDiffProtoRule s name =
--     find ((name ==) . L.get rInfo) . (diffTheorySideRules s)

-- | Find the open protocol rule with the given name.
lookupOpenDiffProtoDiffRule :: ProtoRuleName -> OpenDiffTheory -> Maybe OpenProtoRule
lookupOpenDiffProtoDiffRule name =
    find ((name ==) . L.get rInfo) . diffTheoryDiffRules

-- | Add a new protocol rules. Fails, if a protocol rule with the same name
-- exists.
addProtoRule :: ProtoRuleE -> OpenTheory -> Maybe OpenTheory
addProtoRule ruE thy = do
    guard nameNotUsedForDifferentRule
    return $ modify thyItems (++ [RuleItem ruE]) thy
  where
    nameNotUsedForDifferentRule =
        maybe True ((ruE ==)) $ lookupOpenProtoRule (L.get rInfo ruE) thy

-- | Add a new protocol rules. Fails, if a protocol rule with the same name
-- exists.
addProtoDiffRule :: ProtoRuleE -> OpenDiffTheory -> Maybe OpenDiffTheory
addProtoDiffRule ruE thy = do
    guard nameNotUsedForDifferentRule
    return $ modify diffThyItems (++ [DiffRuleItem ruE]) thy
  where
    nameNotUsedForDifferentRule =
        maybe True ((ruE ==)) $ lookupOpenDiffProtoDiffRule (L.get rInfo ruE) thy

-- | Add intruder proof rules.
addIntrRuleACs :: [IntrRuleAC] -> OpenTheory -> OpenTheory
addIntrRuleACs rs' = modify (thyCache) (\rs -> nub $ rs ++ rs')

-- | Add intruder proof rules.
addIntrRuleACsDiffBoth :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffBoth rs' thy = addIntrRuleACsDiffRight rs' (addIntrRuleACsDiffLeft rs' thy)

-- | Add intruder proof rules.
addIntrRuleACsDiffLeft :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffLeft rs' thy = modify (diffThyDiffCacheLeft) (\rs -> nub $ rs ++ rs') $ modify (diffThyCacheLeft) (\rs -> nub $ rs ++ rs') thy

-- | Add intruder proof rules.
addIntrRuleACsDiffRight :: [IntrRuleAC] -> OpenDiffTheory -> OpenDiffTheory
addIntrRuleACsDiffRight rs' thy = modify (diffThyDiffCacheRight) (\rs -> nub $ rs ++ rs') $ modify (diffThyCacheRight) (\rs -> nub $ rs ++ rs') thy

-- | Normalize the theory representation such that they remain semantically
-- equivalent. Use this function when you want to compare two theories (quite
-- strictly) for semantic equality; e.g., when testing the parser.
normalizeTheory :: OpenTheory -> OpenTheory
normalizeTheory =
    L.modify thyCache sort
  . L.modify thyItems (\items -> do
      item <- items
      return $ case item of
          LemmaItem lem ->
              LemmaItem $ L.modify lProof stripProofAnnotations $ lem
          RuleItem _    -> item
          TextItem _    -> item
          AxiomItem _   -> item)
  where
    stripProofAnnotations :: ProofSkeleton -> ProofSkeleton
    stripProofAnnotations = fmap stripProofStepAnnotations
    stripProofStepAnnotations (ProofStep method ()) =
        ProofStep (case method of
                     Sorry _         -> Sorry Nothing
                     Contradiction _ -> Contradiction Nothing
                     _               -> method)
                  ()


------------------------------------------------------------------------------
-- Closed theory querying / construction / modification
------------------------------------------------------------------------------

-- querying
-----------

-- | All lemmas.
getLemmas :: ClosedTheory -> [Lemma IncrementalProof]
getLemmas = theoryLemmas

-- | All diff lemmas.
getDiffLemmas :: ClosedDiffTheory -> [DiffLemma IncrementalDiffProof]
getDiffLemmas = diffTheoryDiffLemmas

-- | All side lemmas.
-- REMOVE
-- getEitherLemmas :: ClosedDiffTheory -> [(Side, Lemma IncrementalProof)]
-- getEitherLemmas = diffTheoryLemmas

-- | The variants of the intruder rules.
getIntrVariants :: ClosedTheory -> [IntrRuleAC]
getIntrVariants = intruderRules . L.get (crcRules . thyCache)

-- | All protocol rules modulo E.
getProtoRuleEs :: ClosedTheory -> [ProtoRuleE]
getProtoRuleEs = map openProtoRule . theoryRules

-- | All protocol rules modulo E.
getProtoRuleEsDiff :: Side -> ClosedDiffTheory -> [ProtoRuleE]
getProtoRuleEsDiff s = map openProtoRule . (diffTheorySideRules s)

-- | Get the proof context for a lemma of the closed theory.
getProofContext :: Lemma a -> ClosedTheory -> ProofContext
getProofContext l thy = ProofContext
    ( L.get thySignature                    thy)
    ( L.get (crcRules . thyCache)           thy)
    ( L.get (crcInjectiveFactInsts . thyCache) thy)
    kind
    ( L.get (cases . thyCache)              thy)
    inductionHint
    (toSystemTraceQuantifier $ L.get lTraceQuantifier l)
    False
  where
    kind    = lemmaCaseDistKind l
    cases   = case kind of UntypedCaseDist -> crcUntypedCaseDists
                           TypedCaseDist   -> crcTypedCaseDists
    inductionHint
      | any (`elem` [TypingLemma, InvariantLemma]) (L.get lAttributes l) = UseInduction
      | otherwise                                                        = AvoidInduction

-- | Get the proof context for a lemma of the closed theory.
getProofContextDiff :: Side -> Lemma a -> ClosedDiffTheory -> ProofContext
getProofContextDiff s l thy = case s of
  LHS -> ProofContext
            ( L.get diffThySignature                    thy)
            ( L.get (crcRules . diffThyCacheLeft)           thy)
            ( L.get (crcInjectiveFactInsts . diffThyCacheLeft) thy)
            kind
            ( L.get (cases . diffThyCacheLeft)              thy)
            inductionHint
            (toSystemTraceQuantifier $ L.get lTraceQuantifier l)
            False
  RHS -> ProofContext
            ( L.get diffThySignature                    thy)
            ( L.get (crcRules . diffThyCacheRight)           thy)
            ( L.get (crcInjectiveFactInsts . diffThyCacheRight) thy)
            kind
            ( L.get (cases . diffThyCacheRight)              thy)
            inductionHint
            (toSystemTraceQuantifier $ L.get lTraceQuantifier l)
            False
  where
    kind    = lemmaCaseDistKind l
    cases   = case kind of UntypedCaseDist -> crcUntypedCaseDists
                           TypedCaseDist   -> crcTypedCaseDists
    inductionHint
      | any (`elem` [TypingLemma, InvariantLemma]) (L.get lAttributes l) = UseInduction
      | otherwise                                                        = AvoidInduction

-- | Get the proof context for a diff lemma of the closed theory.
getDiffProofContext :: DiffLemma a -> ClosedDiffTheory -> DiffProofContext
getDiffProofContext _ thy = DiffProofContext (proofContext LHS) (proofContext RHS) (diffTheoryDiffRules thy) (L.get (crConstruct . crcRules . diffThyDiffCacheLeft) thy) (L.get (crDestruct . crcRules . diffThyDiffCacheLeft) thy) ((LHS, axiomsLeft):[(RHS, axiomsRight)])
  where
    items = L.get diffThyItems thy
    axiomsLeft  = do EitherAxiomItem (LHS, ax) <- items
                     return $ formulaToGuarded_ $ L.get axFormula ax
    axiomsRight  = do EitherAxiomItem (RHS, ax) <- items
                      return $ formulaToGuarded_ $ L.get axFormula ax
    proofContext s = case s of
        LHS -> ProofContext
            ( L.get diffThySignature                    thy)
            ( L.get (crcRules . diffThyDiffCacheLeft)           thy)
            ( L.get (crcInjectiveFactInsts . diffThyDiffCacheLeft) thy)
            TypedCaseDist
            ( L.get (crcTypedCaseDists . diffThyDiffCacheLeft)              thy)
            AvoidInduction
            ExistsNoTrace
            True
        RHS -> ProofContext
            ( L.get diffThySignature                    thy)
            ( L.get (crcRules . diffThyDiffCacheRight)           thy)
            ( L.get (crcInjectiveFactInsts . diffThyDiffCacheRight) thy)
            TypedCaseDist
            ( L.get (crcTypedCaseDists . diffThyDiffCacheRight)              thy)
            AvoidInduction
            ExistsNoTrace
            True

-- | The facts with injective instances in this theory
getInjectiveFactInsts :: ClosedTheory -> S.Set FactTag
getInjectiveFactInsts = L.get (crcInjectiveFactInsts . thyCache)

-- | The facts with injective instances in this theory
getDiffInjectiveFactInsts :: Side -> Bool -> ClosedDiffTheory -> S.Set FactTag
getDiffInjectiveFactInsts s isdiff = case (s, isdiff) of
           (LHS, False) -> L.get (crcInjectiveFactInsts . diffThyCacheLeft)
           (RHS, False) -> L.get (crcInjectiveFactInsts . diffThyCacheRight)
           (LHS, True)  -> L.get (crcInjectiveFactInsts . diffThyDiffCacheLeft)
           (RHS, True)  -> L.get (crcInjectiveFactInsts . diffThyDiffCacheRight)

-- | The classified set of rules modulo AC in this theory.
getClassifiedRules :: ClosedTheory -> ClassifiedRules
getClassifiedRules = L.get (crcRules . thyCache)

-- | The classified set of rules modulo AC in this theory.
getDiffClassifiedRules :: Side -> Bool -> ClosedDiffTheory -> ClassifiedRules
getDiffClassifiedRules s isdiff = case (s, isdiff) of
           (LHS, False) -> L.get (crcRules . diffThyCacheLeft)
           (RHS, False) -> L.get (crcRules . diffThyCacheRight)
           (LHS, True)  -> L.get (crcRules . diffThyDiffCacheLeft)
           (RHS, True)  -> L.get (crcRules . diffThyDiffCacheRight)

-- | The precomputed case distinctions.
getCaseDistinction :: CaseDistKind -> ClosedTheory -> [CaseDistinction]
getCaseDistinction UntypedCaseDist = L.get (crcUntypedCaseDists . thyCache)
getCaseDistinction TypedCaseDist   = L.get (crcTypedCaseDists .   thyCache)

-- | The precomputed case distinctions.
getDiffCaseDistinction :: Side -> Bool -> CaseDistKind -> ClosedDiffTheory -> [CaseDistinction]
getDiffCaseDistinction LHS False UntypedCaseDist = L.get (crcUntypedCaseDists . diffThyCacheLeft)
getDiffCaseDistinction RHS False UntypedCaseDist = L.get (crcUntypedCaseDists . diffThyCacheRight)
getDiffCaseDistinction LHS False TypedCaseDist   = L.get (crcTypedCaseDists .   diffThyCacheLeft)
getDiffCaseDistinction RHS False TypedCaseDist   = L.get (crcTypedCaseDists .   diffThyCacheRight)
getDiffCaseDistinction LHS True  UntypedCaseDist = L.get (crcUntypedCaseDists . diffThyDiffCacheLeft)
getDiffCaseDistinction RHS True  UntypedCaseDist = L.get (crcUntypedCaseDists . diffThyDiffCacheRight)
getDiffCaseDistinction LHS True  TypedCaseDist   = L.get (crcTypedCaseDists .   diffThyDiffCacheLeft)
getDiffCaseDistinction RHS True  TypedCaseDist   = L.get (crcTypedCaseDists .   diffThyDiffCacheRight)

-- construction
---------------

-- | Close a protocol rule; i.e., compute AC variant and typing assertion
-- soundness sequent, if required.
closeEitherProtoRule :: MaudeHandle -> (Side, OpenProtoRule) -> (Side, ClosedProtoRule)
closeEitherProtoRule hnd (s, ruE) = (s, closeProtoRule hnd ruE)

-- -- | Convert a lemma to the corresponding guarded formula.
-- lemmaToGuarded :: Lemma p -> Maybe LNGuarded
-- lemmaToGuarded lem =

-- | Close a theory by closing its associated rule set and checking the proof
-- skeletons and caching AC variants as well as precomputed case distinctions.
--
-- This function initializes the relation to the Maude process with the
-- correct signature. This is the right place to do that because in a closed
-- theory the signature may not change any longer.
closeTheory :: FilePath         -- ^ Path to the Maude executable.
            -> OpenTheory
            -> IO ClosedTheory
closeTheory maudePath thy0 = do
    sig <- toSignatureWithMaude maudePath $ L.get thySignature thy0
    return $ closeTheoryWithMaude sig thy0
    
-- | Close a theory by closing its associated rule set and checking the proof
-- skeletons and caching AC variants as well as precomputed case distinctions.
--
-- This function initializes the relation to the Maude process with the
-- correct signature. This is the right place to do that because in a closed
-- theory the signature may not change any longer.
closeDiffTheory :: FilePath         -- ^ Path to the Maude executable.
            -> OpenDiffTheory
            -> IO ClosedDiffTheory
closeDiffTheory maudePath thy0 = do
    sig <- toSignatureWithMaude maudePath $ L.get diffThySignature thy0
    return $ closeDiffTheoryWithMaude sig thy0
    
-- | Close a diff theory given a maude signature. This signature must be valid for
-- the given theory.
closeDiffTheoryWithMaude :: SignatureWithMaude -> OpenDiffTheory -> ClosedDiffTheory
closeDiffTheoryWithMaude sig thy0 = do
    proveDiffTheory (const True) (const True) checkProof checkDiffProof (DiffTheory (L.get diffThyName thy0) sig cacheLeft cacheRight diffCacheLeft diffCacheRight items)
  where
    diffCacheLeft  = closeRuleCache axiomsLeft  typAsms sig leftClosedRules  (L.get diffThyDiffCacheLeft  thy0) True
    diffCacheRight = closeRuleCache axiomsRight typAsms sig rightClosedRules (L.get diffThyDiffCacheRight thy0) True
    cacheLeft  = closeRuleCache axiomsLeft  typAsms sig leftClosedRules  (L.get diffThyCacheLeft  thy0) False
    cacheRight = closeRuleCache axiomsRight typAsms sig rightClosedRules (L.get diffThyCacheRight thy0) False
    checkProof = checkAndExtendProver (sorryProver Nothing)
    checkDiffProof = checkAndExtendDiffProver (sorryDiffProver Nothing)
    diffRules  = diffTheoryDiffRules thy0
    leftOpenRules  = map getLeftRule  diffRules
    rightOpenRules = map getRightRule diffRules

    -- Maude / Signature handle
    hnd = L.get sigmMaudeHandle sig

    -- Close all theory items: in parallel (especially useful for variants)
    --
    -- NOTE that 'rdeepseq' is OK here, as the proof has not yet been checked
    -- and therefore no constraint systems will be unnecessarily cached.
    (items, _solveRel, _breakers) = (`runReader` hnd) $ addSolvingLoopBreakers
       ((closeDiffTheoryItem <$> ( (L.get diffThyItems thy0) ++ (map (\x -> EitherRuleItem (LHS, x)) leftOpenRules) ++ (map (\x -> EitherRuleItem (RHS, x)) rightOpenRules))) `using` parList rdeepseq)
          where
            closeDiffTheoryItem :: DiffTheoryItem OpenProtoRule OpenProtoRule DiffProofSkeleton ProofSkeleton -> DiffTheoryItem OpenProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof
            closeDiffTheoryItem = foldDiffTheoryItem
              DiffRuleItem
              (EitherRuleItem . closeEitherProtoRule hnd)
              (\l -> DiffLemmaItem (fmap skeletonToIncrementalDiffProof l))
              (\(s, l) -> EitherLemmaItem (s, (fmap skeletonToIncrementalProof l)))
              EitherAxiomItem
              DiffTextItem
            
    -- extract typing axioms and lemmas
    axiomsLeft  = do EitherAxiomItem (LHS, ax) <- items
                     return $ formulaToGuarded_ $ L.get axFormula ax
    axiomsRight  = do EitherAxiomItem (RHS, ax) <- items
                      return $ formulaToGuarded_ $ L.get axFormula ax
    typAsms = do EitherLemmaItem (_, lem) <- items
                 guard (isTypingLemma lem)
                 return $ formulaToGuarded_ $ L.get lFormula lem

    -- extract protocol rules
    leftClosedRules  :: [ClosedProtoRule]
    leftClosedRules  = leftTheoryRules  (DiffTheory errClose errClose errClose errClose errClose errClose items)
    rightClosedRules :: [ClosedProtoRule]
    rightClosedRules = rightTheoryRules (DiffTheory errClose errClose errClose errClose errClose errClose items)
    errClose  = error "closeDiffTheory"

    addSolvingLoopBreakers = useAutoLoopBreakersAC
        (liftToItem $ enumPrems . L.get cprRuleAC)
        (liftToItem $ enumConcs . L.get cprRuleAC)
        (liftToItem $ getDisj . L.get (pracVariants . rInfo . cprRuleAC))
        addBreakers
      where
        liftToItem f (EitherRuleItem (_, ru)) = (f ru)
        liftToItem _ _                   = []

        addBreakers bs (EitherRuleItem (s, ru)) =
            EitherRuleItem (s, L.set (pracLoopBreakers . rInfo . cprRuleAC) bs ru)
        addBreakers _  item              = item


    
-- | Close a theory given a maude signature. This signature must be valid for
-- the given theory.
closeTheoryWithMaude :: SignatureWithMaude -> OpenTheory -> ClosedTheory
closeTheoryWithMaude sig thy0 = do
      proveTheory (const True) checkProof
    $ Theory (L.get thyName thy0) sig cache items
  where
    cache      = closeRuleCache axioms typAsms sig rules (L.get thyCache thy0) False
    checkProof = checkAndExtendProver (sorryProver Nothing)

    -- Maude / Signature handle
    hnd = L.get sigmMaudeHandle sig

    -- Close all theory items: in parallel (especially useful for variants)
    --
    -- NOTE that 'rdeepseq' is OK here, as the proof has not yet been checked
    -- and therefore no constraint systems will be unnecessarily cached.
    (items, _solveRel, _breakers) = (`runReader` hnd) $ addSolvingLoopBreakers
       ((closeTheoryItem <$> L.get thyItems thy0) `using` parList rdeepseq)
    closeTheoryItem = foldTheoryItem
       (RuleItem . closeProtoRule hnd)
       AxiomItem
       (LemmaItem . fmap skeletonToIncrementalProof)
       TextItem

    -- extract typing axioms and lemmas
    axioms  = do AxiomItem ax <- items
                 return $ formulaToGuarded_ $ L.get axFormula ax
    typAsms = do LemmaItem lem <- items
                 guard (isTypingLemma lem)
                 return $ formulaToGuarded_ $ L.get lFormula lem

    -- extract protocol rules
    rules :: [ClosedProtoRule]
    rules = theoryRules (Theory errClose errClose errClose items)
    errClose = error "closeTheory"

    addSolvingLoopBreakers = useAutoLoopBreakersAC
        (liftToItem $ enumPrems . L.get cprRuleAC)
        (liftToItem $ enumConcs . L.get cprRuleAC)
        (liftToItem $ getDisj . L.get (pracVariants . rInfo . cprRuleAC))
        addBreakers
      where
        liftToItem f (RuleItem ru) = f ru
        liftToItem _ _             = []

        addBreakers bs (RuleItem ru) =
            RuleItem (L.set (pracLoopBreakers . rInfo . cprRuleAC) bs ru)
        addBreakers _  item = item



-- Partial evaluation / abstract interpretation
-----------------------------------------------

-- | Apply partial evaluation.
applyPartialEvaluation :: EvaluationStyle -> ClosedTheory -> ClosedTheory
applyPartialEvaluation evalStyle thy0 =
    closeTheoryWithMaude sig $
    L.modify thyItems replaceProtoRules (openTheory thy0)
  where
    sig          = L.get thySignature thy0
    ruEs         = getProtoRuleEs thy0
    (st', ruEs') = (`runReader` L.get sigmMaudeHandle sig) $
                   partialEvaluation evalStyle ruEs

    replaceProtoRules [] = []
    replaceProtoRules (item:items)
      | isRuleItem item  =
          [ TextItem ("text", render ppAbsState)

          ] ++ map RuleItem ruEs' ++ filter (not . isRuleItem) items
      | otherwise        = item : replaceProtoRules items

    isRuleItem (RuleItem _) = True
    isRuleItem _            = False

    ppAbsState =
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size st') ++ " facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList st') $--$
      (text $ "This abstract state results in " ++ show (length ruEs') ++
              " refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (length ruEs) ++ ".\n\n")

-- | Apply partial evaluation.
applyPartialEvaluationDiff :: EvaluationStyle -> ClosedDiffTheory -> ClosedDiffTheory
applyPartialEvaluationDiff evalStyle thy0 =
    closeDiffTheoryWithMaude sig $
    L.modify diffThyItems replaceProtoRules (openDiffTheory thy0)
  where
    sig            = L.get diffThySignature thy0
    ruEs s         = getProtoRuleEsDiff s thy0
    (stL', ruEsL') = (`runReader` L.get sigmMaudeHandle sig) $
                     partialEvaluation evalStyle (ruEs LHS)
    (stR', ruEsR') = (`runReader` L.get sigmMaudeHandle sig) $
                     partialEvaluation evalStyle (ruEs RHS)

    replaceProtoRules [] = []
    replaceProtoRules (item:items)
      | isEitherRuleItem item  =
          [ DiffTextItem ("text", render ppAbsState)

          ] ++ map (\x -> EitherRuleItem (LHS, x)) ruEsL' ++ map (\x -> EitherRuleItem (RHS, x)) ruEsR' ++ filter (not . isEitherRuleItem) items
      | otherwise        = item : replaceProtoRules items

    isEitherRuleItem (EitherRuleItem _) = True
    isEitherRuleItem _                  = False

    ppAbsState =
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size stL') ++ " left facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList stL') $--$
      (text $ "This abstract state results in " ++ show (length ruEsL') ++
              " left refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (length (ruEs LHS)) ++ ".\n\n") $--$
      (text $ " the abstract state after partial evaluation"
              ++ " contains " ++ show (S.size stR') ++ " right facts:") $--$
      (numbered' $ map prettyLNFact $ S.toList stR') $--$
      (text $ "This abstract state results in " ++ show (length ruEsR') ++
              " right refined multiset rewriting rules.\n" ++
              "Note that the original number of multiset rewriting rules was "
              ++ show (length (ruEs RHS)) ++ ".\n\n")
              

-- Applying provers
-------------------

-- | Prove both the assertion soundness as well as all lemmas of the theory. If
-- the prover fails on a lemma, then its proof remains unchanged.
proveTheory :: (Lemma IncrementalProof -> Bool)   -- ^ Lemma selector.
            -> Prover
            -> ClosedTheory
            -> ClosedTheory
proveTheory selector prover thy =
    modify thyItems ((`MS.evalState` []) . mapM prove) thy
  where
    prove item = case item of
      LemmaItem l0 -> do l <- MS.gets (LemmaItem . proveLemma l0)
                         MS.modify (l :)
                         return l
      _            -> do return item

    proveLemma lem preItems
      | selector lem = modify lProof add lem
      | otherwise    = lem
      where
        ctxt    = getProofContext lem thy
        sys     = mkSystem ctxt (theoryAxioms thy) preItems $ L.get lFormula lem
        add prf = fromMaybe prf $ runProver prover ctxt 0 sys prf

-- | Prove both the assertion soundness as well as all lemmas of the theory. If
-- the prover fails on a lemma, then its proof remains unchanged.
proveDiffTheory :: (Lemma IncrementalProof -> Bool)       -- ^ Lemma selector.
            -> (DiffLemma IncrementalDiffProof -> Bool)   -- ^ DiffLemma selector.
            -> Prover
            -> DiffProver
            -> ClosedDiffTheory
            -> ClosedDiffTheory
proveDiffTheory selector diffselector prover diffprover thy =
  -- FIXME!
    modify diffThyItems ((`MS.evalState` []) . mapM prove) thy
  where
 -- Not clear wether this is correct or useful   prove :: DiffTheoryItem OpenProtoRule ClosedProtoRule IncrementalProof IncrementalProof -> DiffTheoryItem OpenProtoRule ClosedProtoRule IncrementalProof IncrementalProof
    prove item = case item of
      EitherLemmaItem (s, l0) -> do l <- MS.gets (\x -> EitherLemmaItem (s, (proveLemma s l0 x)))
                                    MS.modify (l :)
                                    return l
      DiffLemmaItem l0        -> do l' <- MS.gets (\x -> DiffLemmaItem (proveDiffLemma l0 x))
                                    MS.modify (l' :)
                                    return l'
      _                       -> do return item

    proveLemma s lem preItems
      | selector lem = modify lProof add lem
      | otherwise    = lem
      where
        ctxt    = getProofContextDiff s lem thy
        sys     = mkSystemDiff s ctxt (diffTheoryAxioms thy) preItems $ L.get lFormula lem
        add prf = fromMaybe prf $ runProver prover ctxt 0 sys prf

    proveDiffLemma lem _
      | diffselector lem = modify lDiffProof add lem
      | otherwise        = lem
      where
        ctxt    = getDiffProofContext lem thy
        sys     = emptyDiffSystem
        add prf = fromMaybe prf $ runDiffProver diffprover ctxt 0 sys prf
        
-- | Construct a constraint system for verifying the given formula.
mkSystem :: ProofContext -> [Axiom] -> [TheoryItem r p]
         -> LNFormula -> System
mkSystem ctxt axioms previousItems =
    -- Note that it is OK to add reusable lemmas directly to the system, as
    -- they do not change the considered set of traces. This is the key
    -- difference between lemmas and axioms.
    addLemmas
  . formulaToSystem (map (formulaToGuarded_ . L.get axFormula) axioms)
                    (L.get pcCaseDistKind ctxt)
                    (L.get pcTraceQuantifier ctxt) False
  where
    addLemmas sys =
        insertLemmas (gatherReusableLemmas $ L.get sCaseDistKind sys) sys

    gatherReusableLemmas kind = do
        LemmaItem lem <- previousItems
        guard $    lemmaCaseDistKind lem <= kind
                && ReuseLemma `elem` L.get lAttributes lem
                && AllTraces == L.get lTraceQuantifier lem
        return $ formulaToGuarded_ $ L.get lFormula lem

-- | Construct a constraint system for verifying the given formula.
mkSystemDiff :: Side -> ProofContext -> [(Side, Axiom)] -> [DiffTheoryItem r r2 p p2]
         -> LNFormula -> System
mkSystemDiff s ctxt axioms previousItems =
    -- Note that it is OK to add reusable lemmas directly to the system, as
    -- they do not change the considered set of traces. This is the key
    -- difference between lemmas and axioms.
    addLemmas
  . formulaToSystem (map (formulaToGuarded_ . L.get axFormula) axioms')
                    (L.get pcCaseDistKind ctxt)
                    (L.get pcTraceQuantifier ctxt) False
  where
    axioms' = foldr (\(s', a) l -> if s == s' then l ++ [a] else l) [] axioms
    addLemmas sys =
        insertLemmas (gatherReusableLemmas $ L.get sCaseDistKind sys) sys

    gatherReusableLemmas kind = do
        EitherLemmaItem (s'', lem) <- previousItems
        guard $    lemmaCaseDistKind lem <= kind && s==s''
                && ReuseLemma `elem` L.get lAttributes lem
                && AllTraces == L.get lTraceQuantifier lem
        return $ formulaToGuarded_ $ L.get lFormula lem

-- | Construct a diff constraint system.
mkDiffSystem :: DiffProofContext -> [(Side, Axiom)] -> [DiffTheoryItem r r2 p p2]
        -> DiffSystem
mkDiffSystem _ _ _ = emptyDiffSystem

------------------------------------------------------------------------------
-- References to lemmas
------------------------------------------------------------------------------

-- | Lemmas are referenced by their name.
type LemmaRef = String

-- | Resolve a path in a theory.
lookupLemmaProof :: LemmaRef -> ClosedTheory -> Maybe IncrementalProof
lookupLemmaProof name thy = L.get lProof <$> lookupLemma name thy


-- | Resolve a path in a diff theory.
lookupLemmaProofDiff :: Side -> LemmaRef -> ClosedDiffTheory -> Maybe IncrementalProof
lookupLemmaProofDiff s name thy = L.get lProof <$> lookupLemmaDiff s name thy


-- | Resolve a path in a diff theory.
lookupDiffLemmaProof :: LemmaRef -> ClosedDiffTheory -> Maybe IncrementalDiffProof
lookupDiffLemmaProof name thy = L.get lDiffProof <$> lookupDiffLemma name thy


-- | Modify the proof at the given lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyLemmaProof :: Prover -> LemmaRef -> ClosedTheory -> Maybe ClosedTheory
modifyLemmaProof prover name thy =
    modA thyItems changeItems thy
  where
    findLemma (LemmaItem lem) = name == L.get lName lem
    findLemma _               = False

    change preItems (LemmaItem lem) = do
         let ctxt = getProofContext lem thy
             sys  = mkSystem ctxt (theoryAxioms thy) preItems $ L.get lFormula lem
         lem' <- modA lProof (runProver prover ctxt 0 sys) lem
         return $ LemmaItem lem'
    change _ _ = error "LemmaProof: change: impossible"

    changeItems items = case break findLemma items of
        (pre, i:post) -> do
             i' <- change pre i
             return $ pre ++ i':post
        (_, []) -> Nothing


-- | Modify the proof at the given lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyLemmaProofDiff :: Side -> Prover -> LemmaRef -> ClosedDiffTheory -> Maybe ClosedDiffTheory
modifyLemmaProofDiff s prover name thy =
    modA diffThyItems (changeItems s) thy
  where
    findLemma s'' (EitherLemmaItem (s''', lem)) = (name == L.get lName lem) && (s''' == s'')
    findLemma _ _                            = False

    change s'' preItems (EitherLemmaItem (s''', lem)) = if s''==s'''
        then
          do
            let ctxt = getProofContextDiff s'' lem thy
                sys  = mkSystemDiff s'' ctxt (diffTheoryAxioms thy) preItems $ L.get lFormula lem
            lem' <- modA lProof (runProver prover ctxt 0 sys) lem
            return $ EitherLemmaItem (s''', lem')
        else
          error "LemmaProof: change: impossible"
    change _ _ _ = error "LemmaProof: change: impossible"

    changeItems s' items = case break (findLemma s') items of
        (pre, i:post) -> do
             i' <- change s' pre i
             return $ pre ++ i':post
        (_, []) -> Nothing

        
-- | Modify the proof at the given diff lemma ref, if there is one. Fails if the
-- path is not present or if the prover fails.
modifyDiffLemmaProof :: DiffProver -> LemmaRef -> ClosedDiffTheory -> Maybe ClosedDiffTheory
modifyDiffLemmaProof prover name thy = -- error $ show $ -- name ++ show thy
     modA diffThyItems changeItems thy
  where
    findLemma (DiffLemmaItem lem) = (name == L.get lDiffName lem)
    findLemma  _                  = False

    change preItems (DiffLemmaItem lem) =
          do
            -- I don't get why we need this here, but anyway the empty system does not seem to be a problem.
            let ctxt = getDiffProofContext lem thy
                sys  = mkDiffSystem ctxt (diffTheoryAxioms thy) preItems
            lem' <- modA lDiffProof (runDiffProver prover ctxt 0 sys) lem
            return $ DiffLemmaItem lem'
    change _ _ = error "DiffLemmaProof: change: impossible"

    changeItems items = case break findLemma items of
        (pre, i:post) -> do
             i' <- change pre i
             return $ pre ++ i':post
        (_, []) -> Nothing


------------------------------------------------------------------------------
-- Pretty printing
------------------------------------------------------------------------------

-- | Pretty print a side for parameters
prettySide :: HighlightDocument d => Side -> d
prettySide LHS = text "[left]"
prettySide RHS = text "[right]"

-- | Pretty print a formal comment
prettyFormalComment :: HighlightDocument d => String -> String -> d
prettyFormalComment "" body = multiComment_ [body]
prettyFormalComment header body = text $ header ++ "{*" ++ body ++ "*}"

-- | Pretty print a theory.
prettyTheory :: HighlightDocument d
             => (sig -> d) -> (c -> d) -> (r -> d) -> (p -> d)
             -> Theory sig c r p -> d
prettyTheory ppSig ppCache ppRule ppPrf thy = vsep $
    [ kwTheoryHeader $ text $ L.get thyName thy
    , lineComment_ "Function signature and definition of the equational theory E"
    , ppSig $ L.get thySignature thy
    , ppCache $ L.get thyCache thy
    ] ++
    parMap rdeepseq ppItem (L.get thyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldTheoryItem
        ppRule prettyAxiom (prettyLemma ppPrf) (uncurry prettyFormalComment)

-- | Pretty print a diff theory.
prettyDiffTheory :: HighlightDocument d
                 => (sig -> d) -> (c -> d) -> ((Side, r2) -> d) -> (p -> d) -> (p2 -> d)
                 -> DiffTheory sig c OpenProtoRule r2 p p2 -> d
prettyDiffTheory ppSig ppCache ppRule ppDiffPrf ppPrf thy = vsep $
    [ kwTheoryHeader $ text $ L.get diffThyName thy
    , lineComment_ "Function signature and definition of the equational theory E"
    , ppSig $ L.get diffThySignature thy
    , ppCache $ L.get diffThyCacheLeft thy
    , ppCache $ L.get diffThyCacheRight thy
    , ppCache $ L.get diffThyDiffCacheLeft thy
    , ppCache $ L.get diffThyDiffCacheRight thy
    ] ++
    parMap rdeepseq ppItem (L.get diffThyItems thy) ++
    [ kwEnd ]
  where
    ppItem = foldDiffTheoryItem
        prettyDiffRule ppRule (prettyDiffLemma ppDiffPrf) (prettyEitherLemma ppPrf) prettyEitherAxiom (uncurry prettyFormalComment)

-- | Pretty print the lemma name together with its attributes.
prettyLemmaName :: HighlightDocument d => Lemma p -> d
prettyLemmaName l = case L.get lAttributes l of
      [] -> text (L.get lName l)
      as -> text (L.get lName l) <->
            (brackets $ fsep $ punctuate comma $ map prettyLemmaAttribute as)
  where
    prettyLemmaAttribute TypingLemma    = text "typing"
    prettyLemmaAttribute ReuseLemma     = text "reuse"
    prettyLemmaAttribute InvariantLemma = text "use_induction"
    prettyLemmaAttribute LHSLemma       = text "left"
    prettyLemmaAttribute RHSLemma       = text "right"
--     prettyLemmaAttribute BothLemma      = text "both"


-- | Pretty print the diff lemma name
prettyDiffLemmaName :: HighlightDocument d => DiffLemma p -> d
prettyDiffLemmaName l = text ((L.get lDiffName l))
    
-- | Pretty print an axiom.
prettyAxiom :: HighlightDocument d => Axiom -> d
prettyAxiom ax =
    kwAxiom <-> text (L.get axName ax) <> colon $-$
    (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get axFormula ax) $-$
    (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get axFormula ax

-- | Pretty print an either axiom.
prettyEitherAxiom :: HighlightDocument d => (Side, Axiom) -> d
prettyEitherAxiom (s, ax) =
    kwAxiom <-> text (L.get axName ax) <-> prettySide s <> colon $-$
    (nest 2 $ doubleQuotes $ prettyLNFormula $ L.get axFormula ax) $-$
    (nest 2 $ if safety then lineComment_ "safety formula" else emptyDoc)
  where
    safety = isSafetyFormula $ formulaToGuarded_ $ L.get axFormula ax

    -- | Pretty print a lemma.
prettyLemma :: HighlightDocument d => (p -> d) -> Lemma p -> d
prettyLemma ppPrf lem =
    kwLemma <-> prettyLemmaName lem <> colon $-$
    (nest 2 $
      sep [ prettyTraceQuantifier $ L.get lTraceQuantifier lem
          , doubleQuotes $ prettyLNFormula $ L.get lFormula lem
          ]
    )
    $-$
    ppLNFormulaGuarded (L.get lFormula lem)
    $-$
    ppPrf (L.get lProof lem)
  where
    ppLNFormulaGuarded fm = case formulaToGuarded fm of
        Left err -> multiComment $
            text "conversion to guarded formula failed:" $$
            nest 2 err
        Right gf -> case toSystemTraceQuantifier $ L.get lTraceQuantifier lem of
          ExistsNoTrace -> multiComment
            ( text "guarded formula characterizing all counter-examples:" $-$
              doubleQuotes (prettyGuarded (gnot gf)) )
          ExistsSomeTrace -> multiComment
            ( text "guarded formula characterizing all satisfying traces:" $-$
              doubleQuotes (prettyGuarded gf) )

-- | Pretty print an Either lemma.
prettyEitherLemma :: HighlightDocument d => (p -> d) -> (Side, Lemma p) -> d
prettyEitherLemma ppPrf (_, lem) =
    kwLemma <-> prettyLemmaName lem <> colon $-$
    (nest 2 $
      sep [ prettyTraceQuantifier $ L.get lTraceQuantifier lem
          , doubleQuotes $ prettyLNFormula $ L.get lFormula lem
          ]
    )
    $-$
    ppLNFormulaGuarded (L.get lFormula lem)
    $-$
    ppPrf (L.get lProof lem)
  where
    ppLNFormulaGuarded fm = case formulaToGuarded fm of
        Left err -> multiComment $
            text "conversion to guarded formula failed:" $$
            nest 2 err
        Right gf -> case toSystemTraceQuantifier $ L.get lTraceQuantifier lem of
          ExistsNoTrace -> multiComment
            ( text "guarded formula characterizing all counter-examples:" $-$
              doubleQuotes (prettyGuarded (gnot gf)) )
          ExistsSomeTrace -> multiComment
            ( text "guarded formula characterizing all satisfying traces:" $-$
              doubleQuotes (prettyGuarded gf) )

-- | Pretty print a diff lemma.
prettyDiffLemma :: HighlightDocument d => (p -> d) -> DiffLemma p -> d
prettyDiffLemma ppPrf lem =
    kwDiffLemma <-> prettyDiffLemmaName lem <> colon 
    $-$
    ppPrf (L.get lDiffProof lem)

-- | Pretty-print a non-empty bunch of intruder rules.
prettyIntruderVariants :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntruderVariants vs = vcat . intersperse (text "") $ map prettyIntrRuleAC vs

{-
-- | Pretty-print the intruder variants section.
prettyIntrVariantsSection :: HighlightDocument d => [IntrRuleAC] -> d
prettyIntrVariantsSection rules =
    prettyFormalComment "section" " Finite Variants of the Intruder Rules " $--$
    nest 1 (prettyIntruderVariants rules)
-}

-- | Pretty print an open rule together with its assertion soundness proof.
prettyOpenProtoRule :: HighlightDocument d => OpenProtoRule -> d
prettyOpenProtoRule = prettyProtoRuleE

-- | Pretty print an open rule together with its assertion soundness proof.
prettyDiffRule :: HighlightDocument d => OpenProtoRule -> d
prettyDiffRule = prettyProtoRuleE

-- | Pretty print an open rule together with its assertion soundness proof.
prettyEitherRule :: HighlightDocument d => (Side, OpenProtoRule) -> d
prettyEitherRule (_, p) = prettyProtoRuleE p

prettyIncrementalProof :: HighlightDocument d => IncrementalProof -> d
prettyIncrementalProof = prettyProofWith ppStep (const id)
  where
    ppStep step = sep
      [ prettyProofMethod (psMethod step)
      , if isNothing (psInfo step) then multiComment_ ["unannotated"]
                                   else emptyDoc
      ]

prettyIncrementalDiffProof :: HighlightDocument d => IncrementalDiffProof -> d
prettyIncrementalDiffProof = prettyDiffProofWith ppStep (const id)
  where
    ppStep step = sep
      [ prettyDiffProofMethod (dpsMethod step)
      , if isNothing (dpsInfo step) then multiComment_ ["unannotated"]
                                    else emptyDoc
      ]

-- | Pretty print an closed rule.
prettyClosedProtoRule :: HighlightDocument d => ClosedProtoRule -> d
prettyClosedProtoRule cru =
    (prettyProtoRuleE ruE) $--$
    (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$ ppRuleAC)
  where
    ruAC = L.get cprRuleAC cru
    ruE  = L.get cprRuleE cru
    ppRuleAC
      | isTrivialProtoVariantAC ruAC ruE = multiComment_ ["has exactly the trivial AC variant"]
      | otherwise                        = multiComment $ prettyProtoRuleAC ruAC

-- -- | Pretty print an closed rule.
-- prettyClosedEitherRule :: HighlightDocument d => (Side, ClosedProtoRule) -> d
-- prettyClosedEitherRule (s, cru) = 
--     text ((show s) ++ ": ") <>
--     (prettyProtoRuleE ruE) $--$
--     (nest 2 $ prettyLoopBreakers (L.get rInfo ruAC) $-$ ppRuleAC)
--   where
--     ruAC = L.get cprRuleAC cru
--     ruE  = L.get cprRuleE cru
--     ppRuleAC
--       | isTrivialProtoVariantAC ruAC ruE = multiComment_ ["has exactly the trivial AC variant"]
--       | otherwise                        = multiComment $ prettyProtoRuleAC ruAC

-- | Pretty print an open theory.
prettyOpenTheory :: HighlightDocument d => OpenTheory -> d
prettyOpenTheory =
    prettyTheory prettySignaturePure
                 (const emptyDoc) prettyOpenProtoRule prettyProof
                 -- prettyIntrVariantsSection prettyOpenProtoRule prettyProof

-- | Pretty print an open theory.
prettyOpenDiffTheory :: HighlightDocument d => OpenDiffTheory -> d
prettyOpenDiffTheory =
    prettyDiffTheory prettySignaturePure
                 (const emptyDoc) prettyEitherRule prettyDiffProof prettyProof
                 -- prettyIntrVariantsSection prettyOpenProtoRule prettyProof

-- | Pretty print a closed theory.
prettyClosedTheory :: HighlightDocument d => ClosedTheory -> d
prettyClosedTheory thy =
    prettyTheory prettySignatureWithMaude
                 ppInjectiveFactInsts
                 -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                 prettyClosedProtoRule
                 prettyIncrementalProof
                 thy
  where
    ppInjectiveFactInsts crc =
        case S.toList $ L.get crcInjectiveFactInsts crc of
            []   -> emptyDoc
            tags -> lineComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) tags ]

-- | Pretty print a closed theory.
prettyClosedDiffTheory :: HighlightDocument d => ClosedDiffTheory -> d
prettyClosedDiffTheory thy =
    prettyDiffTheory prettySignatureWithMaude
                 ppInjectiveFactInsts
                 -- (prettyIntrVariantsSection . intruderRules . L.get crcRules)
                 (\_ -> emptyDoc) --prettyClosedEitherRule
                 prettyIncrementalDiffProof
                 prettyIncrementalProof
                 thy
  where
    ppInjectiveFactInsts crc =
        case S.toList $ L.get crcInjectiveFactInsts crc of
            []   -> emptyDoc
            tags -> lineComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) tags ]

prettyClosedSummary :: Document d => ClosedTheory -> d
prettyClosedSummary thy =
    vcat lemmaSummaries
  where
    lemmaSummaries = do
        LemmaItem lem  <- L.get thyItems thy
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary $ L.get lProof lem
            quantifier = (toSystemTraceQuantifier $ L.get lTraceQuantifier lem)
            analysisType = parens $ prettyTraceQuantifier $ L.get lTraceQuantifier lem
        return $ text (L.get lName lem) <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))

prettyClosedDiffSummary :: Document d => ClosedDiffTheory -> d
prettyClosedDiffSummary thy =
    (vcat lemmaSummaries) $$ (vcat diffLemmaSummaries)
  where
    lemmaSummaries = do
        EitherLemmaItem (s, lem)  <- L.get diffThyItems thy
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary $ L.get lProof lem
            quantifier = (toSystemTraceQuantifier $ L.get lTraceQuantifier lem)
            analysisType = parens $ prettyTraceQuantifier $ L.get lTraceQuantifier lem
        return $ text (show s) <-> text ": " <-> text (L.get lName lem) <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    diffLemmaSummaries = do
        DiffLemmaItem (lem)  <- L.get diffThyItems thy
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldDiffProof diffProofStepSummary $ L.get lDiffProof lem
        return $ text "DiffLemma: " <-> text (L.get lDiffName lem) <-> colon <->
                 text (showDiffProofStatus status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))
    diffProofStepSummary = diffProofStepStatus &&& const (Sum (1::Integer))

-- | Pretty print a 'TraceQuantifier'.
prettyTraceQuantifier :: Document d => TraceQuantifier -> d
prettyTraceQuantifier ExistsTrace = text "exists-trace"
prettyTraceQuantifier AllTraces   = text "all-traces"


-- Instances: FIXME: Sort them into the right files
--------------------------------------------------

$( derive makeBinary ''TheoryItem)
$( derive makeBinary ''DiffTheoryItem)
$( derive makeBinary ''LemmaAttribute)
$( derive makeBinary ''TraceQuantifier)
$( derive makeBinary ''Axiom)
$( derive makeBinary ''Lemma)
$( derive makeBinary ''DiffLemma)
$( derive makeBinary ''ClosedProtoRule)
$( derive makeBinary ''ClosedRuleCache)
$( derive makeBinary ''Theory)
$( derive makeBinary ''DiffTheory)

$( derive makeNFData ''TheoryItem)
$( derive makeNFData ''DiffTheoryItem)
$( derive makeNFData ''LemmaAttribute)
$( derive makeNFData ''TraceQuantifier)
$( derive makeNFData ''Axiom)
$( derive makeNFData ''Lemma)
$( derive makeNFData ''DiffLemma)
$( derive makeNFData ''ClosedProtoRule)
$( derive makeNFData ''ClosedRuleCache)
$( derive makeNFData ''Theory)
$( derive makeNFData ''DiffTheory)
