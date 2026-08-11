-- |
-- Checked rendering modes shared by ProVerif property printers.
module Export.ProVerif.Render
  ( ppAxiomLemma,
    ppLemma,
    ppRestr,
    renderSapicFormula,
  )
where

import Control.Monad.Fresh
import Control.Monad.Trans.PreciseFresh qualified as Precise
import Data.List as List
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Maybe
import Data.Set qualified as S
import Export.Name (freshNameAvoiding)
import Export.ProVerif.Formula
import Export.ProVerif.Instrumentation
import Export.ProVerif.Property
import Export.Sapic
import Export.Types
import Sapic.Typing
import Text.PrettyPrint.Class
import Theory
import Theory.Sapic
import Theory.Text.Pretty

data EventTimeMode
  = RenderEventTime
  | OmitEventTime
  deriving (Eq, Ord, Show)

data PVElement
  = R
  | RSL
  deriving (Eq, Ord, Show)

renderSapicFormula :: LNFormula -> Doc
renderSapicFormula formula =
  fst . snd $
    Precise.evalFresh
      (ppLFormula emptyTypeEnv (ppNAtom RenderEventTime M.empty S.empty) formula)
      (avoidPrecise formula)

mergeType :: (Eq a) => Maybe a -> Maybe a -> Maybe a
mergeType t Nothing = t
mergeType _ t = t

mergeEnv :: M.Map LVar SapicType -> M.Map LVar SapicType -> M.Map LVar SapicType
mergeEnv = M.mergeWithKey (\_ t1 t2 -> Just $ mergeType t1 t2) id id

typeVarsEvent :: (Ord k) => TypingEnvironment -> FactTag -> [Term (Lit c k)] -> M.Map k SapicType
typeVarsEvent TypingEnvironment {events = ev} tag ts =
  case M.lookup tag ev of
    Just t ->
      foldl
        ( \mp (term, ty) ->
            case viewTerm term of
              Lit (Var lvar) -> M.insert lvar ty mp
              _ -> mp
        )
        M.empty
        (zip ts t)
    Nothing -> M.empty

ppProtoAtom ::
  (HighlightDocument d, Ord k, Show k, Show c) =>
  EventTimeMode ->
  d -> -- shared rule-ID variable
  (Term (Lit c k) -> Maybe d) -> -- per-occurrence rule-id variable of a timepoint variable, if any
  S.Set String -> -- events requiring rule identifiers
  TypingEnvironment ->
  Bool ->
  (s (Term (Lit c k)) -> d) ->
  (Term (Lit c k) -> d) ->
  ProtoAtom s (Term (Lit c k)) ->
  (d, M.Map k SapicType)
ppProtoAtom eventTimeMode sharedRuleId ridOf ruleIdEvents te _ _ ppT (Action v f@(Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | tag == KUFact = translationFail "KU facts are outside the supported formula translation"
  | isKLogFact f =
      (withEventTime (ppFactL "attacker" ts), M.empty)
  | otherwise =
      ( withEventTime
          ( text "event("
              <> eventArgs ('e' : factTagName tag) ts
              <> text ")"
          ),
        typeVarsEvent te tag ts
      )
  where
    factName = factTagName tag
    useRuleId = factName `S.member` ruleIdEvents
    ppFactL n t = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ map ppT t
    eventArgs n t
      | useRuleId = nestShort' (n ++ "(") ")" . fsep . punctuate comma $ (ridDoc : map ppT t)
      | otherwise = ppFactL n t
    ridDoc = fromMaybe sharedRuleId (ridOf v)
    withEventTime document =
      case eventTimeMode of
        RenderEventTime -> document <> opAction <> ppT v
        OmitEventTime -> document
ppProtoAtom _ _ _ _ _ _ ppS _ (Syntactic s) = (ppS s, M.empty)
-- A temporal equality between rule-id instrumented events is translated as an
-- equality of their rule-id variables: distinct ProVerif events never share a
-- timepoint, while in Tamarin equal timepoints mean "same rule instance".
ppProtoAtom _ _ ridOf _ _ False _ ppT (EqE l r) =
  case (ridOf l, ridOf r) of
    (Just dl, Just dr) -> (sep [dl <-> opEqual, dr], M.empty)
    _ -> (sep [ppT l <-> opEqual, ppT r], M.empty)
ppProtoAtom _ _ ridOf _ _ True _ ppT (EqE l r) =
  case (ridOf l, ridOf r) of
    (Just dl, Just dr) -> (sep [dl <-> text "<>", dr], M.empty)
    _ -> (sep [ppT l <-> text "<>", ppT r], M.empty)
ppProtoAtom _ _ _ _ _ _ _ ppT (Less u v) = (ppT u <-> opLess <-> ppT v, M.empty)
ppProtoAtom _ _ _ _ _ _ _ ppT (Subterm u v) = (text "subterm(" <> ppT u <> comma <> ppT v <> text ")", M.empty)
ppProtoAtom _ _ _ _ _ _ _ _ (Last i) = (operator_ "last" <> parens (text (show i)), M.empty)

ppAtom :: EventTimeMode -> M.Map String String -> S.Set String -> TypingEnvironment -> Bool -> (LNTerm -> Doc) -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppAtom eventTimeMode ridNames ruleIdEvents te b =
  ppProtoAtom eventTimeMode (text "rid") ridOf ruleIdEvents te b (const emptyDoc)
  where
    ridOf t
      | eventTimeMode == OmitEventTime = Nothing
      | otherwise = case viewTerm t of
          Lit (Var (LVar n LSortNode _)) -> text <$> M.lookup n ridNames
          _ -> Nothing

-- only used for ProVerif queries display
-- the Bool is set to False when we must negate the atom
ppNAtom :: EventTimeMode -> M.Map String String -> S.Set String -> TypingEnvironment -> Bool -> ProtoAtom s LNTerm -> (Doc, M.Map LVar SapicType)
ppNAtom eventTimeMode ridNames ruleIdEvents te b =
  ppAtom eventTimeMode ridNames ruleIdEvents te b (fst . ppLNTerm emptyTC)

extractFree :: BVar p -> p
extractFree (Free v) = v
extractFree (Bound i) = translationInvariantFail $ "prettyFormula: illegal bound variable '" ++ show i ++ "'"

toLAt :: (Ord (f1 b), Ord (f1 (BVar b)), Functor f2, Functor f1) => f2 (Term (f1 (BVar b))) -> f2 (Term (f1 b))
toLAt = fmap (mapLits (fmap extractFree))

ppLFormula ::
  (MonadFresh m, Ord c, HighlightDocument b, Functor syn) =>
  TypingEnvironment ->
  (TypingEnvironment -> Bool -> ProtoAtom syn (Term (Lit c LVar)) -> (b, M.Map LVar SapicType)) ->
  ProtoFormula syn (String, LSort) c LVar ->
  m ([LVar], (b, M.Map LVar SapicType))
ppLFormula = ppLFormulaWithTimeVars True

ppLFormulaWithTimeVars ::
  (MonadFresh m, Ord c, HighlightDocument b, Functor syn) =>
  Bool ->
  TypingEnvironment ->
  (TypingEnvironment -> Bool -> ProtoAtom syn (Term (Lit c LVar)) -> (b, M.Map LVar SapicType)) ->
  ProtoFormula syn (String, LSort) c LVar ->
  m ([LVar], (b, M.Map LVar SapicType))
ppLFormulaWithTimeVars keepTimeVars te ppAt =
  printFormula
  where
    printFormula (Ato a) = pure ([], ppAt te False (toLAt a))
    printFormula (TF True) = pure ([], (operator_ "true", M.empty)) -- "T"
    printFormula (TF False) = pure ([], (operator_ "false", M.empty)) -- "F"
    printFormula (Not (Ato a@(EqE _ _))) = pure ([], ppAt te True (toLAt a))
    printFormula (Not p) = do
      (vs, (p', envp)) <- printFormula p
      pure (vs, (operator_ "not" <> opParens p', envp))
    printFormula (Conn op p q) = do
      (vsp, (p', envp)) <- printFormula p
      (vsq, (q', envq)) <- printFormula q
      pure (vsp ++ vsq, (sep [opParens p' <-> ppOp op, opParens q'], mergeEnv envp envq))
      where
        ppOp And = text "&&"
        ppOp Or = text "||"
        ppOp Imp = text "==>"
        ppOp Iff = opIff
    printFormula fm@(Qua {}) =
      scopeFreshness $ do
        (vs, _, fm') <- openFormulaPrefix fm
        (vsp, d') <- printFormula fm'
        pure (filter (\v -> keepTimeVars || lvarSort v /= LSortNode) (vs ++ vsp), d')

data DeclarationMode
  = QueryDeclaration
  | AssumptionDeclaration PVElement Bool

ppFormulaDeclaration ::
  MonadFresh m =>
  DeclarationMode ->
  M.Map String String ->
  S.Set String ->
  TypingEnvironment ->
  LNFormula ->
  [LVar] ->
  String ->
  m Doc
ppFormulaDeclaration mode originalRuleIdNames ruleIdEvents typeEnvironment formula extraVariables attributes = do
  (variables, (body, variableTypes)) <- renderBody formula
  let needsSharedRuleId
        | M.null ruleIdNames = formulaUsesRuleIdEvents ruleIdEvents formula
        | otherwise =
            any
              (\(timepoint, tag) -> tag `S.member` ruleIdEvents && timepoint `M.notMember` ruleIdNames)
              (collectEventTimeVars formula)
      declaredVariables =
        [text "rid:bitstring" | needsSharedRuleId]
          ++ [text (name ++ ":bitstring") | name <- S.toList (S.fromList (M.elems ruleIdNames))]
          ++ map (ppTimeTypeVar variableTypes) (S.toList (S.fromList (extraVariables ++ variables)))
  pure $ case mode of
    QueryDeclaration ->
      sep
        [ if null declaredVariables
            then text "query;"
            else text "query " <> fsep (punctuate comma declaredVariables) <> text ";",
          nest 1 body <> text attributes <> text "."
        ]
    AssumptionDeclaration element _ ->
      sep
        [ text (declarationWord element) <> fsep (punctuate comma declaredVariables) <> text ";",
          nest 1 body,
          text attributes,
          text "."
        ]
  where
    keepTimeVariables = case mode of
      QueryDeclaration -> True
      AssumptionDeclaration _ keep -> keep
    ruleIdNames
      | keepTimeVariables = originalRuleIdNames
      | otherwise = M.empty
    eventTimeMode
      | keepTimeVariables = RenderEventTime
      | otherwise = OmitEventTime
    atomRenderer = ppNAtom eventTimeMode ruleIdNames ruleIdEvents
    renderBody (Conn Imp (TF True) conclusion)
      | QueryDeclaration <- mode = do
          (variables, (conclusionDoc, variableTypes)) <-
            ppLFormula typeEnvironment atomRenderer conclusion
          pure
            ( variables,
              ( sep [opParens (text "attacker(())") <-> text "==>", opParens conclusionDoc],
                variableTypes
              )
            )
    renderBody body =
      ppLFormulaWithTimeVars keepTimeVariables typeEnvironment atomRenderer body
    declarationWord R = "restriction "
    declarationWord RSL = "axiom "
ppTimeTypeVar :: M.Map LVar SapicType -> LVar -> Doc
ppTimeTypeVar _ lvar@(LVar _ LSortNode _) = ppLVar lvar <> text ":time"
ppTimeTypeVar te lvar =
  case M.lookup lvar te of
    Nothing -> ppLVar lvar <> text ":bitstring"
    Just t -> ppLVar lvar <> text ":" <> text (ppType t)

collectBinderHints :: LNFormula -> [(String, LSort)]
collectBinderHints (Qua _ binderHint body) = binderHint : collectBinderHints body
collectBinderHints (Not body) = collectBinderHints body
collectBinderHints (Conn _ left right) = collectBinderHints left ++ collectBinderHints right
collectBinderHints _ = []

-- | Rename timepoint variables whose name collides with a term variable.
-- Tamarin keeps term variables ('t') and timepoint variables ('#t') in
-- separate namespaces, but a ProVerif query has a single namespace. The term
-- variable keeps its name; the colliding timepoint gets a fresh name
-- ('#t' -> '#t1'). Timepoints still bound in the formula are renamed at their
-- binder; timepoints already opened by the caller are renamed as free
-- variables and in the extra query variables. Returns the renaming so that
-- keys of per-occurrence rule-id maps can be remapped alongside.
renameCollidingTimepoints :: LNFormula -> [LVar] -> (M.Map String String, LNFormula, [LVar])
renameCollidingTimepoints fm extravs
  | M.null renaming = (renaming, fm, extravs)
  | otherwise = (renaming, renameFrees (renameHints fm), map renameVar extravs)
  where
    hints = collectBinderHints fm
    freeVars = frees fm ++ extravs
    termNames =
      S.fromList $
        [n | (n, s) <- hints, s /= LSortNode]
          ++ [n | LVar n s _ <- freeVars, s /= LSortNode]
    nodeNames =
      S.fromList $
        [n | (n, LSortNode) <- hints]
          ++ [n | LVar n LSortNode _ <- freeVars]
    usedNames = S.fromList (map fst hints) `S.union` S.fromList (map lvarName freeVars)
    renaming =
      M.fromList . snd $
        List.mapAccumL freshen usedNames (S.toList (termNames `S.intersection` nodeNames))
    freshen used n =
      let n' = freshNameAvoiding "" used n
       in (S.insert n' used, (n, n'))

    renameHints (Qua q (n, s) p)
      | s == LSortNode, Just n' <- M.lookup n renaming = Qua q (n', s) (renameHints p)
      | otherwise = Qua q (n, s) (renameHints p)
    renameHints (Not p) = Not (renameHints p)
    renameHints (Conn c p q) = Conn c (renameHints p) (renameHints q)
    renameHints f = f

    renameFrees = apply substRename
    substRename :: LNSubst
    substRename =
      substFromList
        [ (v, varTerm (renameVar v))
          | v@(LVar n LSortNode _) <- List.nub (frees fm),
            n `M.member` renaming
        ]

    renameVar v@(LVar n LSortNode _)
      | Just n' <- M.lookup n renaming = v {lvarName = n'}
    renameVar v = v

-- | Sibling quantifiers that reuse a binder name collapse to one query
-- variable when the formula is flattened into a single ProVerif query. For
-- binders separated by a (positive) disjunction this is harmless: the merged
-- variable is used once per disjunct, and distributing an existential over a
-- disjunction is an equivalence. Binders whose scopes can be active on the
-- same conjunctive path must stay distinct, however: merging them equates
-- independent timepoints, and ProVerif rejects the result outright for time
-- variables ("Time variable also assigned"). Rename every later duplicate
-- that is not separated from all earlier same-named binders by a
-- disjunction.
renameConjunctiveDuplicateBinders :: LNFormula -> [LVar] -> LNFormula
renameConjunctiveDuplicateBinders fm extravs = snd (go True M.empty st0 fm)
  where
    st0 = (0 :: Int, M.empty :: M.Map String [M.Map Int Bool], used0)
    -- Avoid both the raw names and the printed forms ('n_i' for index i) of
    -- all binders and free variables.
    used0 =
      S.fromList (map fst hints)
        `S.union` S.fromList (map printedName (frees fm ++ extravs))
    printedName (LVar n _ 0) = n
    printedName (LVar n _ i) = n ++ "_" ++ show i
    hints = collectBinderHints fm

    -- A positive disjunction separates its branches; under negation the roles
    -- of conjunction and disjunction swap. Implication premises count as
    -- negated; premise and conclusion are not separated from each other.
    go pos w st (Conn Or p q)
      | pos = branch pos w st Or p q
    go pos w st (Conn And p q)
      | not pos = branch pos w st And p q
    go pos w st (Conn Imp p q) =
      let (st1, p') = go (not pos) w st p
          (st2, q') = go pos w st1 q
       in (st2, Conn Imp p' q')
    go pos w st (Conn c p q) =
      let (st1, p') = go pos w st p
          (st2, q') = go pos w st1 q
       in (st2, Conn c p' q')
    go pos w st (Not p) = let (st1, p') = go (not pos) w st p in (st1, Not p')
    go pos w (oid, kept, used) (Qua q (n, s) p) =
      let conflicts = any (conflicting w) (M.findWithDefault [] n kept)
          (n', used') =
            if conflicts
              then let c = freshName n used in (c, S.insert c used)
              else (n, used)
          kept' = M.insertWith (++) n' [w] kept
          (st1, p') = go pos w (oid, kept', used') p
       in (st1, Qua q (n', s) p')
    go _ _ st f = (st, f)

    branch pos w (oid, kept, used) c p q =
      let (st1, p') = go pos (M.insert oid True w) (oid + 1, kept, used) p
          (st2, q') = go pos (M.insert oid False w) st1 q
       in (st2, Conn c p' q')

    -- Two binders conflict unless some disjunction on both their paths
    -- separates them (same node, different sides).
    conflicting w w' = and (M.elems (M.intersectionWith (==) w w'))
    -- 'n_i' matches how the freshness machinery would have printed a
    -- disambiguated duplicate, keeping the output stable for formulas it
    -- already handled (nested duplicates).
    freshName name used = freshNameAvoiding "_" used name

ppFormulaEx :: DeclarationMode -> M.Map String String -> S.Set String -> TypingEnvironment -> LNFormula -> [LVar] -> String -> Doc
ppFormulaEx mode originalRuleIdNames ruleIdEvents typeEnvironment originalFormula originalVariables attributes =
  Precise.evalFresh
    (ppFormulaDeclaration mode ruleIdNames ruleIdEvents typeEnvironment formula variables attributes)
    (avoidPrecise formula)
  where
    (renaming, renamedFormula, variables) =
      renameCollidingTimepoints originalFormula originalVariables
    formula = renameConjunctiveDuplicateBinders renamedFormula variables
    ruleIdNames = M.mapKeys (\key -> M.findWithDefault key key renaming) originalRuleIdNames

renderPreparedQuery ::
  M.Map String String ->
  S.Set String ->
  TypingEnvironment ->
  PreparedFormula ->
  String ->
  Doc
renderPreparedQuery ridNames ruleIdEvents typeEnvironment prepared attributes =
  Precise.evalFresh (go formula) (avoidPrecise formula)
  where
    formula = prepared.preparedFormula
    renderFormula body variables =
      ppFormulaEx QueryDeclaration ridNames ruleIdEvents typeEnvironment body variables attributes
    openAndRender quantified = do
      (variables, _, body) <- openFormulaPrefix quantified
      pure (renderFormula body variables)
    go (Not quantified@(Qua Ex _ _)) = openAndRender quantified
    go quantified@(Qua Ex _ _) = openAndRender quantified
    go (Not quantified@(Qua All _ _)) = pure (renderFormula quantified [])
    go quantified@(Qua All _ _) = pure (renderFormula quantified [])
    go _ = translationInvariantFail "prepared query violated the supported-fragment invariant"

ppLemma :: S.Set String -> TypingEnvironment -> Lemma ProofSkeleton -> PropertyOutcome PreparedQueryProperty -> Doc
ppLemma _ruleIdEvents _te p (PropertyOmitted reason) =
      text "(*" <> text p._lName <> text "*)"
        $$ text ("(* Lemma translation failed: " ++ reason ++ ". *)")
        $$ text "(*" <> prettyLNFormula p._lFormula <> text "*)"
        $$ text ""
ppLemma _ _ _ PropertyExcluded = emptyDoc
ppLemma ruleIdEvents te p (PropertyEmitted prepared) =
  vcat (intersperse (text "") (map renderSubformula (NE.toList prepared.preparedQueryFormulas)))
    $$ reconstructionComment
  where
    lemmaNameComment = text "(*" <> text p._lName <> text "*)"
    useInduction
      | InvariantLemma `elem` p._lAttributes = "[induction]"
      | otherwise = ""
    renderSubformula queryFormula =
      vcat
        ( [lemmaNameComment]
            ++ catMaybes [timepointComment, negationWarning]
            ++ [queryDoc]
        )
      where
        preparedFormulaPlan = queryFormula.preparedQueryBody
        timepointComment
          | preparedFormulaPlan.preparedHadTimepointSplit =
              Just (text "(* Timepoints in lemma have been split *)")
          | otherwise = Nothing
        negationWarning
          | queryFormula.preparedQueryPolarity == InvertResult =
              Just (text "(* Lemma has a leading negation, interpret ProVerif's answers accordingly! *)")
          | otherwise = Nothing
        queryDoc =
          renderPreparedQuery
            preparedFormulaPlan.preparedRuleIdNames
            ruleIdEvents
            te
            preparedFormulaPlan
            useInduction
    reconstructionComment = case prepared.preparedQueryRecombination of
      Nothing -> text ""
      Just ConjoinQueryResults ->
        text "(* To reconstruct lemma " <> text p._lName <> text ", combine the query results with ∧. *)"
      Just DisjoinQueryResults ->
        text "(* To reconstruct lemma " <> text p._lName <> text ", combine the query results with ∨. *)"

renderPreparedAssumption ::
  PVElement ->
  S.Set String ->
  TypingEnvironment ->
  PreparedFormula ->
  String ->
  Doc
renderPreparedAssumption element ruleIdEvents typeEnvironment prepared attributes =
  Precise.evalFresh (go formula) (avoidPrecise formula)
  where
    formula = prepared.preparedFormula
    renderFormula body variables =
      ppFormulaEx
        (AssumptionDeclaration element prepared.preparedKeepTimeVariables)
        prepared.preparedRuleIdNames
        ruleIdEvents
        typeEnvironment
        body
        variables
        attributes
    go (Not quantified@(Qua Ex _ _)) = do
      (variables, _, body) <- openFormulaPrefix quantified
      pure (renderFormula body variables)
    go quantified@(Qua All _ _) = pure (renderFormula quantified [])
    go _ = translationInvariantFail "prepared assumption violated the supported-fragment invariant"
ppAxiomLemma :: S.Set String -> TypingEnvironment -> Lemma ProofSkeleton -> PropertyOutcome PreparedAxiomProperty -> Doc
ppAxiomLemma _ruleIdEvents _te l (PropertyOmitted reason) =
      text "(*"
        <> text l._lName
        <> text " [reuse/source lemma not translated as axiom]"
        <> text "*)"
        $$ text ("(* Axiom translation failed: " ++ reason ++ ". *)")
        $$ text "(*" <> prettyLNFormula l._lFormula <> text "*)"
        $$ text ""
ppAxiomLemma _ _ _ PropertyExcluded = emptyDoc
ppAxiomLemma ruleIdEvents te l (PropertyEmitted prepared) =
  timepointComment
    $$ text "(*"
    <> text l._lName
    <> text " [reuse/source lemma translated as axiom]"
    <> text "*)"
    $$ vcat (intersperse (text "") (map renderAxiom (NE.toList prepared.preparedAxiomFormulas)))
  where
    renderAxiom preparedFormulaPlan =
      renderPreparedAssumption RSL ruleIdEvents te preparedFormulaPlan ""

    timepointComment = if any preparedHadTimepointSplit prepared.preparedAxiomFormulas
                       then text "(* Timepoints in lemma have been split *)\n"
                       else text ""

ppRestr :: S.Set String -> TypingEnvironment -> Restriction -> PropertyOutcome PreparedRestrictionProperty -> Doc
ppRestr _ _ restriction (PropertyOmitted reason) =
  text "(*" <> text restriction._rstrName <> text "*)"
    $$ text ("(* Restriction translation failed: " ++ reason ++ ". *)")
    $$ text "(*" <> prettyLNFormula restriction._rstrFormula <> text "*)"
    $$ text ""
ppRestr _ _ _ PropertyExcluded = emptyDoc
ppRestr ruleIdEvents typeEnvironment restriction (PropertyEmitted prepared) =
  timepointComment
    $$ text "(*" <> text restriction._rstrName <> text "*)"
    $$ originalComment
    $$ vcat (intersperse (text "") (map renderFormula (NE.toList prepared.preparedRestrictionFormulas)))
  where
    timepointComment
      | any preparedHadTimepointSplit prepared.preparedRestrictionFormulas =
          text "(* Timepoints in restriction have been split *)"
      | otherwise = emptyDoc
    originalComment
      | prepared.preparedRestrictionWasRewritten =
          text "(* Original: " <> prettyLNFormula restriction._rstrFormula <> text " *)"
      | otherwise = emptyDoc
    renderFormula preparedFormulaPlan =
      renderPreparedAssumption R ruleIdEvents typeEnvironment preparedFormulaPlan ""
