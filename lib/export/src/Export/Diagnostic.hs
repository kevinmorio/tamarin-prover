-- |
-- Rendering and warning-policy integration for structured export diagnostics.
module Export.Diagnostic
  ( diagnosticIsProofRelevant,
    diagnosticsToWfReport,
    renderExportDiagnostics,
  )
where

import Data.Foldable (toList)
import Data.Sequence (Seq)
import Export.Types
import Text.PrettyPrint.Class
import Theory.Tools.Wellformedness (WfErrorReport, underlineTopic)

diagnosticIsProofRelevant :: ExportDiagnostic -> Bool
diagnosticIsProofRelevant diagnostic =
  case diagnostic.diagnosticImpact of
    Informational -> False
    UntranslatedGoal -> True
    ChangedAssumptions -> True
    ChangedProcessSemantics -> True

diagnosticsToWfReport :: Seq ExportDiagnostic -> WfErrorReport
diagnosticsToWfReport =
  map (\diagnostic -> (underlineTopic "Export translation", diagnosticDoc diagnostic))
    . filter diagnosticIsProofRelevant
    . toList

renderExportDiagnostics :: Seq ExportDiagnostic -> Doc
renderExportDiagnostics diagnostics
  | null entries = emptyDoc
  | otherwise =
      text "WARNING: export omitted or approximated proof-relevant input."
        $$ renderSection "Changed assumptions" ChangedAssumptions
        $$ renderSection "Untranslated goals" UntranslatedGoal
        $$ renderSection "Changed process semantics" ChangedProcessSemantics
        $$ renderSection "Export notes" Informational
  where
    entries = toList diagnostics
    renderSection heading impact =
      case filter ((== impact) . (.diagnosticImpact)) entries of
        [] -> emptyDoc
        matching ->
          text ""
            $$ text heading
            $$ text (replicate (length heading) '=')
            $$ vcat (map ((text "- " <>) . diagnosticDoc) matching)

diagnosticDoc :: ExportDiagnostic -> Doc
diagnosticDoc diagnostic =
  text (subjectLabel diagnostic.diagnosticSubject)
    <> text ": "
    <> text diagnostic.diagnosticMessage
    <> text " ["
    <> text diagnostic.diagnosticCode
    <> text "]"

subjectLabel :: DiagnosticSubject -> String
subjectLabel ProcessSubject = "Process"
subjectLabel (LemmaSubject name) = "Lemma `" ++ name ++ "`"
subjectLabel (AxiomSubject name) = "Axiom `" ++ name ++ "`"
subjectLabel (RestrictionSubject name) = "Restriction `" ++ name ++ "`"
subjectLabel (BuiltinSubject name) = "Builtin `" ++ name ++ "`"
