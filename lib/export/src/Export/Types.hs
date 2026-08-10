-- |
-- Shared result and diagnostic types for exporter backends.
module Export.Types
  ( DiagnosticSeverity (..),
    DiagnosticImpact (..),
    DiagnosticSubject (..),
    ExportDiagnostic (..),
    ExportError (..),
    ExportResult (..),
  )
where

import Data.Sequence (Seq)
import Text.PrettyPrint.Class (Doc)

data DiagnosticSeverity
  = DiagnosticNotice
  | DiagnosticWarning
  | DiagnosticFatal
  deriving (Eq, Ord, Show)

data DiagnosticImpact
  = Informational
  | UntranslatedGoal
  | ChangedAssumptions
  | ChangedProcessSemantics
  deriving (Eq, Ord, Show)

data DiagnosticSubject
  = ProcessSubject
  | LemmaSubject String
  | AxiomSubject String
  | RestrictionSubject String
  | BuiltinSubject String
  deriving (Eq, Ord, Show)

data ExportDiagnostic = ExportDiagnostic
  { diagnosticCode :: String,
    diagnosticSeverity :: DiagnosticSeverity,
    diagnosticImpact :: DiagnosticImpact,
    diagnosticSubject :: DiagnosticSubject,
    diagnosticMessage :: String
  }
  deriving (Eq, Ord, Show)

data ExportError = ExportError
  { exportErrorCode :: String,
    exportErrorMessage :: String
  }
  deriving (Eq, Ord, Show)

data ExportResult = ExportResult
  { exportDocument :: Doc,
    exportDiagnostics :: Seq ExportDiagnostic
  }

