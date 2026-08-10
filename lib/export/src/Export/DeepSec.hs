-- |
-- DeepSec backend entry point.
module Export.DeepSec (prettyDeepSecTheory) where

import Data.List (intersperse)
import Data.Set qualified as Set
import Export.ProVerif
import Export.Sapic
import Export.Types
import Text.PrettyPrint.Class
import Theory

prettyDeepSecTheory :: Int -> OpenTheory -> IO (Either ExportError ExportResult)
prettyDeepSecTheory replicationLimit thy =
  captureExport diagnostics $ do
    headers <- loadHeaders Set.empty context thy emptyTypeEnv
    let renderedHeaders =
          attribHeaders context $ Set.toList (Set.unions [headers, macroHeaders, equivalenceHeaders])
    pure $ deepSecTemplate renderedHeaders macroProcesses requests equivalenceLemmas comments
  where
    context = emptyTC {trans = DeepSec, replicationBound = replicationLimit}
    requests =
      map (text . (._eText)) (lookupExportInfo "requests" thy)
    (macroProcesses, macroHeaders) = loadMacroProc context thy
    (equivalenceLemmas, equivalenceHeaders, _, _) = loadEquivProc context thy
    comments = [text "(*" $$ text body $$ text "*)" | (_, body) <- theoryFormalComments thy]
    diagnostics = collectBuiltinDiagnostics thy

deepSecTemplate :: (Document d) => [d] -> [d] -> [d] -> [d] -> [d] -> d
deepSecTemplate headers macroProcesses requests equivalenceLemmas comments =
  vcat headers
    $$ vcat macroProcesses
    $$ vcat requests
    $$ vcat equivalenceLemmas
    $--$ vcat (intersperse (text "") comments)
