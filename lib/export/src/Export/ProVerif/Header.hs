module Export.ProVerif.Header
  ( ProVerifHeader (..),
    filterHeaders,
    getProVerifHeaderIdentifier,
    checkDuplicates',
  )
where

import Control.Monad (unless)
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Export.Types (translationFail)

-- ProVerif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProVerifHeader
  = Type String -- type declaration
  | Sym String String String [String] -- symbol declaration, (symkind,name,type,attr)
  | Fun String String Int String [String] -- symbol declaration, (symkind,name,arity,types,attr)
  | HEvent String String
  | Table String String
  | Eq String String String String -- eqtype, quantif, equation pub/priv
  deriving (Ord, Show, Eq)

filterHeaders :: Set.Set ProVerifHeader -> Set.Set ProVerifHeader
filterHeaders = Set.filter (not . isForbidden)
  where
    isForbidden (Fun "fun" "true" _ _ _) = True
    isForbidden (Type "bitstring") = True
    isForbidden (Type "channel") = True
    isForbidden (Type "nat") = True
    isForbidden _ = False

getProVerifHeaderIdentifier :: ProVerifHeader -> Maybe String
getProVerifHeaderIdentifier (Fun _ name _ _ _) = Just name
getProVerifHeaderIdentifier (Sym _ name _ _) = Just name
getProVerifHeaderIdentifier (HEvent name _) = Just name
getProVerifHeaderIdentifier (Table name _) = Just name
getProVerifHeaderIdentifier _ = Nothing

checkDuplicates' :: Set.Set ProVerifHeader -> IO [ProVerifHeader]
checkDuplicates' headers = do
  unless (null conflicts) $
    translationFail $
      unlines
        ( "ProVerif constructs (functions, constants, events, tables) must be distinct. Please rename these duplicates:"
            : [intercalate ", " (map show definitions) | (_, definitions) <- conflicts]
        )
  pure (Set.toList headers)
  where
    identifiers =
      Map.fromListWith (<>)
        [ (name, [header])
        | header <- Set.toList headers,
          Just name <- [getProVerifHeaderIdentifier header]
        ]
    conflicts = Map.toList (Map.filter ((> 1) . length) identifiers)
