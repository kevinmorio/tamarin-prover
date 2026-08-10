-- |
-- Deterministic target-name allocation shared by exporter components.
module Export.Name
  ( TargetNamespace (..),
    TargetEvent (..),
    TargetVariable (..),
    NameAllocator,
    emptyNameAllocator,
    reserveNames,
    allocateEvent,
    allocateVariable,
  )
where

import Data.Map.Strict qualified as Map
import Data.Set qualified as Set

data TargetNamespace
  = GlobalNamespace
  | VariableNamespace
  deriving (Eq, Ord, Show)

newtype TargetEvent = TargetEvent {targetEventText :: String}
  deriving (Eq, Ord, Show)

newtype TargetVariable = TargetVariable {targetVariableText :: String}
  deriving (Eq, Ord, Show)

newtype NameAllocator = NameAllocator (Map.Map TargetNamespace (Set.Set String))
  deriving (Eq, Show)

emptyNameAllocator :: NameAllocator
emptyNameAllocator = NameAllocator Map.empty

reserveNames :: TargetNamespace -> Set.Set String -> NameAllocator -> NameAllocator
reserveNames namespace names (NameAllocator allocated) =
  NameAllocator (Map.insertWith Set.union namespace names allocated)

allocateEvent :: String -> NameAllocator -> (TargetEvent, NameAllocator)
allocateEvent preferred allocator =
  let (name, allocator') = allocate GlobalNamespace preferred allocator
   in (TargetEvent name, allocator')

allocateVariable :: String -> NameAllocator -> (TargetVariable, NameAllocator)
allocateVariable preferred allocator =
  let (name, allocator') = allocate VariableNamespace preferred allocator
   in (TargetVariable name, allocator')

allocate :: TargetNamespace -> String -> NameAllocator -> (String, NameAllocator)
allocate namespace preferred allocator =
  (chosen, reserveNames namespace (Set.singleton chosen) allocator)
  where
    used = namesIn namespace allocator
    chosen =
      head
        [ candidate
        | candidate <- preferred : [preferred ++ "_" ++ show suffix | suffix <- [(1 :: Integer) ..]],
          candidate `Set.notMember` used
        ]

namesIn :: TargetNamespace -> NameAllocator -> Set.Set String
namesIn namespace (NameAllocator allocated) =
  Map.findWithDefault Set.empty namespace allocated

