-- |
-- Checked rendering modes shared by ProVerif property printers.
module Export.ProVerif.Render
  ( EventTimeMode (..),
    PVElement (..),
  )
where

data EventTimeMode
  = RenderEventTime
  | OmitEventTime
  deriving (Eq, Ord, Show)

data PVElement
  = R
  | RSL
  deriving (Eq, Ord, Show)
