{-# LANGUAGE DeriveAnyClass #-}

module Items.ExportInfo where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)

data ExportInfo = ExportInfo
  { _eTag  :: String
  , _eText :: String
  }
  deriving (Eq, Ord, Show, Generic, NFData, Binary)
