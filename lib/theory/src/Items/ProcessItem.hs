{-# LANGUAGE DeriveAnyClass #-}

module Items.ProcessItem where

import Theory.Sapic
import GHC.Generics
import Data.Binary (Binary)
import Control.DeepSeq

------------------------------------------------------------------------------
-- Processes
------------------------------------------------------------------------------

data ProcessDef = ProcessDef
  { _pName :: String
  , _pBody :: PlainProcess
  , _pVars :: Maybe [SapicLVar]
  }
  deriving (Eq, Ord, Show, Generic, NFData, Binary)
