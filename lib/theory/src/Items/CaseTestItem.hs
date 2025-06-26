{-# LANGUAGE DeriveAnyClass #-}

module Items.CaseTestItem where

import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Data.Binary (Binary)
import Theory.Model
import Theory.Syntactic.Predicate
import Text.PrettyPrint.Highlight (HighlightDocument, Document (nest, (<->), ($-$), text, sep), colon, doubleQuotes)

------------------------------------------------------------------------------
-- Case Tests
------------------------------------------------------------------------------

type CaseIdentifier = String

data CaseTest = CaseTest
  { _cName       :: CaseIdentifier
  , _cFormula    :: SyntacticLNFormula
  }
  deriving (Eq, Ord, Show, Generic, NFData, Binary)

caseTestToPredicate :: CaseTest -> Maybe Predicate
caseTestToPredicate caseTest = fmap (Predicate fact) formula
  where
    fact = protoFact Linear caseTest._cName (frees formula)
    formula = toLNFormula caseTest._cFormula

prettyCaseTest :: HighlightDocument d => CaseTest -> d
prettyCaseTest caseTest =
    text "test" <-> text caseTest._cName <> colon $-$
    (nest 2 $
      sep [ doubleQuotes $ prettySyntacticLNFormula caseTest._cFormula ]
    )
