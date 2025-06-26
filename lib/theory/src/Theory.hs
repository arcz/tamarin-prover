-- FIXME: for functions prove
-- |
-- Copyright   : (c) 2010-2012 Benedikt Schmidt & Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : GHC only
--
-- Theory datatype and transformations on it.
module Theory (
  -- * Restrictions
    expandRestriction

  -- * Processes
  , ProcessDef(..)
  , TranslationElement(..)
  -- Datastructure added to Theory Items
  , addProcess
  , findProcess
  , mapMProcesses
  , mapMProcessesDef
  , addProcessDef
  , lookupProcessDef
  , lookupFunctionTypingInfo
  , addFunctionTypingInfo
  , addMacros
  , addDiffMacros
  , clearFunctionTypingInfos

  -- * Options
  , transAllowPatternMatchinginLookup
  , transProgress
  , transReliable
  , transReport
  , stateChannelOpt
  , asynchronousChannels
  , compressEvents
  , forcedInjectiveFacts
  , setforcedInjectiveFacts
  , thyOptions
  , thyIsSapic
  , setOption
  , Option
  -- * Predicates
  , module Theory.Syntactic.Predicate
  , addPredicate

  -- * Export blocks
  , ExportInfo(..)
  , addExportInfo
  , lookupExportInfo

  -- * Case Tests
  , CaseTest(..)
  , caseTestToPredicate
  , defineCaseTests

  -- * Lemmas
  , LemmaAttribute(..)
  , TraceQuantifier(..)
  , CaseIdentifier
  , Lemma
  , SyntacticLemma
  , ProtoLemma(..)
  , AccLemma(..)
  , lName
  , DiffLemma
  , lDiffName
  , lDiffAttributes
  , lDiffProof
  , lTraceQuantifier
  , lFormula
  , lAttributes
  , lProof
  , lPlaintext
  , aName
  , aAttributes
  , aCaseIdentifiers
  , aCaseTests
  , aFormula
  , unprovenLemma
  , skeletonLemma
  , skeletonDiffLemma
  , isLeftLemma
  , isRightLemma
--   , isBothLemma
  , addLeftLemma
  , addRightLemma
  , expandLemma

  -- * Theories
  , Theory(..)
  , DiffTheory(..)
  , TheoryItem(..)
  , DiffTheoryItem(..)
  , thyName
  , thyInFile
  , thySignature
  , thyTactic
  , thyCache
  , thyItems
  , diffThyName
  , diffThyInFile
  , diffThySignature
  , diffThyCacheLeft
  , diffThyCacheRight
  , diffThyDiffCacheLeft
  , diffThyDiffCacheRight
  , diffThyItems
  , diffTheoryLemmas
  , diffTheorySideLemmas
  , diffTheoryDiffRules
  , diffTheoryDiffLemmas
  , theoryRules
  , theoryLemmas
  , theoryCaseTests
  , theoryFormalComments
  , theoryRestrictions
  , theoryProcesses
  , theoryProcessDefs
  , theoryFunctionTypingInfos
  , theoryBuiltins
  , theoryEquivLemmas
  , theoryDiffEquivLemmas
  , theoryPredicates
  , theoryAccLemmas
  , diffTheoryRestrictions
  , diffTheorySideRestrictions
  , diffTheoryFormalComments
  , addTactic
  , addRestriction
  , addLemma
  , addLemmaAtIndex
  , modifyLemma
  , addAccLemma
  , addCaseTest
  , addRestrictionDiff
  , addLemmaDiff
  , addDiffLemma
  , addHeuristic
  , addDiffHeuristic
  , addDiffTactic
  , removeLemma
  , removeLemmaDiff
  , filterLemma
  , removeDiffLemma
  , lookupLemma
  , lookupLemmaIndex
  , getLemmaPreItems
  , lookupDiffLemma
  , lookupAccLemma
  , lookupCaseTest
  , lookupLemmaDiff
  , addComment
  , addDiffComment
  , addStringComment
  , addFormalComment
  , addFormalCommentDiff
  , filterSide
  , addDefaultDiffLemma
  , addProtoRuleLabel
  , addIntrRuleLabels

  -- ** Open theories
  , OpenTheory
  , OpenTheoryItem
  , OpenTranslatedTheory
  , OpenDiffTheory
  , removeTranslationItems
--  , EitherTheory
  , EitherOpenTheory
  , EitherClosedTheory
  , defaultOpenTheory
  , defaultOpenDiffTheory
  , addProtoRule
  , addProtoDiffRule
  , addOpenProtoRule
  , addOpenProtoDiffRule
  , applyPartialEvaluation
  , applyPartialEvaluationDiff
  , addIntrRuleACsAfterTranslate
  , addIntrRuleACs
  , addIntrRuleACsDiffBoth
  , addIntrRuleACsDiffBothDiff
  , addIntrRuleACsDiffAll
  , normalizeTheory

  -- ** Closed theories
  , ClosedTheory
  , ClosedDiffTheory
  , ClosedRuleCache(..) -- FIXME: this is only exported for the Binary instances
  , closeTheory
  , closeTheoryWithMaude
  , closeDiffTheory
  , closeDiffTheoryWithMaude
  , openTheory
  , openTranslatedTheory
  , openDiffTheory

  , ClosedProtoRule(..)
  , OpenProtoRule(..)
  , oprRuleE
  , oprRuleAC
  , cprRuleE
  , cprRuleAC
  , DiffProtoRule(..)
  , dprRule
  , dprLeftRight
  , unfoldRuleVariants

  , getLemmas
  , getEitherLemmas
  , getDiffLemmas
  , getIntrVariants
  , getIntrVariantsDiff
  , getProtoRuleEs
  , getProtoRuleEsDiff
  , getProofContext
  , getProofContextDiff
  , getDiffProofContext
  , getClassifiedRules
  , getDiffClassifiedRules
  , getInjectiveFactInsts
  , getDiffInjectiveFactInsts
  , getLeftProtoRule
  , getRightProtoRule

  , getSource
  , getDiffSource
  -- ** Proving
  , ProofSkeleton
  , DiffProofSkeleton
  , proveTheory
  , proveDiffTheory

  -- ** Lemma references
  , lookupLemmaProof
  , modifyLemmaProof
  , lookupLemmaProofDiff
  , modifyLemmaProofDiff
  , lookupDiffLemmaProof
  , modifyDiffLemmaProof

  -- * Pretty printing
  , prettyTheory
  , prettyLemmaName
  , prettyRestriction
  , prettyLemma
  , prettyDiffLemmaName
  , prettyClosedTheory
  , prettyClosedDiffTheory
  , prettyOpenTheory
  , prettyOpenTranslatedTheory
  , prettyOpenDiffTheory
  , prettyMacros

  , prettyOpenProtoRule
  , prettyDiffRule

  , prettyClosedSummary
  , prettyClosedDiffSummary

  , prettyTraceQuantifier

  , prettyProcess
  , prettyProcessDef

  -- * Convenience exports
  , module Theory.Model
  , module Theory.Proof
  , module Pretty


  ) where

import ClosedTheory
import Items.ExportInfo
import OpenTheory
import Pretty
import Prover
import Theory.Model
import Theory.Proof
import Theory.Syntactic.Predicate
import TheoryObject
