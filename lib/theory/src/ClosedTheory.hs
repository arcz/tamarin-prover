module ClosedTheory where

import Control.Arrow ((&&&))
import Control.Monad (guard)

import Data.Bifunctor (second)
import Data.Monoid (Sum(..))
import Data.Set qualified as S

import Lemma
import Rule
import Safe
import Theory.Model
import Theory.Proof
import Theory.Text.Pretty
import Theory.Tools.InjectiveFactInstances
import TheoryObject
import Term.Macro
import OpenTheory
import Pretty

------------------------------------------------------------------------------
-- Closed theory querying / construction / modification
------------------------------------------------------------------------------

-- | Closed theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedTheory =
    Theory SignatureWithMaude ClosedRuleCache ClosedProtoRule IncrementalProof ()

-- | Closed Diff theories can be proven. Invariants:
--     1. Lemma names are unique
--     2. All proof steps with annotated sequents are sound with respect to the
--        closed rule set of the theory.
--     3. Maude is running under the given handle.
type ClosedDiffTheory =
    DiffTheory SignatureWithMaude ClosedRuleCache DiffProtoRule ClosedProtoRule IncrementalDiffProof IncrementalProof

-- | Either Therories can be Either a normal or a diff theory
type EitherClosedTheory = Either ClosedTheory ClosedDiffTheory

-- querying
-----------

-- | All lemmas.
getLemmas :: ClosedTheory -> [Lemma IncrementalProof]
getLemmas = theoryLemmas

-- | All diff lemmas.
getDiffLemmas :: ClosedDiffTheory -> [DiffLemma IncrementalDiffProof]
getDiffLemmas = diffTheoryDiffLemmas

-- | All side lemmas.
getEitherLemmas :: ClosedDiffTheory -> [(Side, Lemma IncrementalProof)]
getEitherLemmas = diffTheoryLemmas

-- | The variants of the intruder rules.
getIntrVariants :: ClosedTheory -> [IntrRuleAC]
getIntrVariants = intruderRules . (._thyCache._crcRules)

-- | The variants of the intruder rules.
getIntrVariantsDiff :: Side -> ClosedDiffTheory -> [IntrRuleAC]
getIntrVariantsDiff s
  | s == LHS  = intruderRules . (._diffThyCacheLeft._crcRules)
  | s == RHS  = intruderRules . (._diffThyCacheRight._crcRules)
  | otherwise = error "The Side MUST always be LHS or RHS."

-- | All protocol rules modulo E.
getProtoRuleEs :: ClosedTheory -> [ProtoRuleE]
-- we remove duplicates if they exist due to variant unfolding
getProtoRuleEs = S.toList . S.fromList . map ((._oprRuleE) . openProtoRule) . theoryRules

-- | All protocol rules modulo E.
getProtoRuleEsDiff :: Side -> ClosedDiffTheory -> [ProtoRuleE]
-- we remove duplicates if they exist due to variant unfolding
getProtoRuleEsDiff s = S.toList . S.fromList . map ((._oprRuleE) . openProtoRule) . diffTheorySideRules s

-- | Get the proof context for a lemma of the closed theory.
getProofContext :: Lemma a -> ClosedTheory -> ProofContext
getProofContext l thy = ProofContext
    thy._thySignature
    thy._thyCache._crcRules
    thy._thyCache._crcInjectiveFactInsts
    kind
    (cases thy._thyCache)
    inductionHint
    specifiedHeuristic
    specifiedTactic
    (toSystemTraceQuantifier l._lTraceQuantifier)
    l._lName
    [ h | HideLemma h <- l._lAttributes]
    thy._thyOptions._verboseOption
    False
    (all isSubtermRule  $ filter isDestrRule $ intruderRules thy._thyCache._crcRules)
    (any isConstantRule $ filter isDestrRule $ intruderRules thy._thyCache._crcRules)
    thy._thyIsSapic
  where
    kind    = lemmaSourceKind l
    cases   = case kind of RawSource     -> (._crcRawSources)
                           RefinedSource -> (._crcRefinedSources)
    inductionHint
      | any (`elem` [SourceLemma, InvariantLemma]) l._lAttributes = UseInduction
      | otherwise                                                 = AvoidInduction

    -- Heuristic specified for the lemma > globally specified heuristic > default heuristic
    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case thy._thyHeuristic of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = headMay [Heuristic gr | LemmaHeuristic gr <- l._lAttributes]

    -- Tactic specified for the lemma
    specifiedTactic = case lattr of
        [] -> Nothing
        _  -> Just lattr
      where
        lattr = thy._thyTactic

-- | Get the proof context for a lemma of the closed theory.
getProofContextDiff :: Side -> Lemma a -> ClosedDiffTheory -> ProofContext
getProofContextDiff s l thy = case s of
  LHS ->
    ProofContext
      thy._diffThySignature
      thy._diffThyCacheLeft._crcRules
      thy._diffThyCacheLeft._crcInjectiveFactInsts
      kind
      (cases thy._diffThyCacheLeft)
      inductionHint
      specifiedHeuristic
      specifiedTactic
      (toSystemTraceQuantifier l._lTraceQuantifier)
      l._lName
      [ h | HideLemma h <- l._lAttributes]
      thy._diffThyOptions._verboseOption
      False
      (all isSubtermRule  $ filter isDestrRule $ intruderRules thy._diffThyCacheLeft._crcRules)
      (any isConstantRule $ filter isDestrRule $ intruderRules thy._diffThyCacheLeft._crcRules)
      thy._diffThyIsSapic
  RHS ->
    ProofContext
      thy._diffThySignature
      thy._diffThyCacheRight._crcRules
      thy._diffThyCacheRight._crcInjectiveFactInsts
      kind
      (cases thy._diffThyCacheRight)
      inductionHint
      specifiedHeuristic
      specifiedTactic
      (toSystemTraceQuantifier l._lTraceQuantifier)
      l._lName
      [ h | HideLemma h <- l._lAttributes]
      thy._diffThyOptions._verboseOption
      False
      (all isSubtermRule  $ filter isDestrRule $ intruderRules thy._diffThyCacheRight._crcRules)
      (any isConstantRule $ filter isDestrRule $ intruderRules thy._diffThyCacheRight._crcRules)
      thy._diffThyIsSapic
  where
    kind    = lemmaSourceKind l
    cases   = case kind of RawSource     -> (._crcRawSources)
                           RefinedSource -> (._crcRefinedSources)
    inductionHint
      | any (`elem` [SourceLemma, InvariantLemma]) l._lAttributes = UseInduction
      | otherwise                                                 = AvoidInduction
    -- Heuristic specified for the lemma > globally specified heuristic > default heuristic
    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case thy._diffThyHeuristic of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = headMay [Heuristic gr | LemmaHeuristic gr <- l._lAttributes]

    specifiedTactic = case lattr of
        [] -> Nothing
        _  -> Just lattr
      where
        lattr = thy._diffThyTactic

-- | Get the proof context for a diff lemma of the closed theory.
getDiffProofContext :: DiffLemma a -> ClosedDiffTheory -> DiffProofContext
getDiffProofContext l thy = DiffProofContext (proofContext LHS) (proofContext RHS)
    ((._dprRule) <$> diffTheoryDiffRules thy) thy._diffThyDiffCacheLeft._crcRules._crConstruct
    thy._diffThyDiffCacheLeft._crcRules._crDestruct
    ((LHS, restrictionsLeft):[(RHS, restrictionsRight)]) gatherReusableLemmas
  where
    items = thy._diffThyItems
    restrictionsLeft  = do EitherRestrictionItem (LHS, rstr) <- items
                           pure $ formulaToGuarded_ rstr._rstrFormula
    restrictionsRight = do EitherRestrictionItem (RHS, rstr) <- items
                           pure $ formulaToGuarded_ rstr._rstrFormula
    gatherReusableLemmas = do
        EitherLemmaItem (s, lem) <- items
        guard $    lemmaSourceKind lem <= RefinedSource
                && ReuseDiffLemma `elem` lem._lAttributes
                && AllTraces == lem._lTraceQuantifier
        pure (s, formulaToGuarded_ lem._lFormula)
    proofContext s   = case s of
        LHS -> ProofContext
            thy._diffThySignature
            thy._diffThyDiffCacheLeft._crcRules
            thy._diffThyDiffCacheLeft._crcInjectiveFactInsts
            RefinedSource
            thy._diffThyDiffCacheLeft._crcRefinedSources
            AvoidInduction
            specifiedHeuristic
            specifiedTactic
            ExistsNoTrace
            l._lDiffName
            [ h | HideLemma h <- l._lDiffAttributes ]
            thy._diffThyOptions._verboseOption
            True
            (all isSubtermRule  $ filter isDestrRule $ intruderRules thy._diffThyCacheLeft._crcRules)
            (any isConstantRule $ filter isDestrRule $ intruderRules thy._diffThyCacheLeft._crcRules)
            thy._diffThyIsSapic
        RHS -> ProofContext
            thy._diffThySignature
            thy._diffThyDiffCacheRight._crcRules
            thy._diffThyDiffCacheRight._crcInjectiveFactInsts
            RefinedSource
            thy._diffThyDiffCacheRight._crcRefinedSources
            AvoidInduction
            specifiedHeuristic
            specifiedTactic
            ExistsNoTrace
            l._lDiffName
            [ h | HideLemma h <- l._lDiffAttributes ]
            thy._diffThyOptions._verboseOption
            True
            (all isSubtermRule  $ filter isDestrRule $ intruderRules thy._diffThyCacheRight._crcRules)
            (any isConstantRule $ filter isDestrRule $ intruderRules thy._diffThyCacheRight._crcRules)
            thy._diffThyIsSapic

    specifiedHeuristic = case lattr of
        Just lh -> Just lh
        Nothing  -> case thy._diffThyHeuristic of
                    [] -> Nothing
                    gh -> Just (Heuristic gh)
      where
        lattr = headMay [Heuristic gr | LemmaHeuristic gr <- l._lDiffAttributes]

    specifiedTactic = case lattr of
        [] -> Nothing
        _  -> Just lattr
      where
        lattr = thy._diffThyTactic

-- | The facts with injective instances in this theory
getInjectiveFactInsts :: ClosedTheory -> S.Set (FactTag, [[MonotonicBehaviour]])
getInjectiveFactInsts thy = thy._thyCache._crcInjectiveFactInsts

-- | The facts with injective instances in this theory
getDiffInjectiveFactInsts :: Side -> Bool -> ClosedDiffTheory -> S.Set (FactTag, [[MonotonicBehaviour]])
getDiffInjectiveFactInsts s isdiff thy = case (s, isdiff) of
  (LHS, False) -> thy._diffThyCacheLeft._crcInjectiveFactInsts
  (RHS, False) -> thy._diffThyCacheRight._crcInjectiveFactInsts
  (LHS, True)  -> thy._diffThyDiffCacheLeft._crcInjectiveFactInsts
  (RHS, True)  -> thy._diffThyDiffCacheRight._crcInjectiveFactInsts

-- | The classified set of rules modulo AC in this theory.
getClassifiedRules :: ClosedTheory -> ClassifiedRules
getClassifiedRules thy = thy._thyCache._crcRules

-- | The classified set of rules modulo AC in this theory.
getDiffClassifiedRules :: Side -> Bool -> ClosedDiffTheory -> ClassifiedRules
getDiffClassifiedRules s isdiff thy = case (s, isdiff) of
  (LHS, False) -> thy._diffThyCacheLeft._crcRules
  (RHS, False) -> thy._diffThyCacheRight._crcRules
  (LHS, True)  -> thy._diffThyDiffCacheLeft._crcRules
  (RHS, True)  -> thy._diffThyDiffCacheRight._crcRules

-- | The precomputed case distinctions.
getSource :: SourceKind -> ClosedTheory -> [Source]
getSource RawSource     = (._thyCache._crcRawSources)
getSource RefinedSource = (._thyCache._crcRefinedSources)

-- | The precomputed case distinctions.
getDiffSource :: Side -> Bool -> SourceKind -> ClosedDiffTheory -> [Source]
getDiffSource LHS False RawSource     = (._diffThyCacheLeft._crcRawSources)
getDiffSource RHS False RawSource     = (._diffThyCacheRight._crcRawSources)
getDiffSource LHS False RefinedSource = (._diffThyCacheLeft._crcRefinedSources)
getDiffSource RHS False RefinedSource = (._diffThyCacheRight._crcRefinedSources)
getDiffSource LHS True  RawSource     = (._diffThyDiffCacheLeft._crcRawSources)
getDiffSource RHS True  RawSource     = (._diffThyDiffCacheRight._crcRawSources)
getDiffSource LHS True  RefinedSource = (._diffThyDiffCacheLeft._crcRefinedSources)
getDiffSource RHS True  RefinedSource = (._diffThyDiffCacheRight._crcRefinedSources)

-- construction
---------------

-- | Close a protocol rule; i.e., compute AC variant and source assertion
-- soundness sequent, if required.
closeEitherProtoRule :: MaudeHandle -> (Side, OpenProtoRule) -> (Side, [ClosedProtoRule])
closeEitherProtoRule hnd (s, ruE) = (s, closeProtoRule hnd [] ruE)

-- | Apply macro to a diff protocol rule.
applyMacroInDiffProtoRule :: [Macro]-> DiffProtoRule -> DiffProtoRule
applyMacroInDiffProtoRule mcs (DiffProtoRule ruE sides) = DiffProtoRule (applyMacroInRule mcs ruE) sides

-- | Apply macro to an open protocol rule.
applyMacroInProtoRule :: [Macro]-> OpenProtoRule -> OpenProtoRule
applyMacroInProtoRule mcs (OpenProtoRule ruE variants) = OpenProtoRule (applyMacroInRule mcs ruE) variants


-- -- | Convert a lemma to the corresponding guarded formula.
-- lemmaToGuarded :: Lemma p -> Maybe LNGuarded
-- lemmaToGuarded lem =


-- | Pretty print an closed rule.
prettyClosedProtoRule :: HighlightDocument d => ClosedProtoRule -> d
prettyClosedProtoRule cru =
  if isTrivialProtoVariantAC ruAC ruE then
  -- We have a rule that only has one trivial variant, and without added annotations
  -- Hence showing the initial rule modulo E
    (prettyProtoRuleE ruE) $--$
    (nest 2 $ prettyLoopBreakers ruAC._rInfo $-$
     multiComment_ ["has exactly the trivial AC variant"])
  else
    if ruleName ruAC == ruleName ruE then
      if not (equalUpToTerms ruAC ruE) then
      -- Here we have a rule with added annotations,
      -- hence showing the annotated rule as if it was a rule mod E
      -- note that we can do that, as we unfolded variants
        (prettyProtoRuleACasE ruAC) $--$
        (nest 2 $ prettyLoopBreakers ruAC._rInfo $-$
         multiComment_ ["has exactly the trivial AC variant"])
      else
      -- Here we have a rule with one or multiple variants, but without other annotations
      -- Hence showing the rule mod E with commented variants
        (prettyProtoRuleE ruE) $--$
        (nest 2 $ prettyLoopBreakers ruAC._rInfo $-$
         (multiComment $ prettyProtoRuleAC ruAC))
    else
    -- Here we have a variant of a rule that has multiple variants.
    -- Hence showing only the variant as a rule modulo AC. This should not
    -- normally be used, as it breaks the ability to re-import.
      (prettyProtoRuleAC ruAC) $--$
      (nest 3 $ prettyLoopBreakers ruAC._rInfo $-$
          (multiComment_ ["variant of"]) $-$
          (multiComment $ prettyProtoRuleE ruE)
      )
 where
    ruAC      = cru._cprRuleAC
    ruE       = cru._cprRuleE

-- -- | Pretty print an closed rule.
-- prettyClosedEitherRule :: HighlightDocument d => (Side, ClosedProtoRule) -> d
-- prettyClosedEitherRule (s, cru) =
--     text ((show s) ++ ": ") <>
--     (prettyProtoRuleE ruE) $--$
--     (nest 2 $ prettyLoopBreakers ruAC._rInfo $-$ ppRuleAC)
--   where
--     ruAC = cru._cprRuleAC
--     ruE  = cru._cprRuleE
--     ppRuleAC
--       | isTrivialProtoVariantAC ruAC ruE = multiComment_ ["has exactly the trivial AC variant"]
--       | otherwise                        = multiComment $ prettyProtoRuleAC ruAC

-- | Pretty print a closed theory.
prettyClosedTheory :: HighlightDocument d => ClosedTheory -> d
prettyClosedTheory thy = if containsManualRuleVariants mergedRules
    then
      prettyTheory prettySignatureWithMaude
                       ppInjectiveFactInsts
                       -- (prettyIntrVariantsSection . intruderRules . (._crcRules))
                       prettyOpenProtoRuleAsClosedRule
                       prettyIncrementalProof
                       emptyString
                       thy'
    else
      prettyTheory prettySignatureWithMaude
               ppInjectiveFactInsts
               -- (prettyIntrVariantsSection . intruderRules . (._crcRules))
               prettyClosedProtoRule
               prettyIncrementalProof
               emptyString
               thy
  where
    items = thy._thyItems
    mergedRules = mergeOpenProtoRules $ map (mapTheoryItem openProtoRule id) items
    thy' :: Theory SignatureWithMaude ClosedRuleCache OpenProtoRule IncrementalProof ()
    thy' = Theory
      { _thyName = thy._thyName
      ,_thyInFile = thy._thyInFile
      ,_thyHeuristic = thy._thyHeuristic
      ,_thyTactic = thy._thyTactic
      ,_thySignature = thy._thySignature
      ,_thyCache = thy._thyCache
      ,_thyItems = mergedRules
      ,_thyOptions = thy._thyOptions
      ,_thyIsSapic = thy._thyIsSapic
      }
    ppInjectiveFactInsts crc =
        case S.toList crc._crcInjectiveFactInsts  of
            []   -> emptyDoc
            tags -> multiComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) (map fst tags) ]

-- | Pretty print a closed diff theory.
prettyClosedDiffTheory :: HighlightDocument d => ClosedDiffTheory -> d
prettyClosedDiffTheory thy = if containsManualRuleVariantsDiff mergedRules
    then
      prettyDiffTheory prettySignatureWithMaude
                 ppInjectiveFactInsts
                 -- (prettyIntrVariantsSection . intruderRules . (._crcRules))
                 (const emptyDoc) --prettyClosedEitherRule
                 prettyIncrementalDiffProof
                 prettyIncrementalProof
                 thy'
    else
        prettyDiffTheory prettySignatureWithMaude
                   ppInjectiveFactInsts
                   -- (prettyIntrVariantsSection . intruderRules . (._crcRules))
                   (const emptyDoc) --prettyClosedEitherRule
                   prettyIncrementalDiffProof
                   prettyIncrementalProof
                   thy
  where
    items = thy._diffThyItems
    mergedRules = mergeLeftRightRulesDiff $ mergeOpenProtoRulesDiff $
       map (mapDiffTheoryItem id (second openProtoRule) id id) items
    thy' :: DiffTheory SignatureWithMaude ClosedRuleCache DiffProtoRule OpenProtoRule IncrementalDiffProof IncrementalProof
    thy' = DiffTheory
      { _diffThyName = thy._diffThyName
      , _diffThyInFile = thy._diffThyInFile
      , _diffThyHeuristic = thy._diffThyHeuristic
      , _diffThyTactic = thy._diffThyTactic
      , _diffThySignature = thy._diffThySignature
      , _diffThyCacheLeft = thy._diffThyCacheLeft
      , _diffThyCacheRight = thy._diffThyCacheRight
      , _diffThyDiffCacheLeft = thy._diffThyDiffCacheLeft
      , _diffThyDiffCacheRight = thy._diffThyDiffCacheRight
      , _diffThyItems = mergedRules
      , _diffThyOptions = thy._diffThyOptions
      , _diffThyIsSapic = thy._diffThyIsSapic
      }
    ppInjectiveFactInsts crc =
        case S.toList crc._crcInjectiveFactInsts of
            []   -> emptyDoc
            tags -> multiComment $ sep
                      [ text "looping facts with injective instances:"
                      , nest 2 $ fsepList (text . showFactTagArity) (map fst tags) ]

prettyClosedSummary :: Document d => ClosedTheory -> d
prettyClosedSummary thy =
    vcat lemmaSummaries
  where
    lemmaSummaries = do
        LemmaItem lem  <- thy._thyItems
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary lem._lProof
            quantifier = toSystemTraceQuantifier lem._lTraceQuantifier
            analysisType = parens $ prettyTraceQuantifier lem._lTraceQuantifier
        return $ text lem._lName <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))

prettyClosedDiffSummary :: Document d => ClosedDiffTheory -> d
prettyClosedDiffSummary thy =
    vcat lemmaSummaries $$ vcat diffLemmaSummaries
  where
    lemmaSummaries = do
        EitherLemmaItem (s, lem) <- thy._diffThyItems
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldProof proofStepSummary lem._lProof
            quantifier = toSystemTraceQuantifier lem._lTraceQuantifier
            analysisType = parens $ prettyTraceQuantifier lem._lTraceQuantifier
        return $ text (show s) <-> text ": " <-> text lem._lName <-> analysisType <> colon <->
                 text (showProofStatus quantifier status) <->
                 parens (integer siz <-> text "steps")

    diffLemmaSummaries = do
        DiffLemmaItem lem <- thy._diffThyItems
        -- Note that here we are relying on the invariant that all proof steps
        -- with a 'Just' annotation follow from the application of
        -- 'execProofMethod' to their parent and are valid in the sense that
        -- the application of 'execProofMethod' to their method and constraint
        -- system is guaranteed to succeed.
        --
        -- This is guaranteed initially by 'closeTheory' and is (must be)
        -- maintained by the provers being applied to the theory using
        -- 'modifyLemmaProof' or 'proveTheory'. Note that we could check the
        -- proof right before computing its status. This is however quite
        -- expensive, as it requires recomputing all intermediate constraint
        -- systems.
        --
        -- TODO: The whole consruction seems a bit hacky. Think of a more
        -- principled constrution with better correctness guarantees.
        let (status, Sum siz) = foldDiffProof diffProofStepSummary lem._lDiffProof
        return $ text "DiffLemma: " <-> text lem._lDiffName <-> colon <->
                 text (showDiffProofStatus status) <->
                 parens (integer siz <-> text "steps")

    proofStepSummary = proofStepStatus &&& const (Sum (1::Integer))
    diffProofStepSummary = diffProofStepStatus &&& const (Sum (1::Integer))


-- | Render the results of the precomputations, for --precompute-only
prettyPrecomputation ::  Document d => ClosedTheory -> d
prettyPrecomputation thy = foldr1 ($-$)
    [
      ruleLink
    , reqCasesLink "Raw sources:" RawSource
    , reqCasesLink "Refined sources:" RefinedSource
    ]
  where
    rules          = getClassifiedRules thy
    rulesInfo      = text $ show $ length rules._crProtocol
    casesInfo kind = nCases <> comma <-> text chainInfo
      where
        cases   = getSource kind thy
        nChains = sum $ map (sum . unsolvedChainConstraints) cases
        nCases  = text $ show (length cases) ++ " " ++ "cases"
        chainInfo | nChains == 0 = "deconstructions complete"
                  | otherwise    = show nChains ++ " partial deconstructions left"

    overview n p   = n <-> p
    ruleLinkMsg         = text $ "Multiset rewriting rules" ++
                          (if null (theoryRestrictions thy) then "" else " and restrictions") ++ ":"
    ruleLink            = overview ruleLinkMsg rulesInfo
    reqCasesLink name k = overview (text name) (casesInfo k)


-- | Render the results of the precomputations, for --precompute-only (diff mode)
prettyDiffPrecomputation :: Document d => ClosedDiffTheory -> d
prettyDiffPrecomputation thy = foldr1 ($-$)
    [
      ruleLink LHS False
    , ruleLink RHS False
    , ruleLink LHS True
    , ruleLink RHS True
    , reqCasesLink LHS "LHS: Raw sources:"            RawSource False
    , reqCasesLink RHS "RHS: Raw sources:"            RawSource False
    , reqCasesLink LHS "LHS: Raw sources [Diff]:"     RawSource True
    , reqCasesLink RHS "RHS: Raw sources [Diff]:"     RawSource True
    , reqCasesLink LHS "LHS: Refined sources:"        RefinedSource   False
    , reqCasesLink RHS "RHS: Refined sources:"        RefinedSource   False
    , reqCasesLink LHS "LHS: Refined sources [Diff]:" RefinedSource   True
    , reqCasesLink RHS "RHS: Refined sources [Diff]:" RefinedSource   True
    ]
  where
    rules s isdiff     = getDiffClassifiedRules s isdiff thy
    rulesInfo s isdiff = text $ show $ length (rules s isdiff)._crProtocol
    casesInfo s kind isdiff = nCases <> comma <-> text chainInfo
      where
        cases   = getDiffSource s isdiff kind thy
        nChains = sum $ map (sum . unsolvedChainConstraints) cases
        nCases  = text $ show (length cases) ++ " " ++ "cases"
        chainInfo | nChains == 0 = "deconstructions complete"
                  | otherwise    = show nChains ++ " partial deconstructions left"

    overview n p   = n <-> p
    ruleLink s isdiff    = overview (ruleLinkMsg s isdiff) (rulesInfo s isdiff)
    ruleLinkMsg s isdiff = text $ show s ++ ": Multiset rewriting rules" ++
                           (if null (diffTheorySideRestrictions s thy) then "" else " and restrictions") ++ (if isdiff then " [Diff]" else "") ++ ":"

    reqCasesLink s name k isdiff = overview (text name) (casesInfo s k isdiff)
