{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns               #-}
-- |
-- Copyright   : (c) 2019 Charlie Jacomme and Robert Künnemann
-- License     : GPL v3 (see LICENSE)
--
-- Maintainer  : Robert Künnemann <robert@kunnemann.de>
-- Portability : GHC only
--
-- Translation from Sapic processes to Proverif

module Export (
    prettyProVerifTheory

) where

import         Term.Builtin.Signature
import         Term.Builtin.Rules
import         Term.SubtermRule


import         Theory
import         Theory.Sapic
import         Text.PrettyPrint.Class


import qualified Data.Set as S
import qualified Data.Label as L
import Data.List as List
import qualified Data.ByteString.Char8 as BC


template headers queries process =
  (vcat headers)
  $$
  (vcat queries)
  $$
  (text "process")
  $$
  (nest 4 process)

-- Proverif Headers need to be ordered, and declared only once. We order them by type, and will update a set of headers.
data ProverifHeader =
  Sym String
  | Fun String
  | Eq String
  -- | Type String -- will  be used to define types
  deriving (Ord, Show, Eq)

-- We declare some base headers. Notably, we need a dedicated attacker channel.
base_headers = S.fromList [
  Sym ("free attacker_channel:channel.")
  ]
  
-- The corresponding headers for each Tamarin builtin. If the functions of the builtin are inside the signature, we add the corresponding headers to the output.
builtins = map (\(x,y) -> (x, S.fromList y)) [
  (hashFunSig, [Fun "fun hash(bitstring):bitstring."] ),
  (signatureFunSig, [
      Fun "fun sign(bitstring,bitstring):bitstring.",
      Fun "fun pk(bitstring):bitstring.",
      Eq "reduc forall m:bitstring,sk:bitstring; verify(sign(m,sk),m,pk(sk)) = true."
      ]
  ),
  (S.fromList [ expSym, oneSym], [
      Sym "const g:bitstring.",
      Fun "fun exp(bitstring,bitstring):bitstring",
      Eq "equation forall a:bitstring,b:bitstring; exp( exp(g,a),b) = exp(exp(g,b),a)."
      ]
  ),
  (symEncFunSig, [
      Sym "type skey.",
      Fun "fun senc(bitstring,skey):bitstring.",
      Eq "reduc forall m:bitstring,sk:skey; sdec(senc(m,sk),sk) = m."]
  ),
  (pairFunSig,  [Eq "reduc forall a:bitstring,b:bitstring; fst((a,b))=a.",
  Eq  "reduc forall a:bitstring,b:bitstring; snd((a,b))=b."]
  )
  ]


builtins_rules = foldl S.union S.empty [pairRules, symEncRules, asymEncRules, signatureRules]
  
-- utility function, generate a sequence of type arguments, for events and function declaration
make_args :: Int -> String
make_args 0 = ""
make_args 1 = "bitstring"
make_args n = "bitstring,"++(make_args (n-1))

-- main pp function  
prettyProVerifTheory :: OpenTheory -> Doc
prettyProVerifTheory thy =  template hd [] proc
  where hd = attribHeaders $ S.toList (base_headers `S.union` (loadHeaders thy) `S.union` prochd)
        (proc,prochd) = loadProc thy

-- pretty print an LNTerm, collecting the constant that need to be declared
-- a boolean b allows to add types to variables (for input bindings)        
pppSapicTerm :: Bool -> SapicTerm -> (Doc, S.Set ProverifHeader)
pppSapicTerm b t = (ppTerm t, getHdTerm t)
  where
    ppTerm t = case viewTerm t of
        Lit  (Con (Name FreshName n))             -> text $ show n
        Lit  (Con (Name PubName n))               -> text $ show n
        Lit  (t)              | b                 -> text $ show t
        Lit  (Var (SapicLVar n t))                -> text $ show n
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq s)      _       | isPair t -> ppTerms ", " 1 "(" ")" (split t)
        FApp (NoEq (f, _)) []                     -> text (BC.unpack f)
        FApp (NoEq (f, _)) ts                     -> ppFun f ts
        FApp (C EMap)      ts                     -> ppFun emapSymString ts
        FApp List          ts                     -> ppFun (BC.pack"LIST") ts
               
    ppACOp Mult  = "*"
    ppACOp Union = "+"
    ppACOp Xor   = "⊕"
    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts
    split (viewTerm2 -> FPair t1 t2) = t1 : split t2
    split t                          = [t]
  
    ppFun f ts =
      text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
    getHdTerm t =  case viewTerm t of
        Lit  (Con (Name PubName n))               -> S.singleton   (Sym ("free " ++ show n ++":bitstring."))
        Lit  (t)                                  -> S.empty
        FApp _ ts                     -> foldl (\x y -> x `S.union` (getHdTerm y)) S.empty ts

ppSapicTerm :: SapicTerm -> (Doc, S.Set ProverifHeader)
ppSapicTerm = pppSapicTerm False

-- TODO: we should generalise functionality so pppSapicTerm and pppLNTerm share
-- the code they have in common
pppLNTerm :: Bool -> LNTerm -> (Doc, S.Set ProverifHeader)
pppLNTerm b t = (ppTerm t, getHdTerm t)
  where
    ppTerm t = case viewTerm t of
        Lit  (Con (Name FreshName n))             -> text $ show n
        Lit  (Con (Name PubName n))               -> text $ show n
        Lit  (t)              | b                 -> text $ show t <> ":bitstring"                    
        Lit  (t)                                  -> text $ show t
        FApp (AC o)        ts                     -> ppTerms (ppACOp o) 1 "(" ")" ts
        FApp (NoEq s)      [t1,t2] | s == expSym  -> ppTerm t1 <> text "^" <> ppTerm t2
        FApp (NoEq s)      [t1,t2] | s == diffSym -> text "diff" <> text "(" <> ppTerm t1 <> text ", " <> ppTerm t2 <> text ")"
        FApp (NoEq s)      _       | isPair t -> ppTerms ", " 1 "(" ")" (split t)
        FApp (NoEq (f, _)) []                     -> text (BC.unpack f)
        FApp (NoEq (f, _)) ts                     -> ppFun f ts
        FApp (C EMap)      ts                     -> ppFun emapSymString ts
        FApp List          ts                     -> ppFun (BC.pack"LIST") ts
               
    ppACOp Mult  = "*"
    ppACOp Union = "+"
    ppACOp Xor   = "⊕"
    ppTerms sepa n lead finish ts =
        fcat . (text lead :) . (++[text finish]) .
            map (nest n) . punctuate (text sepa) . map ppTerm $ ts
    split (viewTerm2 -> FPair t1 t2) = t1 : split t2
    split t                          = [t]
  
    ppFun f ts =
      text (BC.unpack f ++"(") <> fsep (punctuate comma (map ppTerm ts)) <> text ")"
    getHdTerm t =  case viewTerm t of
        Lit  (Con (Name PubName n))               -> S.singleton   (Sym ("free " ++ show n ++":bitstring."))
        Lit  (t)                                  -> S.empty
        FApp _ ts                     -> foldl (\x y -> x `S.union` (getHdTerm y)) S.empty ts

ppLNTerm :: LNTerm -> (Doc, S.Set ProverifHeader)
ppLNTerm = pppLNTerm False

-- pretty print a Fact, collecting the constant that need to be declared         
ppFact :: Fact SapicTerm -> (Doc, S.Set ProverifHeader)
ppFact (Fact tag _ ts)
  | factTagArity tag /= length ts = sppFact ("MALFORMED-" ++ show tag) ts
  | otherwise                     = sppFact (showFactTag tag) ts
  where
    sppFact name ts = 
      (nestShort' (name ++ "(") ")" . fsep . punctuate comma $ pts, sh)
      where (pts, shs) = unzip $ map ppSapicTerm ts
            sh = foldl S.union S.empty shs

-- pretty print an Action, collecting the constant and events that need to be declared         
ppAction :: SapicAction -> (Doc, S.Set ProverifHeader)
ppAction (New n) = (text "new " <> (text $ show n), S.empty)
ppAction Rep  = (text "!", S.empty)
ppAction (ChIn (Just t1) t2 )  = (text "in(" <> pt1 <> text "," <> pt2 <> text ")", sh1 `S.union` sh2)
  where (pt1, sh1) = ppSapicTerm t1
        (pt2, sh2) = pppSapicTerm True t2
ppAction (ChIn Nothing t2 )  = (text "in(attacker_channel," <> pt2 <> text ")", sh2)
  where (pt2, sh2) = pppSapicTerm True t2

ppAction (ChOut (Just t1) t2 )  = (text "out(" <> pt1 <> text "," <> pt2 <> text ")", sh1 `S.union` sh2)
  where (pt1, sh1) = ppSapicTerm t1
        (pt2, sh2) = ppSapicTerm t2
ppAction (ChOut Nothing t2 )  = (text "out(attacker_channel," <> pt2 <> text ")", sh2)
  where (pt2, sh2) = ppSapicTerm t2
ppAction (Event (Fact tag m ts) )  = (text "event " <> pa, sh `S.union` (S.singleton (Eq ("event " ++ (showFactTag tag) ++ "(" ++ make_args (length ts) ++ ")."))))
  where (pa, sh) = ppFact (Fact tag m ts)
ppAction _  = (text "Action not supported for translation", S.empty)

ppSapic :: AnProcess ann -> (Doc, S.Set ProverifHeader)
ppSapic (ProcessNull _) = (text "0", S.empty)
ppSapic (ProcessComb Parallel _ pl pr)  = ( (nest 2 (parens ppl)) $$ text "|" $$ (nest 2 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr
ppSapic (ProcessComb NDC _ pl pr)  = ( (nest 4 (parens ppl)) $$ text "+" <> (nest 4 (parens ppr)), pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr

ppSapic (ProcessComb (Cond a)  _ pl (ProcessNull _))  =
  ( text "if " <> pa <> text " then" $$ (nest 4 (parens ppl)), sh `S.union` pshl)
  where (ppl, pshl) = ppSapic pl
        (pa, sh) = ppFact' a
        ppFact' formula@(Ato (Syntactic (Pred f))) = (text "non-predicate conditions not yet supported also not supported ;) ", S.empty )
                                                    --- note though that we can get a printout by converting to LNFormula, like this ppFact (toLNFormula formula)
        ppFact' _                          = (text "non-predicate conditions not yet supported", S.empty)

ppSapic (ProcessComb (CondEq t1 t2)  _ pl (ProcessNull _))  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) , sh1 `S.union` sh2 `S.union` pshl)
                                     where (ppl, pshl) = ppSapic pl
                                           (pt1, sh1) = ppSapicTerm t1
                                           (pt2, sh2) = ppSapicTerm t2 
                                           
-- ppSapic (ProcessComb (Cond a)  _ pl (ProcessNull _))  =
--   ( text "if" <> pa $$ (nest 4 (parens ppl)), sh `S.union` pshl)
--   where (ppl, pshl) = ppSapic pl
--         (pa , sh  ) = ppFact a

ppSapic (ProcessComb (CondEq t1 t2)  _ pl pr)  = ( text "if " <> pt1 <> text "=" <> pt2 <> text " then " $$ (nest 4 (parens ppl)) $$ text "else" <> (nest 4 (parens ppr)), sh1 `S.union` sh2 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr
                                           (pt1, sh1) = ppSapicTerm t1
                                           (pt2, sh2) = ppSapicTerm t2 
   
ppSapic (ProcessComb (Lookup t v )  _ pl pr)  = (text "lookup " <> pt1 <> text " as " <> (text $ show v) $$ (nest 4 (parens ppl)) $$ text "else" <> (nest 4 (parens ppr)), sh1 `S.union` pshl `S.union` pshr)
                                     where (ppl, pshl) = ppSapic pl
                                           (ppr, pshr) = ppSapic pr
                                           (pt1, sh1) = ppSapicTerm t
   

                                           
ppSapic (ProcessAction Rep _ p)  = (text "!" <> parens pp, psh)
                                   where (pp, psh) = ppSapic p
ppSapic  (ProcessAction a _ (ProcessNull _))  = (pa, sh)
                                     where (pa, sh) = ppAction a
ppSapic  (ProcessAction a _ p)  = (pa <> text ";" $$ pp , sh `S.union` psh)
                                     where (pa, sh) = ppAction a
                                           (pp, psh) = ppSapic p

loadProc :: OpenTheory -> (Doc, S.Set ProverifHeader)
loadProc thy = case theoryProcesses thy of
  []  -> (text "", S.empty)
  [p] -> ppSapic p
  ps  -> (text "Multiple sapic processes detected, error", S.empty)

-- Load the proverif headers from the OpenTheory
loadHeaders :: OpenTheory -> S.Set ProverifHeader
loadHeaders thy =
  (S.map  headerOfFunSym funSymsNoBuiltin) `S.union` funSymsBuiltins `S.union` (S.foldl (\x y -> x `S.union` (headersOfRule y)) S.empty sigRules) 
  where sig = (L.get sigpMaudeSig (L.get thySignature thy))
        -- generating headers for function symbols, both for builtins and user defined functions
        sigFunSyms = stFunSyms sig
        funSymsBuiltins = ((foldl (\x (y,z) -> if S.isSubsetOf y sigFunSyms then  x `S.union` z else x )) S.empty builtins)
        funSymsNoBuiltin = sigFunSyms S.\\ ((foldl (\x (y,z) -> x `S.union` y  )) S.empty builtins)
        headerOfFunSym (f,(k,Public)) = Fun (make_str (f,k) ++ ".")
        headerOfFunSym (f,(k,Private)) = Fun ((make_str (f,k))  ++ " [private].")
        make_str (f,k) = "fun " ++ BC.unpack f ++ "(" ++ (make_args k) ++ "):bitstring"
        -- generating headers for equations
        sigRules = stRules sig S.\\ builtins_rules

headersOfRule r = case ctxtStRuleToRRule r of
  (lhs `RRule` rhs) -> (S.singleton hrule)  `S.union` lsh `S.union` rsh          
    where (plhs,lsh) = ppLNTerm lhs 
          (prhs,rsh) = ppLNTerm rhs
          hrule = Eq  ("equation forall " ++
                       make_frees (map show freesr)  ++
                       ";" ++
                       (render $ sep [ nest 2 $ plhs
                           , text "=" <-> prhs ])++".")
          freesr = List.union (frees lhs) (frees rhs)        
          make_frees [] = ""
          make_frees [x] = x ++ ":bitstring"
          make_frees (x:xs) =  x ++ ":bitstring," ++ (make_frees xs)

attribHeaders :: [ProverifHeader] -> [Doc]
attribHeaders hd =
  sym ++ fun ++ eq
  where (eq,fun,sym) = splitHeaders hd
        splitHeaders [] = ([],[],[])
        splitHeaders (x:xs)
          | Sym s <- x = (e1,f1,(text s):s1)
          | Fun s <- x =  (e1,(text s):f1,s1)
          | Eq s <- x =  ((text s):e1,f1,s1)
          where (e1,f1,s1) = splitHeaders xs
          
