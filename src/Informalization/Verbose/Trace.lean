/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Ontology
import Informalization.Core.Routine
import Informalization.Core.Explanation
import Informalization.Core.ProofGraph
import Informalization.Core.Spine
import Informalization.Core.Register
import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
import ConstructiveCryptography.CryptographicAlgebra.Star
import ConstructiveCryptography.Instances.Algebra
import ConstructiveCryptography.Instances.Game
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Game.MBO
import RandomSystems.Game.UntilBad

/-!
# Zero-Cost `Expr.mdata` Trace Markers & Maurer-Voice Proof Decompiler

Provides kernel-transparent `Expr.mdata` tags (`ccVerboseKind`, `ccVerboseLabel`,
`ccVerboseReason`, `ccVerboseRole`, `ccVerboseCount`) emitted by `Informalization.Verbose.Syntax`,
together with a high-priority `ProofGraph.RuleExplainer` (`priority := 500`) registered at
module initialization.

* **Zero trust-base impact:** `Expr.mdata` is ignored by the Lean 4 kernel (`isDefEq`, `inferType`,
  and `#print axioms` remain strictly within `{propext, Classical.choice, Quot.sound}`).
* **1-to-1 structural fidelity:** Preserves `Write`, `Introduce_hybrid`, `Claim`, `Fact`,
  backward `It_suffices_to_show`, `Tightness_sandwich` lower/upper bounds, `Exhibit_simulator`,
  `By_extended_H_technique`, annotated `cc_calc` steps, and `By_CC_routine` compression receipts.
* **CI hygiene lock:** Strictly uses authentic CC literature phrasing (*"attached to the
  $E$-interface"*, *"at the left/right interface"*, *"underlying system $G^{-}$ obtained by
  ignoring the MBO"*) and never emits forbidden Lean-isms.
-/

namespace Informalization.Verbose.Trace

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Routine
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph
open Informalization.Core.Spine
open Informalization.Core.Register

/-! ## 1. `MData` Keys & Wrapper Helpers -/

def ccVerboseKindKey   : Name := `ccVerboseKind
def ccVerboseLabelKey  : Name := `ccVerboseLabel
def ccVerboseReasonKey : Name := `ccVerboseReason
def ccVerboseRoleKey   : Name := `ccVerboseRole
def ccVerboseCountKey  : Name := `ccVerboseCount

/-- Build a `KVMap` carrying Verbose-CC authoring metadata. -/
def mkVerboseMData (kind : String)
    (label? : Option String := none)
    (reason? : Option String := none)
    (role? : Option String := none)
    (count? : Option Nat := none) : MData :=
  let kv : KVMap := ({} : KVMap).setString ccVerboseKindKey kind
  let kv := match label? with | some l => kv.setString ccVerboseLabelKey l | none => kv
  let kv := match reason? with | some r => kv.setString ccVerboseReasonKey r | none => kv
  let kv := match role? with | some rl => kv.setString ccVerboseRoleKey rl | none => kv
  let kv := match count? with | some c => kv.setNat ccVerboseCountKey c | none => kv
  kv

/-- Wrap a kernel proof term with zero-cost `Expr.mdata` trace metadata. -/
def wrapVerboseMData (kind : String) (proof : Expr)
    (label? : Option String := none)
    (reason? : Option String := none)
    (role? : Option String := none)
    (count? : Option Nat := none) : Expr :=
  .mdata (mkVerboseMData kind label? reason? role? count?) proof

def mdataGetString? (kv : MData) (k : Name) : Option String :=
  match kv.find k with
  | some (.ofString s) => if s.isEmpty then none else some s
  | _ => none

def mdataGetNat? (kv : MData) (k : Name) : Option Nat :=
  match kv.find k with
  | some (.ofNat n) => some n
  | _ => none

/-- Peel outer non-verbose Lean `mdata` (such as `noImplicitLambda`) to expose the outermost
Verbose-CC `mdata` annotation, if any. -/
partial def unwrapVerboseMData? : Expr → Option (MData × Expr)
  | .mdata kv inner =>
      if (mdataGetString? kv ccVerboseKindKey).isSome then some (kv, inner)
      else unwrapVerboseMData? inner
  | _ => none

/-- Search inside a step proof term for an annotated `cc_calc_step` reason in $O(\text{DAG})$ time. -/
def findCalcStepReason? (e : Expr) (_fuel : Nat := 16) : Option String :=
  match e.find? fun sub =>
    match sub with
    | .mdata kv _ =>
        mdataGetString? kv ccVerboseKindKey == some "cc_calc_step" &&
          (mdataGetString? kv ccVerboseReasonKey).isSome
    | _ => false with
  | some (.mdata kv _) => mdataGetString? kv ccVerboseReasonKey
  | _ => none

/-- Check whether an expression contains any `cc_calc_step` annotation in $O(\text{DAG})$ time. -/
def hasAnyCalcStepAnnotation (e : Expr) (_fuel : Nat := 24) : Bool :=
  (e.find? fun sub =>
    match sub with
    | .mdata kv _ => mdataGetString? kv ccVerboseKindKey == some "cc_calc_step"
    | _ => false).isSome

/-- Check whether an expression contains any Verbose-CC `mdata` annotation in $O(\text{DAG})$ time. -/
def hasAnyVerboseAnnotation (e : Expr) (_fuel : Nat := 32) : Bool :=
  (e.find? fun sub =>
    match sub with
    | .mdata kv _ => (mdataGetString? kv ccVerboseKindKey).isSome
    | _ => false).isSome

/-- Bounded AST node count (`> limit` stops early) so large combinatorial/arithmetic tactics
(`simp`, `linarith`, `norm_num`) dropped from Verbose-CC are summarized cleanly without `whnf` blowup. -/
partial def exprCountBounded (e : Expr) (limit : Nat := 80) : Nat :=
  let rec go (x : Expr) (rem : Nat) : Nat :=
    if rem == 0 then 0
    else match x with
    | .app f a =>
        let r1 := go f (rem - 1)
        if r1 == 0 then 0 else go a r1
    | .lam _ d b _ =>
        let r1 := go d (rem - 1)
        if r1 == 0 then 0 else go b r1
    | .forallE _ d b _ =>
        let r1 := go d (rem - 1)
        if r1 == 0 then 0 else go b r1
    | .letE _ _ v b _ =>
        let r1 := go v (rem - 1)
        if r1 == 0 then 0 else go b r1
    | .mdata _ i => go i (rem - 1)
    | .proj _ _ s => go s (rem - 1)
    | _ => rem - 1
  limit - go e limit

/-! ## 2. Proof-Term Inspection Helpers -/

private def pickOpener (kind : TransitionKind) : StateRefT DiscourseState MetaM String := do
  let st ← get
  let (op, st') := st.pickOpener kind
  set st'
  return op

private def markStepEmitted : StateRefT DiscourseState MetaM Unit :=
  modify (·.markEmitted)

private def subContextOf (ctx : DecompCtx) : DecompCtx :=
  { ctx with lastFactFVar? := none, factIndex := 0, atRootConclusion := false, isProofStart := false, isClosingGoal := false }

private def visibleMathLengthTex (tex : String) : Nat :=
  let s := tex
    |>.replace "\\mathrm{" "" |>.replace "\\mathsf{" "" |>.replace "\\mathcal{" ""
    |>.replace "\\mathbf{" "" |>.replace "\\mathbb{" "" |>.replace "\\text{" ""
    |>.replace "\\left" "" |>.replace "\\right" ""
    |>.replace "\\!" "" |>.replace "\\," " " |>.replace "\\;" " "
    |>.replace "{" "" |>.replace "}" ""
  s.trimAscii.toString.length

private def hasSubstantialMath (tex : String) : Bool :=
  visibleMathLengthTex tex ≥ 42 ||
    (tex.splitOn " + ").length ≥ 3 ||
    (tex.splitOn "\\sum").length > 1 ||
    (tex.splitOn "\\frac").length > 1

private def endsWithDisplayMath (inls : Array Inline) : Bool :=
  match inls.back? with
  | some (.displayMath _ _) => true
  | _ => false

private def appendSentencePunct (inls : Array Inline) (punct : String := ".") : Array Inline :=
  if punct.isEmpty || endsWithDisplayMath inls then inls
  else
    match inls.back? with
    | some (.text s) =>
        let t := s.trimAsciiEnd.toString
        if t.endsWith "." || t.endsWith "!" || t.endsWith "?" || t.endsWith ":" then inls
        else if t.endsWith "," || t.endsWith ";" then
          let base := (t.dropEnd 1).toString.trimAsciiEnd.toString
          inls.pop.push (.text (base ++ punct))
        else inls.push (.text punct)
    | _ => inls.push (.text punct)

private def ppCleanType (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty

private def isAtomicAliasVal (e : Expr) : Bool :=
  let c := e.consumeMData
  let isLit := match c with | .lit _ => true | _ => false
  c.isFVar || c.isConst || isLit || c.isAppOfArity ``OfNat.ofNat 3

private def extendTblWithLocalAlias (tbl : SymbolTable) (fv val : Expr)
    (symTex _valTex : String) : MetaM SymbolTable := do
  let tbl0 := tbl.withExprAlias fv symTex
  if isAtomicAliasVal val then
    return tbl0
  let cVal := val.consumeMData
  if tbl0.exprAliases.any fun (k, _) => k == cVal then
    return tbl0
  let tbl1 ← tbl0.withNormalizedExprAlias val symTex
  return tbl1.withExprAlias cVal symTex

private def inlineCollectText (inls : Array Inline) : String :=
  String.join (inls.toList.map fun
    | .text s => s
    | .emph s => s
    | _ => " ")

private def isClauseText (raw0 : String) : Bool :=
  let low := raw0.trimAscii.toString.toLower
  if low.startsWith "that " then
    false
  else
    let starters := [
      "there exists", "there is", "there are",
      "for every", "for all", "for each",
      "if ", "every ", "each ", "no ", "any ",
      "we have", "it holds", "such "
    ]
    let verbs := [
      " satisfies ", " is ", " are ", " constructs ", " holds", " does not hold",
      " can be ", " equals ", " distinguishes ", " wins "
    ]
    starters.any (fun p => low.startsWith p) ||
      verbs.any (fun v => (low.splitOn v).length > 1)

private def isClauseProseInl (inls : Array Inline) : Bool :=
  isClauseText (inlineCollectText inls)

private def clauseThat (prefixWithoutThat : String) (inls : Array Inline) : Array Inline :=
  if isClauseProseInl inls then
    #[.text s!"{prefixWithoutThat} that "] ++ inls
  else
    #[.text s!"{prefixWithoutThat} "] ++ inls

private def hasGerundLead (low : String) : Bool :=
  [ "multiplying ", "combining ", "dividing ", "summing ", "substituting ",
    "rewriting ", "splitting ", "expanding ", "taking ", "applying ",
    "absorbing ", "composing ", "comparing ", "bounding "
  ].any fun g => low.startsWith g

private def hasFiniteVerbPhrase (low : String) : Bool :=
  let padded := " " ++ low ++ " "
  [ " gives ", " give ", " show ", " shows ", " yield ", " yields ",
    " establish ", " establishes ", " implies ", " imply ", " ensure ", " ensures ",
    " holds ", " hold ", " follows ", " follow "
  ].any fun v => (padded.splitOn v).length > 1

private def trimTrailingPeriodLocal (s : String) : String :=
  let t := s.trimAscii.toString
  if t.endsWith "." || t.endsWith "," then (t.dropEnd 1).trimAscii.toString else t

private def sanitizeReasonCore (raw0 : String) (cap : Bool) : String :=
  let raw := trimTrailingPeriodLocal (raw0.trimAscii.toString.replace "⊥" "a contradiction")
  let low := raw.toLower
  let stripped :=
    if low.startsWith "by by " || low.startsWith "by from " || low.startsWith "by since " then
      (raw.drop 3).trimAscii.toString
    else if low.startsWith "applying by " || low.startsWith "applying from " then
      (raw.drop 9).trimAscii.toString
    else if low.startsWith "applying multiplying " || low.startsWith "applying combining " ||
        low.startsWith "applying dividing " || low.startsWith "applying summing " ||
        low.startsWith "applying substituting " || low.startsWith "applying rewriting " ||
        low.startsWith "applying splitting " then
      (raw.drop 9).trimAscii.toString
    else
      raw
  let sLow := stripped.toLower
  let out :=
    if sLow.startsWith "by " || sLow.startsWith "since " || sLow.startsWith "because " ||
       sLow.startsWith "from " || sLow.startsWith "under " || sLow.startsWith "using " ||
       sLow.startsWith "via " || hasGerundLead sLow then
      stripped
    else if hasFiniteVerbPhrase sLow then
      s!"since {lowercaseFirst stripped}"
    else
      s!"by {stripped}"
  if cap then capitalizeFirst out else out

private partial def findOuterByLeafMData? : Expr → Option (String × String × Expr)
  | e@(.mdata kv inner) =>
      if let some res := unwrapByLeafMData? e then
        some res
      else if (mdataGetString? kv ccVerboseKindKey).isSome then
        none
      else
        findOuterByLeafMData? inner
  | _ => none

private def formatLeafSummaryProse (raw0 : String) : Array Inline :=
  let clean := trimTrailingPeriodLocal (raw0.trimAscii.toString.replace "⊥" "a contradiction")
  if clean.isEmpty || clean.toLower == "routine calculation" then
    #[.text "This follows by a routine calculation."]
  else
    let lead := sanitizeReasonCore clean true
    parseProseWithMath s!"{lead}, this holds."

private def parsePaperReductionLines (body : String) : Array PseudocodeLine := Id.run do
  let norm := (body.replace "\r\n" "\n").replace "\r" "\n"
  let rawLines := norm.splitOn "\n"
  let mut out : Array PseudocodeLine := #[]
  for raw in rawLines do
    let trimmed := raw.trimAscii.toString
    if !trimmed.isEmpty then
      let indentChars := (raw.toList.takeWhile (· == ' ')).length
      let indentLvl := indentChars / 2
      out := out.push { indent := indentLvl, inlines := parseProseWithMath trimmed }
  return out

private def formatPropSentence (tbl : SymbolTable) (prop : Expr) (punct : String := ".") :
    MetaM (Array Inline) := do
  if prop.consumeMData.isConstOf ``False then
    return #[.text ("a contradiction" ++ punct)]
  let inls0 ← renderProposition tbl prop
  let inls1 := inls0.map fun
    | .text s => .text (s.replace "⊥" "a contradiction")
    | other => other
  let inls := ensureSymbolicPredClause inls1
  if !inls.isEmpty then
    match inls[inls.size - 1]! with
    | .inlineMath tex =>
        if hasSubstantialMath tex then
          return inls.set! (inls.size - 1) (.displayMath tex punct)
    | .displayMath tex p =>
        return inls.set! (inls.size - 1) (.displayMath tex (if p.isEmpty then punct else p))
    | _ => pure ()
  return appendSentencePunct inls punct

/-- Search an elaborated expression for an entity matching `label?` (or a semantic type
predicate) and render it through `exprToLatex ... tbl` so theorem-local `With notation` and
module `informal_symbol` aliases (`\sigma`, `D`) take precedence over raw tactic labels. -/
private partial def findEntityLatex? (tbl : SymbolTable) (e : Expr) (label? : Option String)
    (matchTy : Expr → MetaM Bool) (fuel : Nat := 12) : MetaM (Option String) := do
  let rec visit (cur : Expr) (n : Nat) : MetaM (Option String) := do
    if n == 0 then return none
    let c := cur.consumeMData
    if let some lbl := label? then
      let matchesLbl : Bool ← match c with
        | .const cn _ => pure (cn.toString == lbl || shortConstName cn == lbl)
        | .fvar fvid => do
            try
              let d ← fvid.getDecl
              pure (d.userName.toString == lbl)
            catch _ => pure false
        | _ => pure false
      if matchesLbl then
        return some (← exprToLatex c tbl)
    if !c.hasLooseBVars then
      try
        let ty ← inferType c
        if ← matchTy ty then
          return some (← exprToLatex c tbl)
      catch _ => pure ()
    match c with
    | .app .. =>
        let args := c.getAppArgs
        for arg in args.reverse do
          if let some res ← visit arg (n - 1) then
            return some res
        visit c.getAppFn (n - 1)
    | _ => return none
  if let some hit ← visit e fuel then
    return some hit
  if let some lbl := label? then
    for (cn, aliasTex) in tbl.constAliases do
      if cn.toString == lbl || shortConstName cn == lbl then
        return some aliasTex
    let lctx ← getLCtx
    for d in lctx do
      if d.userName.toString == lbl then
        if let some (_, aliasTex) := tbl.exprAliases.reverse.find? (fun (pat, _) =>
            pat.consumeMData == mkFVar d.fvarId) then
          return some aliasTex
  return label?.map formatMathIdent

private def isDistinguisherType (ty : Expr) : MetaM Bool := do
  let t ← normalizeForPresentation ty
  pure (t.isAppOf `SystemAlgebra.TypedDistinguisher ||
        t.isAppOf `SystemAlgebra.Domain.DistinguisherBehavior ||
        t.isAppOf `SystemAlgebra.Domain.Distinguisher)

private def renderRoutineSummary (tbl : SymbolTable) (reason? : Option String) (inner : Expr) :
    MetaM (String × Expr) := do
  let defaultSum := "routine constructive-cryptography normalization and algebraic bookkeeping"
  match inner with
  | .app (.lam _ dom body _) witness =>
      if dom.consumeMData == mkConst ``Unit && !body.hasLooseBVar 0 then
        let tmpl := reason?.getD defaultSum
        if (tmpl.splitOn "@@EXPR:").length > 1 || (tmpl.splitOn "@@PROP:").length > 1 then
          let anchors := extractAnchorArray witness
          let (inls, _) ← renderSpineTemplate tbl tmpl anchors
          let mut parts : Array String := #[]
          for inl in inls do
            match inl with
            | .text t => parts := parts.push t
            | .emph t => parts := parts.push s!"*{t}*"
            | .inlineMath tex => parts := parts.push s!"\\({tex}\\)"
            | .displayMath tex p => parts := parts.push s!"\\({tex}\\){p}"
            | .symbol _ d true => parts := parts.push s!"\\({d}\\)"
            | .symbol _ d false => parts := parts.push d
            | .citation l _ => parts := parts.push l
          return ((String.intercalate "" parts.toList).trimAscii.toString, body)
        return (tmpl, body)
      return (reason?.getD defaultSum, inner)
  | _ => return (reason?.getD defaultSum, inner)

private def nonexpandPhrase (inner : Expr) : String :=
  let cs : NameSet := inner.foldConsts (init := {}) fun n acc => acc.insert n
  let hasParallel :=
    cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le ||
    cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le ||
    cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le
  let hasAttach :=
    cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le ||
    cs.contains ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.attach
  if hasAttach && hasParallel then
    "non-expansion under converter attachment and parallel composition"
  else if hasParallel then
    "non-expansion under parallel composition"
  else
    "non-expansion under converter attachment"

private def stripTrailingPeriod (s : String) : String :=
  let t := s.trimAscii.toString
  if t.endsWith "." then (t.dropEnd 1).toString else t

private def startsLowerChar (s : String) : Bool :=
  match s.trimAscii.toString.toList with
  | c :: _ => c.isLower
  | [] => false

private def formatGameHeading (rawLabel : String) : String :=
  let t := rawLabel.trimAscii.toString
  let lower := t.toLower
  if lower == "g0" || lower == "g_0" || lower == "g₀" || lower == "game0" || lower == "game_0" then "Game 0."
  else if lower == "g1" || lower == "g_1" || lower == "g₁" || lower == "game1" || lower == "game_1" then "Game 1."
  else if lower == "g2" || lower == "g_2" || lower == "g₂" || lower == "game2" || lower == "game_2" then "Game 2."
  else if lower == "g3" || lower == "g_3" || lower == "g₃" || lower == "game3" || lower == "game_3" then "Game 3."
  else if lower == "g4" || lower == "g_4" || lower == "g₄" || lower == "game4" || lower == "game_4" then "Game 4."
  else if lower.startsWith "game" then
    let numPart := (t.drop 4).trimAscii.toString
    let numClean := if numPart.startsWith "_" then (numPart.drop 1).toString else numPart
    if numClean.isEmpty then "Game." else s!"Game {numClean}."
  else if t.endsWith "." then t
  else s!"Game {t}."

private def declTagFromCtx (ctx : DecompCtx) : String :=
  match ctx.seenDecls.toList.head? with
  | some n => n.toString
  | none => "local"

private def registerScopedNotationInspector (declTag sym rhsTex leanTy desc : String)
    (badge : String := "notation") : IO Unit := do
  registerProofNotationInspector {
    key := s!"vcc:{declTag}:{badge}:{sym}"
    display := sym
    kind := .localShorthand s!"{sym} = {rhsTex}" desc
    leanName? := none
    leanType := leanTy
    roleBadge? := some badge
  }

private def mkVerboseStep (ctx : DecompCtx) (id : String) (content : Array Inline)
    (children : Array ProofNode) (targetForGoal : Expr) (origin? : Option String := none)
    (defaultExpanded : Bool := false) :
    StateRefT DiscourseState MetaM ProofNode := do
  let goal ← buildGoalState ctx.tbl targetForGoal
  return .step id content children (some goal) none origin? false defaultExpanded

private partial def collectConsts (e : Expr) (acc : NameSet := {}) (fuel : Nat := 64) : NameSet :=
  if fuel == 0 then acc
  else match e with
  | .const n _ => acc.insert n
  | .app f a => collectConsts a (collectConsts f acc (fuel - 1)) (fuel - 1)
  | .lam _ d b _ => collectConsts b (collectConsts d acc (fuel - 1)) (fuel - 1)
  | .forallE _ d b _ => collectConsts b (collectConsts d acc (fuel - 1)) (fuel - 1)
  | .letE _ t v b _ =>
      collectConsts b (collectConsts v (collectConsts t acc (fuel - 1)) (fuel - 1)) (fuel - 1)
  | .mdata _ inner => collectConsts inner acc (fuel - 1)
  | .proj _ _ s => collectConsts s acc (fuel - 1)
  | _ => acc

/-- Infer a clean Maurer-voice justification phrase for `It_suffices_to_show` from the checked
reduction body when the author did not provide an explicit string reason. -/
private def inferSufficesReason (env : Environment) (body : Expr) : String :=
  let cs := collectConsts body
  if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le then
    "because converter attachment is non-expanding"
  else if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator then
    "by the simulator characterization of indifferentiability"
  else if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation then
    "by sequential composability of constructions"
  else if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context then
    "by context-insensitivity of constructions"
  else if cs.contains ``ConstructiveCryptography.DistinctionGames.advantage_le_win ||
          cs.contains ``SystemAlgebra.Interface.dist_visible_le ||
          cs.contains ``SystemAlgebra.Interface.game_dist_le then
    "by conditional equivalence"
  else if cs.contains ``SystemAlgebra.RandomSystem.GameEquivalent.abs_decisionProbability_sub_le ||
          cs.contains ``SystemAlgebra.Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent ||
          cs.contains ``SystemAlgebra.RandomSystem.GameEquivalent.transcriptDistance_visible_le then
    "by the fundamental lemma of game playing"
  else if cs.contains ``SystemAlgebra.Interface.distance_le_of_hCoefficient ||
          cs.contains ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le then
    "by the extended H-technique"
  else if cs.contains ``SystemAlgebra.Domain.DistinguisherBehavior.advantage_le_transcriptDistance ||
          cs.contains ``SystemAlgebra.Domain.Distinguisher.advantage_le_transcriptDistance ||
          cs.contains ``ConstructiveCryptography.le_advantageDistance then
    "since $\\Delta$ bounds every compatible distinguisher's distinguishing advantage"
  else if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_singleton_iff ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff ||
          cs.contains ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff then
    "by the constructive security definition"
  else
    -- Look for any project-domain lemma referenced in the reduction body
    let projName? := cs.toList.find? fun n =>
      !isCoreOrMathlibIn env n && !n.toString.startsWith "ConstructiveCryptography.CryptographicAlgebra.Specification"
    match projName? with
    | some pn => sanitizeReasonCore (humanLemmaLabel env pn) false
    | none => "by the checked reduction step"

/-- Extract the converter argument from a substitution-in-context proof term, if present. -/
private def findConverterArgLatex? (tbl : SymbolTable) (proof : Expr) : MetaM (Option String) := do
  for arg in proof.getAppArgs do
    try
      let ty ← inferType arg
      if ty.isAppOf ``Quiver.Hom || ty.isAppOf `SystemAlgebra.TypedConverter then
        return some (← exprToLatex arg tbl)
    catch _ => pure ()
  return none

/-- Extract the intermediate resource `M` from `(distance_triangle _ M _).trans (add_le_add p1 p2)`. -/
private def extractTriangleData? (proof : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  let args := p.getAppArgs
  if fn.isConstOf ``LE.le.trans && args.size ≥ 2 then
    let pTri := args[args.size - 2]!.consumeMData
    let pAdd := args[args.size - 1]!.consumeMData
    if pTri.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.distance_triangle &&
       pAdd.isAppOf ``add_le_add then
      let triArgs := pTri.getAppArgs
      let addArgs := pAdd.getAppArgs
      if triArgs.size ≥ 2 && addArgs.size ≥ 2 then
        let mid := triArgs[triArgs.size - 2]!
        return some (mid, addArgs[addArgs.size - 2]!, addArgs[addArgs.size - 1]!)
  return none

/-! ## 3. Annotated `cc_calc` Chain Flattener -/

private inductive CalcHopKind
  | exactEq
  | computational
  | statistical
  deriving DecidableEq, BEq

private structure CalcHop where
  kind : CalcHopKind
  lhs : Expr
  rhs : Expr
  relLatex : String
  proof : Expr
  prop : Expr

private def unfoldNonCorePredOnce? (e : Expr) : MetaM (Option Expr) := do
  let env ← getEnv
  match e.getAppFn.consumeMData with
  | .const cn _ =>
      if isCoreOrMathlibIn env cn then return none
      try
        if let some u ← withTransparency .default (Meta.unfoldDefinition? e) then
          if u != e then return some u
      catch _ => pure ()
      let w ← withTransparency .reducible (whnf e)
      if w != e then return some w
      return none
  | _ => return none

private def splitDistLe? (prop : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut cur := prop
  for _ in [0:6] do
    let p ← normalizeForPresentation cur
    if p.isAppOf ``LE.le then
      let args := p.getAppArgs
      if args.size ≥ 2 then
        let lhs ← normalizeForPresentation args[args.size - 2]!
        let rhs := args[args.size - 1]!
        if lhs.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.distance then
          let dArgs := lhs.getAppArgs
          if dArgs.size ≥ 2 then
            return some (dArgs[dArgs.size - 2]!, dArgs[dArgs.size - 1]!, rhs)
    match (← unfoldNonCorePredOnce? cur) with
    | some u => cur := u
    | none =>
        match (← unfoldNonCorePredOnce? p) with
        | some u => cur := u
        | none => return none
  return none

private def splitSubstWithin? (prop : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut cur := prop
  for _ in [0:6] do
    let p ← normalizeForPresentation cur
    if p.isAppOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin then
      let args := p.getAppArgs
      if args.size ≥ 3 then
        return some (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)
    match (← unfoldNonCorePredOnce? cur) with
    | some u => cur := u
    | none =>
        match (← unfoldNonCorePredOnce? p) with
        | some u => cur := u
        | none => return none
  return none

private def splitEqTransport? (proof : Expr) : MetaM (Option (Bool × Expr × Expr)) := do
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  let args := p.getAppArgs
  let some head := fn.constName? | return none
  if (head == ``Eq.mp || head == ``Eq.mpr) && args.size ≥ 2 then
    let eqArg := args[args.size - 2]!.consumeMData
    let inner := args[args.size - 1]!
    if eqArg.isAppOf ``congrArg then
      if let some eqProof := eqArg.getAppArgs.back? then
        let eqTy ← inferType eqProof
        if eqTy.isAppOf ``Eq then
          return some (head == ``Eq.mp, eqProof, inner)
  return none

private def splitStatTri? (proof : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some (_, p1, p2) ← extractTriangleData? proof then
    return some (p1, p2)
  return none

private partial def isReflEqProof (e : Expr) : Bool :=
  let c := e.consumeMData
  let fn := c.getAppFn.consumeMData
  let args := c.getAppArgs
  if fn.isConstOf ``Eq.refl || fn.isConstOf ``rfl then true
  else if fn.isConstOf ``Eq.trans && args.size ≥ 2 then
    isReflEqProof args[args.size - 2]! && isReflEqProof args[args.size - 1]!
  else if fn.isConstOf ``congrArg && args.size ≥ 1 then
    isReflEqProof args.back!
  else false

private partial def flattenVerboseCalc (tbl : SymbolTable) (proof expected : Expr)
    (fuel : Nat := 32) : MetaM (Array CalcHop) := do
  if fuel == 0 then return #[]
  let p := proof.consumeMData
  let fn := p.getAppFn.consumeMData
  if fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.trans then
    let pArgs ← proofValuedArgs p
    if pArgs.size == 2 then
      let (p1, t1) := pArgs[0]!
      let (p2, t2) := pArgs[1]!
      return (← flattenVerboseCalc tbl p1 t1 (fuel - 1)) ++
             (← flattenVerboseCalc tbl p2 t2 (fuel - 1))
  if let some (p1, p2) ← splitStatTri? p then
    let t1 ← inferType p1
    let t2 ← inferType p2
    return (← flattenVerboseCalc tbl p1 t1 (fuel - 1)) ++
           (← flattenVerboseCalc tbl p2 t2 (fuel - 1))
  if let some (isRightJoin, eqProof, inner) ← splitEqTransport? p then
    let eqTy ← inferType eqProof
    let innerTy ← inferType inner
    let innerHops ← flattenVerboseCalc tbl inner innerTy (fuel - 1)
    let mut eqHops : Array CalcHop := #[]
    if let some (_, lhs, rhs) := eqTy.eq? then
      if !isReflEqProof eqProof then
        let lhsN ← normalizeForPresentation lhs
        let rhsN ← normalizeForPresentation rhs
        if lhsN != rhsN then
          let lhsTex ← exprToLatex lhsN tbl
          let rhsTex ← exprToLatex rhsN tbl
          if lhsTex != rhsTex then
            eqHops := #[{ kind := .exactEq, lhs := lhsN, rhs := rhsN, relLatex := "=", proof := eqProof, prop := eqTy }]
    return if isRightJoin then innerHops ++ eqHops else eqHops ++ innerHops
  if (fn.isConstOf ``Eq.mp || fn.isConstOf ``Eq.mpr) && p.getAppArgs.size ≥ 2 then
    let inner := p.getAppArgs.back!
    let innerTy ← inferType inner
    let innerHops ← flattenVerboseCalc tbl inner innerTy (fuel - 1)
    if !innerHops.isEmpty then
      return innerHops
  if let some (err, lhs, rhs) ← splitSubstWithin? expected then
    let isStat :=
      fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance ||
      fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical
    let errTex ← match err.consumeMData with
      | .lam _ _ body _ =>
          if !body.hasLooseBVar 0 then exprToLatex body tbl else exprToLatex err tbl
      | _ => exprToLatex err tbl
    let rel := if isStat then "\\approx_{" ++ errTex ++ "}" else "\\simeq_{" ++ errTex ++ "}"
    return #[{
      kind := if isStat then .statistical else .computational
      lhs, rhs, relLatex := rel, proof := proof, prop := expected
    }]
  if let some (lhs, rhs, eps) ← splitDistLe? expected then
    let epsTex ← exprToLatex eps tbl
    return #[{
      kind := .statistical
      lhs, rhs, relLatex := "\\approx_{" ++ epsTex ++ "}", proof := proof, prop := expected
    }]
  return #[]

private def describeVerboseHopReason (env : Environment) (tbl : SymbolTable) (hop : CalcHop) :
    MetaM (Array Inline) := do
  if let some custom := findCalcStepReason? hop.proof then
    return parseProseWithMath custom
  let fn := hop.proof.getAppFn.consumeMData
  match hop.kind with
  | .exactEq =>
      match fn with
      | .const cn _ =>
          if cn == ``Eq.trans then pure #[.text "by chaining exact system identities"]
          else if cn == ``Eq.symm then pure #[.text "by symmetry of exact system identity"]
          else pure #[.text "by exact identity (", .emph (humanLemmaLabel env cn), .text ")"]
      | .fvar _ => pure #[.text "by the assumed system identity"]
      | _ => pure #[.text "by exact system identity"]
  | .statistical =>
      let cs := collectConsts hop.proof
      let hasAttachLe := cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le
      let hasParallelLe :=
        cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le ||
        cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le ||
        cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le
      match fn with
      | .const cn _ =>
          if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance then
            pure #[.text "by distinguishing advantage bound"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical then
            pure #[.text "by statistical distance bound"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le ||
                  (cn == ``LE.le.trans && hasAttachLe && !hasParallelLe) then
            pure #[.text "by non-expansion under converter attachment"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le ||
                  cn == ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le ||
                  cn == ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le ||
                  (cn == ``LE.le.trans && hasParallelLe && !hasAttachLe) then
            pure #[.text "by non-expansion under parallel composition"]
          else if cn == ``LE.le.trans && hasAttachLe && hasParallelLe then
            pure #[.text "by non-expansion under converter attachment and parallel composition"]
          else if cn == ``le_rfl || cn == ``le_refl || cn == `LE.le.refl then
            pure #[.text "by definition of the distance"]
          else
            let lbl := humanLemmaLabel env cn
            if (lbl.splitOn "bound").length > 1 then
              pure #[.text (sanitizeReasonCore lbl false)]
            else
              let clean := sanitizeReasonCore lbl false
              if clean.startsWith "by " && lbl.toLower == (clean.drop 3).toString.toLower then
                pure #[.text "by distinguishing bound (", .emph lbl, .text ")"]
              else
                pure #[.text clean]
      | _ => pure #[.text "by distinguishing bound"]
  | .computational =>
      match fn with
      | .const cn _ =>
          if cn == ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_context ||
             cn == ``ConstructiveCryptography.AdmissibleDistinguishers.substitutesWithin_attach then
            if let some convTex ← findConverterArgLatex? tbl hop.proof then
              return #[.text "by substituting inside context ", .inlineMath convTex,
                       .text " (absorbing ", .inlineMath convTex, .text " into the distinguisher)"]
            pure #[.text "by substituting inside a converter context"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_distance then
            pure #[.text "by the distinguishing advantage bound"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.of_statistical then
            pure #[.text "by statistical distance bound"]
          else if cn == ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.symm then
            pure #[.text "by symmetry of substitution"]
          else
            pure #[.text "by substitution (", .emph (humanLemmaLabel env cn), .text ")"]
      | .fvar _ => pure #[.text "by the assumed substitution"]
      | _ => pure #[.text "by substitution"]

private def buildAnnotatedCalcChain (ctx : DecompCtx) (decompileChild : DecompileChild)
    (expected proof : Expr) (idPrefix : String) :
    StateRefT DiscourseState MetaM (Option (Array ProofNode)) := do
  let isSubGoal := (← splitSubstWithin? expected).isSome
  let isDistGoal := (← splitDistLe? expected).isSome
  if !isSubGoal && !isDistGoal then return none
  let hops ← flattenVerboseCalc ctx.tbl proof expected
  if hops.size < 2 then return none
  let _ ← pickOpener .elaboration
  let subCtx := subContextOf ctx
  let env ← getEnv
  let mut calcSteps : Array (CalcStep × Array ProofNode) := #[]
  for hop in hops do
    let lhsTex ← exprToLatex hop.lhs ctx.tbl
    let rhsTex ← exprToLatex hop.rhs ctx.tbl
    let reason ← describeVerboseHopReason env ctx.tbl hop
    let subNodes ← do
      -- Unwrap `cc_calc_step` `mdata` so inner `By_CC_routine`, assumptions, and subproofs decompile cleanly
      let rawStep := match unwrapVerboseMData? hop.proof with
        | some (kv, inner) =>
            if mdataGetString? kv ccVerboseKindKey == some "cc_calc_step" then inner else hop.proof
        | none => hop.proof
      if let some fvid := unwrapHypothesisFVar? rawStep then
        let n ← renderHypothesisStep ctx.tbl hop.prop fvid s!"vcc-calc-hyp-{fvid.name}-{calcSteps.size}" (isWrap := true)
        pure #[n]
      else if let some fvid := unwrapHypothesisFVar? hop.proof then
        let n ← renderHypothesisStep ctx.tbl hop.prop fvid s!"vcc-calc-hyp-{fvid.name}-{calcSteps.size}" (isWrap := true)
        pure #[n]
      else if hasAnyVerboseAnnotation rawStep then
        decompileChild subCtx hop.prop rawStep
      else
        match rawStep.getAppFn.consumeMData with
        | .const cn _ =>
            let isTrivialNonExpand :=
              cn == ``LE.le.trans &&
              (collectConsts rawStep).toList.all fun c =>
                isCoreOrMathlibIn env c ||
                c == ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le ||
                c == ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le ||
                c == ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le ||
                c == ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le
            if cn == ``le_rfl || cn == ``le_refl || cn == ``Eq.refl || cn == ``rfl ||
               cn == ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le ||
               isTrivialNonExpand then
              pure #[]
            else
              decompileChild subCtx hop.prop rawStep
        | _ => decompileChild subCtx hop.prop rawStep
    let cs : CalcStep := {
      lhsLatex := lhsTex
      relationLatex := hop.relLatex
      rhsLatex := rhsTex
      reason
      diagramHtml? := none
    }
    calcSteps := calcSteps.push (cs, subNodes)
  let goal ← buildGoalState ctx.tbl expected
  let nPhrase := countPhrase hops.size ⟨"hybrid transition", "hybrid transitions"⟩
  let ledgerText :=
    s!"We proceed through a chain of {nPhrase} and apply the triangle inequality:"
  return some #[.calcChain s!"{idPrefix}-{hops.size}" #[.text ledgerText] calcSteps (some goal)]

/-! ## 4. Extended H-Coefficient Witness Extractor -/

private partial def findHCoeffOfGoodBad? (e : Expr) (fuel : Nat := 16) : Option Expr :=
  if fuel == 0 then none
  else
    let c := e.consumeMData
    if c.getAppFn.consumeMData.isConstOf ``SystemAlgebra.RandomSystem.HCoefficient.ofGoodBad then
      some c
    else match c with
    | .app f a => findHCoeffOfGoodBad? a (fuel - 1) <|> findHCoeffOfGoodBad? f (fuel - 1)
    | .letE _ _ v b _ => findHCoeffOfGoodBad? b (fuel - 1) <|> findHCoeffOfGoodBad? v (fuel - 1)
    | _ => none

private def decompileCombinatorialSubgoal (ctx : DecompCtx) (decompileChild : DecompileChild)
    (idTag : String) (summary : String) (aty ap : Expr) :
    StateRefT DiscourseState MetaM (Array ProofNode) := do
  if let some fvid := unwrapHypothesisFVar? ap then
    let n ← renderHypothesisStep ctx.tbl aty fvid s!"{idTag}-{fvid.name}" (isWrap := true)
    return #[n]
  if hasAnyVerboseAnnotation ap || exprCountBounded ap 45 < 45 then
    decompileChild ctx aty ap
  else
    let g ← buildGoalState ctx.tbl aty
    return #[.routineReceipt idTag summary 1 #[] (some g)]

private partial def stripUnusedNonPropForalls (e : Expr) : MetaM Expr := do
  match e.consumeMData with
  | .forallE _ dom body _ =>
      if !body.hasLooseBVar 0 && !(← isProp dom) then
        stripUnusedNonPropForalls body
      else
        return e
  | _ => return e

private def extractHCoefficientChildren (ctx : DecompCtx) (decompileChild : DecompileChild)
    (proof : Expr) : StateRefT DiscourseState MetaM (Array ProofNode) := do
  let subCtx := subContextOf ctx
  let some w := findHCoeffOfGoodBad? proof |
    return ← decompilePremiseArgs subCtx decompileChild proof
  let pArgs ← proofValuedArgs w
  let total := pArgs.size
  let mut out : Array ProofNode := #[]
  -- `ofGoodBad` proof arguments end with: `[..., idealReveal_isProbDist, hε₁, ratio, bad]`
  if total ≥ 4 then
    let (apProb, atyProb) := pArgs[total - 4]!
    let subProb ← decompileCombinatorialSubgoal subCtx decompileChild s!"vcc-hcoeff-prob-rec-{total}"
      "verifying that the auxiliary ideal reveal defines a probability distribution" atyProb apProb
    if !subProb.isEmpty then
      let cleanProb ← stripUnusedNonPropForalls atyProb
      let inlProb := ensureSymbolicPredClause (← renderProposition ctx.tbl cleanProb)
      let gProb ← buildGoalState ctx.tbl cleanProb
      out := out.push (.step s!"vcc-hcoeff-prob-{total}"
        (#[.text "First, on the ideal side the auxiliary reveal defines a valid conditional probability law: "] ++
         inlProb ++ #[.text "."]) subProb (some gProb))
  if total ≥ 2 then
    let (apRatio, atyRatio) := pArgs[total - 2]!
    let subRatio ← decompileCombinatorialSubgoal subCtx decompileChild s!"vcc-hcoeff-ratio-rec-{total}"
      "pointwise probability-ratio verification across good extended transcripts" atyRatio apRatio
    let inlRatio := ensureSymbolicPredClause (← renderProposition ctx.tbl atyRatio)
    let gRatio ← buildGoalState ctx.tbl atyRatio
    let ratioLead :=
      let txt := (String.intercalate "" (inlRatio.toList.map Inline.collectText)).trimAscii.toString.toLower
      if txt.startsWith "for every" || txt.startsWith "if " then
        "On every attainable good extended transcript, the real-to-ideal probability ratio condition holds: "
      else
        "On every attainable good extended transcript, the real-to-ideal probability ratio satisfies "
    out := out.push (.step s!"vcc-hcoeff-ratio-{total}"
      (#[.text ratioLead] ++ inlRatio ++ #[.text "."]) subRatio (some gRatio))
    let (apBad, atyBad) := pArgs[total - 1]!
    let subBad ← decompileCombinatorialSubgoal subCtx decompileChild s!"vcc-hcoeff-bad-rec-{total}"
      "probability-mass bound over bad transcripts across compatible environments" atyBad apBad
    let inlBad := ensureSymbolicPredClause (← renderProposition ctx.tbl atyBad)
    let gBad ← buildGoalState ctx.tbl atyBad
    out := out.push (.step s!"vcc-hcoeff-bad-{total}"
      (#[.text "For bad extended transcripts on the ideal side, "] ++
       inlBad ++ #[.text "."]) subBad (some gBad))
  return out

/-! ## 5. Primary Verbose-CC `RuleExplainer` (Priority 500) -/

private def originOf (env : Environment) (inner : Expr) : Option String :=
  match inner.getAppFn.consumeMData with
  | .const n _ => if isCoreOrMathlibIn env n then none else some n.toString
  | _ => none

/-- High-priority `RuleExplainer` recognizing Verbose-CC `Expr.mdata` trace tags and rendering
checked proof steps in Ueli Maurer's calm, paper-authentic voice. -/
def verboseCCExplainer : RuleExplainer where
  priority := 500
  explain ctx decompileChild expected proof := do
    -- Case 0: Strict `by_leaf` opacity wall — never drill into raw tactic internals (`sorry`-honest).
    if let some (leafKind, leafSummary, leafInner) := findOuterByLeafMData? proof then
      markStepEmitted
      let goal ← buildGoalState ctx.tbl expected
      let env ← getEnv
      if leafKind == "sorry_leaf" || exprContainsSorryAx leafInner then
        let clean := stripTrailingPeriod (leafSummary.trimAscii.toString)
        let msg := if clean.isEmpty then "[UNPROVED: sorry]" else s!"[UNPROVED: sorry] {clean}."
        return some #[.step s!"vcc-leaf-sorry-{ctx.factIndex}" #[.text msg] #[] (some goal)
          none (originOf env leafInner)]
      return some #[.step s!"vcc-leaf-{ctx.factIndex}" (formatLeafSummaryProse leafSummary) #[]
        (some goal) none (originOf env leafInner)]

    -- Case A: Annotated `cc_calc` chain without outer `By_hybrid_chain` wrapper
    if unwrapVerboseMData? proof |>.isNone then
      let p := proof.consumeMData
      let fn := p.getAppFn.consumeMData
      let args := p.getAppArgs
      let isChainRoot :=
        fn.isConstOf ``ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.trans ||
        (← splitStatTri? p).isSome ||
        (← splitEqTransport? p).isSome ||
        ((fn.isConstOf ``Eq.mp || fn.isConstOf ``Eq.mpr) && args.size ≥ 2)
      if isChainRoot && hasAnyCalcStepAnnotation p then
        if let some nodes ← buildAnnotatedCalcChain ctx decompileChild expected proof "vcc-calc" then
          return some nodes
      return none

    let some (kv, inner) := unwrapVerboseMData? proof | return none
    let some kind := mdataGetString? kv ccVerboseKindKey | return none
    let label? := mdataGetString? kv ccVerboseLabelKey
    let reason? := mdataGetString? kv ccVerboseReasonKey
    let role? := mdataGetString? kv ccVerboseRoleKey
    let count? := mdataGetNat? kv ccVerboseCountKey
    let subCtx := subContextOf ctx
    let env ← getEnv

    match kind with
    -- 0. Proof overview roadmap and paragraph breaks
    | "proof_overview" =>
        markStepEmitted
        let bodyInl := appendSentencePunct (parseProseWithMath (reason?.getD "")) "."
        let step ← mkVerboseStep ctx s!"vcc-overview-{ctx.factIndex}" bodyInl #[] expected
        let brk : ProofNode := .flowNote s!"vcc-para-overview-{ctx.factIndex}" "" "paragraph"
        let rest ← decompileChild { ctx with isProofStart := false } expected inner
        return some (#[step, brk] ++ rest)

    | "paragraph" =>
        markStepEmitted
        let heading := reason?.getD ""
        let brk : ProofNode := .flowNote s!"vcc-para-{ctx.factIndex}" heading "paragraph"
        let rest ← decompileChild { ctx with isProofStart := false } expected inner
        return some (#[brk] ++ rest)

    -- 0b. Scoped paper notation (`With notation e as sym [explaining "..."]`)
    | "with_notation" =>
        let sym := label?.getD ""
        let unwrapPair : Option (Expr × Expr) :=
          match inner.consumeMData with
          | .app fn val =>
              match fn.consumeMData with
              | .lam _ _ body _ => some (val, body.instantiate1 val)
              | _ => none
          | .letE _ _ val body _ => some (val, body.instantiate1 val)
          | _ => none
        match unwrapPair with
        | some (val, nextProof) =>
            let normVal ← normalizeForPresentation val
            let tblWithout := { ctx.tbl with exprAliases := ctx.tbl.exprAliases.filter (·.2 != sym) }
            let rhsTex ← exprToLatex normVal tblWithout
            let (leanTy, roleDesc) ← try
              let pty ← inferType normVal
              pure (← ppCleanType pty, ← formatParameterRole ctx.tbl pty)
            catch _ =>
              pure ("", "Scoped paper notation.")
            let desc := reason?.getD roleDesc
            registerScopedNotationInspector (declTagFromCtx ctx) sym rhsTex leanTy desc "notation"
            let nextTbl ← ctx.tbl.withNormalizedExprAlias val sym
            let nextTbl := nextTbl.withExprAlias val.consumeMData sym
            return some (← decompileChild { ctx with tbl := nextTbl } expected nextProof)
        | none =>
            return some (← decompileChild ctx expected inner)

    | "with_notation_let" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            let sym := label?.getD (formatMathIdent (nm.toString))
            let normVal ← normalizeForPresentation val
            let tblWithout := { ctx.tbl with exprAliases := ctx.tbl.exprAliases.filter (·.2 != sym) }
            let rhsTex ← exprToLatex normVal tblWithout
            let (leanTy, roleDesc) ← try
              pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
            catch _ =>
              pure ("", "Scoped local notation.")
            let desc := reason?.getD roleDesc
            registerScopedNotationInspector (declTagFromCtx ctx) sym rhsTex leanTy desc "notation"
            withLetDecl nm ty val fun fv => do
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let step : ProofNode :=
                match reason? with
                | some g =>
                    if visibleMathLengthTex rhsTex ≥ 64 then
                      .step s!"vcc-letnot-{ctx.factIndex}"
                        (#[.text "Let ", .inlineMath sym, .text " denote "] ++ stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g)) ++ #[.text "."])
                        #[] (some goal)
                    else
                      .step s!"vcc-letnot-{ctx.factIndex}"
                        (#[.text "Let ", .inlineMath s!"{sym} := {rhsTex}", .text ", "] ++ stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g)) ++ #[.text "."])
                        #[] (some goal)
                | none =>
                    .step s!"vcc-letnot-{ctx.factIndex}"
                      #[.text "Let ", .inlineMath s!"{sym} := {rhsTex}", .text "."]
                      #[] (some goal)
              let nextTbl ← ctx.tbl.withNormalizedExprAlias val sym
              let nextTbl := (nextTbl.withExprAlias val.consumeMData sym).withExprAlias fv sym
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 1. Individual `cc_calc` step wrapper: let outer chain read its reason, or unwrap cleanly
    | "cc_calc_step" =>
        return some (← decompileChild ctx expected inner)

    -- 2. `Let x denote e` / `Write x := e` local shorthand
    | "write" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let (leanTy, roleDesc) ← try
                pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
              catch _ =>
                pure ("", "Local definition.")
              registerScopedNotationInspector (declTagFromCtx ctx) symTex valTex leanTy (reason?.getD roleDesc) "local shorthand"
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let defMath : Array Inline :=
                if hasSubstantialMath valTex && reason?.isNone then
                  #[.displayMath s!"{symTex} := {valTex}" "."]
                else if reason?.isSome && visibleMathLengthTex valTex ≥ 56 then
                  #[.inlineMath symTex]
                else
                  #[.inlineMath s!"{symTex} := {valTex}"]
              let prose : Array Inline := match reason? with
                | some g =>
                    let gInl := stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g))
                    if visibleMathLengthTex valTex ≥ 56 then
                      #[.text "Let "] ++ defMath ++ #[.text " be "] ++ gInl ++ #[.text "."]
                    else
                      #[.text "Let "] ++ defMath ++ #[.text ", "] ++ gInl ++ #[.text "."]
                | none =>
                    appendSentencePunct (#[.text "Let "] ++ defMath) "."
              let step : ProofNode :=
                .step s!"vcc-write-{symTex}-{ctx.factIndex}" prose #[] (some goal)
              let nextTbl ← extendTblWithLocalAlias ctx.tbl fv val symTex valTex
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 3. `Define hybrid H := e` / `Introduce_hybrid H := e`
    | "hybrid" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let (leanTy, roleDesc) ← try
                pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
              catch _ =>
                pure ("", "Intermediate hybrid system.")
              registerScopedNotationInspector (declTagFromCtx ctx) symTex valTex leanTy (reason?.getD roleDesc) "hybrid"
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let prose : Array Inline := match reason? with
                | some g =>
                    let gClean := stripTrailingPeriod g
                    let gLow := gClean.trimAscii.toString.toLower
                    let gBody :=
                      if gLow.startsWith "where " || gLow.startsWith "in which " || gLow.startsWith "such that " then gClean
                      else s!"where {gClean}"
                    let gInl := parseProseWithMath gBody
                    if visibleMathLengthTex valTex ≥ 56 then
                      #[.text "Define the intermediate hybrid ", .inlineMath symTex, .text ", "] ++ gInl ++ #[.text "."]
                    else
                      #[.text "Define the intermediate hybrid ", .inlineMath s!"{symTex} := {valTex}", .text ", "] ++ gInl ++ #[.text "."]
                | none =>
                    if hasSubstantialMath valTex then
                      #[.text "Define the intermediate hybrid ", .displayMath s!"{symTex} := {valTex}" "."]
                    else
                      #[.text "Define the intermediate hybrid ", .inlineMath s!"{symTex} := {valTex}", .text "."]
              let step : ProofNode :=
                .step s!"vcc-hybrid-{symTex}-{ctx.factIndex}" prose #[] (some goal)
              let nextTbl ← extendTblWithLocalAlias ctx.tbl fv val symTex valTex
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 3b. `Define game G₀ := e` (opens its own Boneh–Shoup `Game k.` paragraph)
    | "define_game" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let (leanTy, roleDesc) ← try
                pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
              catch _ =>
                pure ("", "Security game system.")
              registerScopedNotationInspector (declTagFromCtx ctx) symTex valTex leanTy (reason?.getD roleDesc) "game"
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let headingRaw := role?.getD (formatGameHeading (label?.getD (toString nm)))
              let heading := if headingRaw.endsWith "." then headingRaw else s!"{headingRaw}."
              let prose : Array Inline := match reason? with
                | some g =>
                    let gClean := stripTrailingPeriod g
                    let gLow := gClean.trimAscii.toString.toLower
                    let gBody :=
                      if gLow.startsWith "where " || gLow.startsWith "in which " then gClean
                      else s!"in which {gClean}"
                    let gInl := parseProseWithMath gBody
                    if visibleMathLengthTex valTex ≥ 56 then
                      #[.text "Let ", .inlineMath symTex, .text " be the game "] ++ parseProseWithMath gClean ++ #[.text "."]
                    else
                      #[.text "Define ", .inlineMath s!"{symTex} := {valTex}", .text ", "] ++ gInl ++ #[.text "."]
                | none =>
                    if hasSubstantialMath valTex then
                      #[.text "Let ", .displayMath s!"{symTex} := {valTex}" "."]
                    else
                      #[.text "Let ", .inlineMath s!"{symTex} := {valTex}", .text "."]
              let step : ProofNode :=
                .step s!"vcc-game-{symTex}-{ctx.factIndex}" prose #[] (some goal)
                  none none false false true (some heading)
              let nextTbl ← extendTblWithLocalAlias ctx.tbl fv val symTex valTex
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 3c. `Consider adversary B := e`
    | "let_adv" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let (leanTy, roleDesc) ← try
                pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
              catch _ =>
                pure ("", "Constructed reduction adversary.")
              registerScopedNotationInspector (declTagFromCtx ctx) symTex valTex leanTy (reason?.getD roleDesc) "adversary"
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let prose : Array Inline := match reason? with
                | some g =>
                    let gClean := stripTrailingPeriod g
                    let gLower := gClean.trimAscii.toString.toLower
                    let gInl := parseProseWithMath gClean
                    let conn :=
                      if gLower.startsWith "that " || gLower.startsWith "which " || gLower.startsWith "who " || gLower.startsWith "as " || gLower.startsWith "acting " then " "
                      else " that "
                    if visibleMathLengthTex valTex ≥ 48 then
                      #[.text "Construct an adversary ", .inlineMath symTex, .text conn] ++ gInl ++ #[.text "."]
                    else
                      #[.text "Construct an adversary ", .inlineMath s!"{symTex} := {valTex}", .text conn] ++ gInl ++ #[.text "."]
                | none =>
                    #[.text "Construct an adversary ", .inlineMath s!"{symTex} := {valTex}", .text "."]
              let step : ProofNode :=
                .step s!"vcc-adv-{symTex}-{ctx.factIndex}" prose #[] (some goal)
              let nextTbl ← extendTblWithLocalAlias ctx.tbl fv val symTex valTex
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 4. `We claim` / `We note` / `Claim` / `Fact`
    | "claim" | "fact" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            markStepEmitted
            let valNodes ← decompileChild subCtx ty val
            let propDisp ← formatPropSentence ctx.tbl ty "."
            let lead :=
              if kind == "claim" then
                match ctx.factIndex with
                | 0 => "We claim that "
                | i => match i % 4 with
                  | 1 => "Next, notice that "
                  | 2 => "Moreover, "
                  | 3 => "It also holds that "
                  | _ => "Furthermore, "
              else
                match ctx.factIndex with
                | 0 => "First, observe that "
                | i => match i % 3 with
                  | 1 => "Note further that "
                  | 2 => "In addition, "
                  | _ => "Observe also that "
            let content : Array Inline := match reason? with
              | some r =>
                  let rClean := stripTrailingPeriod r
                  let rInl := parseProseWithMath rClean
                  if endsWithDisplayMath propDisp then
                    let rLow := rClean.trimAscii.toString.toLower
                    let headStr :=
                      if kind == "claim" then
                        match ctx.factIndex with
                        | 0 => "We claim"
                        | i => match i % 4 with
                          | 1 => "Next, notice"
                          | 2 => "Moreover, observe"
                          | 3 => "It also holds"
                          | _ => "Furthermore, note"
                      else
                        match ctx.factIndex with
                        | 0 => "First, observe"
                        | i => match i % 3 with
                          | 1 => "Note further"
                          | 2 => "In addition, observe"
                          | _ => "Observe also"
                    if rLow.startsWith "by " || rLow.startsWith "since " || rLow.startsWith "via " || rLow.startsWith "from " then
                      #[.text s!"{headStr}, "] ++ rInl ++ #[.text ", that"] ++ propDisp
                    else
                      #[.text s!"{headStr} ("] ++ rInl ++ #[.text ") that"] ++ propDisp
                  else
                    let base := match propDisp.back? with
                      | some (.text ".") => propDisp.pop
                      | _ => propDisp
                    #[.text lead] ++ base ++ #[.text ", "] ++ rInl ++ #[.text "."]
              | none => #[.text lead] ++ propDisp
            let step ← mkVerboseStep ctx s!"vcc-{kind}-{ctx.factIndex}" content valNodes ty
            let rest ← withLetDecl nm ty val fun fv =>
              let nextCtx :=
                { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
              decompileChild nextCtx expected (body.instantiate1 fv)
            return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    -- 4b. `Since ... we get [h :] P` and `Since ... we conclude`
    | "since" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            markStepEmitted
            let valNodes ← decompileChild subCtx ty val
            let propDisp ← formatPropSentence ctx.tbl ty "."
            let cs := collectConsts val
            let usesPrev := match ctx.lastFactFVar? with
              | some fid => (Lean.collectFVars {} val).fvarIds.contains fid
              | none => false
            let lead :=
              if cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_attach_le ||
                 cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le ||
                 cs.contains ``ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le then
                "By non-expansion, we obtain"
              else if count?.getD 1 ≥ 2 then
                "Combining the preceding bounds, we obtain"
              else if usesPrev then
                "From this, we obtain"
              else
                "Since the assumption holds, we obtain"
            let step ← mkVerboseStep ctx s!"vcc-since-{ctx.factIndex}"
              (clauseThat lead propDisp) valNodes ty
            let rest ← withLetDecl nm ty val fun fv =>
              let nextCtx :=
                { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
              decompileChild nextCtx expected (body.instantiate1 fv)
            return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    | "since_conclude" =>
        markStepEmitted
        let children ←
          if (unwrapVerboseMData? inner).isSome then
            decompileChild subCtx expected inner
          else
            decompilePremiseArgs subCtx decompileChild inner
        let propDisp ← formatPropSentence ctx.tbl expected "."
        let content : Array Inline ← match reason? with
          | some r =>
              let rInls := stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod r))
              let conn := if isClauseProseInl propDisp then ", which establishes that " else ", which establishes "
              pure (rInls ++ #[.text conn] ++ propDisp)
          | none =>
              if ctx.atRootConclusion || ctx.isClosingGoal then
                pure (clauseThat "Combining these bounds yields" propDisp)
              else
                pure (clauseThat "From these bounds, we conclude" propDisp)
        let step ← mkVerboseStep ctx s!"vcc-since-close-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 5. `By <reason> it suffices to show P` / `It suffices to show P by/because ...`
    | "suffices" =>
        match inner.consumeMData with
        | .letE hNm dom pProof body _ =>
            markStepEmitted
            let (reasonPhrase, reasonNodes) ← withLocalDecl hNm .default dom fun fv => do
              let bodyInst := body.instantiate1 fv
              let rNodes ← decompileChild subCtx expected bodyInst
              let rPhrase := reason?.getD (inferSufficesReason env bodyInst)
              pure (rPhrase, rNodes)
            let pDisp ← formatPropSentence ctx.tbl dom "."
            let lead := sanitizeReasonCore reasonPhrase true
            let sufficesStep ← mkVerboseStep ctx s!"vcc-suffices-{ctx.factIndex}"
              (parseProseWithMath s!"{lead}, it suffices to show that " ++ pDisp)
              reasonNodes dom
            let rest ← decompileChild { ctx with atRootConclusion := false, isProofStart := false, isClosingGoal := ctx.isClosingGoal } dom pProof
            return some (#[sufficesStep] ++ rest)
        | .app fn pProof =>
            match fn.consumeMData with
            | .lam hNm dom body bi =>
                markStepEmitted
                let (reasonPhrase, reasonNodes) ← withLocalDecl hNm bi dom fun fv => do
                  let bodyInst := body.instantiate1 fv
                  let rNodes ← decompileChild subCtx expected bodyInst
                  let rPhrase := reason?.getD (inferSufficesReason env bodyInst)
                  pure (rPhrase, rNodes)
                let pDisp ← formatPropSentence ctx.tbl dom "."
                let lead := sanitizeReasonCore reasonPhrase true
                let sufficesStep ← mkVerboseStep ctx s!"vcc-suffices-{ctx.factIndex}"
                  (parseProseWithMath s!"{lead}, it suffices to show that " ++ pDisp)
                  reasonNodes dom
                let rest ← decompileChild { ctx with atRootConclusion := false, isProofStart := false, isClosingGoal := ctx.isClosingGoal } dom pProof
                return some (#[sufficesStep] ++ rest)
            | _ => return some (← decompileChild ctx expected inner)
        | _ => return some (← decompileChild ctx expected inner)

    -- 6. `By_CC_routine { ... }` compression receipt (quiet in Paper mode, expandable in Auditor)
    | "cc_routine" =>
        markStepEmitted
        let routineCtx := { subCtx with lemmaDepth := subCtx.config.maxLemmaDepth }
        let (summary, realInner) ← renderRoutineSummary ctx.tbl reason? inner
        let details ← match unwrapHypothesisFVar? realInner with
          | some fvid => do
              let n ← renderHypothesisStep ctx.tbl expected fvid s!"vcc-routine-hyp-{fvid.name}" (isWrap := true)
              pure #[n]
          | none => decompileChild routineCtx expected realInner
        let goal ← buildGoalState ctx.tbl expected
        let cnt := count?.getD (max 1 details.size)
        return some #[.routineReceipt s!"vcc-routine-{ctx.factIndex}" summary cnt details (some goal)]

    -- 7. `By_hybrid_chain { cc_calc ... }`
    | "hybrid_chain" =>
        if let some nodes ← buildAnnotatedCalcChain ctx decompileChild expected inner "vcc-hybrid-chain" then
          return some nodes
        return some (← decompileChild ctx expected inner)

    -- 8. `Construct_using h` / `Construct S from R via π using h`
    | "construct" =>
        let op ← pickOpener .consequence
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} from the checked construction witness, "] ++ conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-construct-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 9. `Replace_converter_in h using hEq`
    | "replace_converter" =>
        let op ← pickOpener .elaboration
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} since the two converters induce identical attachments, replacing the converter preserves the statement and shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-replace-conv-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 10. `By_sequential_composition h1 and h2`
    | "seq_comp" =>
        let op ← pickOpener .consequence
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} composing the inner and outer construction steps sequentially shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-seq-comp-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 11. `By_parallel_composition hL and hR`
    | "par_comp" =>
        let op ← pickOpener .consequence
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} placing the left and right constructions side by side by parallel composability establishes that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-par-comp-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 12. `By_context_insensitivity_right` / `By_context_insensitivity_left`
    | "context_right" =>
        let op ← pickOpener .elaboration
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} by context-insensitivity, making the untouched parallel resource available on the right preserves the construction and shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-ctx-right-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    | "context_left" =>
        let op ← pickOpener .elaboration
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} by context-insensitivity, making the untouched parallel resource available on the left preserves the construction and shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-ctx-left-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 13. `Pull_relaxation_through hOuter using hCompat from hInner`
    | "pull_relax" =>
        let op ← pickOpener .consequence
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let content : Array Inline :=
          #[.text s!"{op} pulling the relaxation to the outside through the outer protocol—accounting for the outer converter via the compatibility property—shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-pull-relax-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 14. `Substitute_in_context ...`
    | "substitute" =>
        let op ← pickOpener .elaboration
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl ← renderProposition ctx.tbl expected
        let convTex? ← findConverterArgLatex? ctx.tbl inner
        let ctxPhrase : Array Inline := match convTex? with
          | some c =>
              #[.text "inside the converter context ", .inlineMath c,
                .text " absorbs ", .inlineMath c, .text " into the distinguisher—preserving admissibility by closure of ",
                .inlineMath "\\mathcal{D}", .text "—and shows that "]
          | none =>
              #[.text "inside the surrounding converter context absorbs the context into the distinguisher and shows that "]
        let content : Array Inline :=
          #[.text s!"{op} substituting "] ++ ctxPhrase ++ conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-substitute-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 15. `By_triangle_inequality_via M`
    | "triangle" =>
        let op ← pickOpener .elaboration
        let mut children : Array ProofNode := #[]
        let mut midTex? : Option String := none
        if let some (mid, p1, p2) ← extractTriangleData? inner then
          midTex? := some (← exprToLatex mid ctx.tbl)
          let t1 ← inferType p1
          let t2 ← inferType p2
          let sub1 ← decompileChild subCtx t1 p1
          let sub2 ← decompileChild subCtx t2 p2
          let inl1 ← renderProposition ctx.tbl t1
          let inl2 ← renderProposition ctx.tbl t2
          let g1 ← buildGoalState ctx.tbl t1
          let g2 ← buildGoalState ctx.tbl t2
          children := #[
            .step s!"vcc-tri-left-{ctx.factIndex}"
              (#[.text "For the first leg, "] ++ inl1 ++ #[.text "."]) sub1 (some g1),
            .step s!"vcc-tri-right-{ctx.factIndex}"
              (#[.text "For the second leg, "] ++ inl2 ++ #[.text "."]) sub2 (some g2)
          ]
        else
          children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
        let viaPhrase : Array Inline := match midTex? with
          | some m => #[.text " via the intermediate system ", .inlineMath m]
          | none => #[]
        let content : Array Inline :=
          #[.text s!"{op} applying the triangle inequality"] ++ viaPhrase ++
          #[.text " shows that "] ++ conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-triangle-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 16. `By non-expansion` / `By non-expansion from h`
    | "nonexpand" =>
        let op ← pickOpener .justification
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let content : Array Inline :=
          #[.text s!"{op} {nonexpandPhrase inner}, "] ++
          conclDisp
        let step ← mkVerboseStep ctx s!"vcc-nonexpand-{ctx.factIndex}" content #[] expected (originOf env inner)
        return some #[step]

    | "nonexpand_from" =>
        let op ← pickOpener .justification
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let content : Array Inline :=
          #[.text s!"{op} {nonexpandPhrase inner}, "] ++ conclDisp
        let step ← mkVerboseStep ctx s!"vcc-nonexpand-from-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 17. `Exhibit_simulator σ [for_interface E]`
    | "exhibit_simulator" =>
        markStepEmitted
        let simTex? ← findEntityLatex? ctx.tbl inner label? (fun ty => do
          let t ← normalizeForPresentation ty
          pure (t.isAppOf ``Quiver.Hom || t.isAppOf `SystemAlgebra.TypedConverter ||
                t.isAppOf `ConstructiveCryptography.CryptographicAlgebra.Converter))
        let ifaceTex? ← match role? with
          | some _ => findEntityLatex? ctx.tbl inner role? (fun ty => do
              let t ← normalizeForPresentation ty
              pure (t.consumeMData == mkConst `SystemAlgebra.Interface))
          | none => pure none
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let simPhrase : Array Inline := match simTex?, ifaceTex? with
          | some s, some iface =>
              #[.text "We exhibit the explicit simulator ", .inlineMath s,
                .text " attached to the ", .inlineMath iface, .text "-interface"]
          | some s, none =>
              #[.text "We exhibit the explicit simulator ", .inlineMath s,
                .text " attached to the adversarial interface"]
          | none, _ =>
              #[.text "We exhibit an admitted simulator attached to the adversarial interface"]
        let content : Array Inline :=
          simPhrase ++
          #[.text " and verify both admissibility and the closeness bound, establishing that "] ++
          conclDisp
        let step ← mkVerboseStep ctx s!"vcc-exhibit-sim-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 18. `Compose_simulators hInner and hOuter [using_commutation hCommutes]`
    | "compose_simulators" =>
        markStepEmitted
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
        let content : Array Inline :=
          #[.text "By composition-order invariance between the outer protocol and the inner simulator, composing the simulator constructions serially shows that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-compose-sim-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 19. `Ignore_MBO_of G`
    | "ignore_mbo" =>
        markStepEmitted
        let (realRest, nextExpected) ← do
          let c := inner.consumeMData
          let fn := c.getAppFn.consumeMData
          let cArgs := c.getAppArgs
          if (fn.isConstOf ``Eq.mpr || fn.isConstOf ``Eq.mp) && cArgs.size ≥ 4 then
            let restExpr := cArgs[cArgs.size - 1]!
            let restTy ← inferType restExpr
            pure (restExpr, restTy)
          else
            pure (inner, expected)
        let restNodes ← decompileChild { ctx with isProofStart := false } nextExpected realRest
        let gPhrase : Array Inline := match label? with
          | some g =>
              #[.text "Let ", .inlineMath (formatMathIdent g ++ "^{-}"),
                .text " denote the underlying system resulting from ", .inlineMath (formatMathIdent g),
                .text " by ignoring the MBO; unfolding ", .inlineMath (formatMathIdent g ++ "^{-}"),
                .text " passes to the MBO-free goal."]
          | none =>
              #[.text "Passing to the underlying system obtained by ignoring the MBO reduces to the MBO-free comparison."]
        let step ← mkVerboseStep ctx s!"vcc-ignore-mbo-{ctx.factIndex}"
          gPhrase #[] nextExpected
        return some (#[step] ++ restNodes)

    -- 20. `By_fundamental_lemma_of_game_playing h`
    | "fundamental_game" =>
        markStepEmitted
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
        let content : Array Inline :=
          #[.text "By the fundamental lemma of game playing, any distinguisher between the underlying systems obtained by ignoring the MBO must provoke the MBO, showing that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-fund-game-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 21. `By_conditional_equivalence h`
    | "cond_equiv" =>
        markStepEmitted
        let children ← decompilePremiseArgs subCtx decompileChild inner
        let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
        let content : Array Inline :=
          clauseThat "Since the game is conditionally equivalent to the target system while the monotone binary output (MBO) remains unset, we obtain"
            (conclInl ++ #[.text "."])
        let step ← mkVerboseStep ctx s!"vcc-cond-equiv-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 22. `By_extended_H_technique ...`
    | "extended_h_coeff" =>
        let op ← pickOpener .consequence
        let children ← extractHCoefficientChildren ctx decompileChild inner
        let conclInl := ensureSymbolicPredClause (← renderProposition ctx.tbl expected)
        let content : Array Inline :=
          #[.text s!"{op} extending both systems by revealing their auxiliary randomness and applying the extended H-technique—separately bounding the bad-transcript mass on the ideal side and the probability ratio on good transcripts—establishes that "] ++
          conclInl ++ #[.text "."]
        let step ← mkVerboseStep ctx s!"vcc-ext-hcoeff-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 22b. `By the Difference Lemma with bad event Z [where/explaining "..."] ...`
    | "difference_lemma" =>
        markStepEmitted
        let (badVal?, realProof) :=
          match inner.consumeMData with
          | .app fn bad =>
              match fn.consumeMData with
              | .lam _ _ body _ => (some bad, body)
              | _ => (none, inner)
          | _ => (none, inner)
        let badTex? ← match badVal?, label? with
          | some bv, _ => pure (some (← exprToLatex bv ctx.tbl))
          | none, some l => pure (some (formatMathIdent l))
          | none, none => pure none
        if let (some bv, some g) := (badVal?, reason?) then
          let bt := badTex?.getD "Z"
          let lty ← try ppCleanType (← inferType bv) catch _ => pure "Ω → Prop"
          registerScopedNotationInspector (declTagFromCtx ctx) bt bt lty g "bad event"
        let children ← decompilePremiseArgs subCtx decompileChild realProof
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let badPhrase : Array Inline := match badTex?, reason? with
          | some bt, some g =>
              #[.text " with bad event ", .inlineMath bt, .text " ("] ++ stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g)) ++ #[.text ")"]
          | some bt, none => #[.text " with bad event ", .inlineMath bt]
          | none, some g => #[.text ", "] ++ stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g))
          | none, none => #[]
        let content : Array Inline :=
          #[.text "By the Difference Lemma"] ++ badPhrase ++ #[.text ", "] ++ conclDisp
        let step ← mkVerboseStep ctx s!"vcc-diff-lemma-{ctx.factIndex}" content children expected (originOf env realProof)
        return some #[step]

    -- 23. `We exhibit distinguisher D` / `Exhibit_distinguisher D`
    | "exhibit_distinguisher" =>
        markStepEmitted
        let advBody := do
          let mut cur := inner
          for _ in [0:4] do
            if (unwrapVerboseMData? cur).isSome then break
            let c := cur.consumeMData
            let fn := c.getAppFn.consumeMData
            let cArgs := c.getAppArgs
            if (fn.isConstOf ``Eq.mpr || fn.isConstOf ``Eq.mp) && cArgs.size ≥ 4 then
              cur := cArgs[cArgs.size - 1]!
            else if fn.isConstOf ``le_trans && cArgs.size ≥ 6 then
              cur := cArgs[cArgs.size - 2]!
            else
              break
          let advTy ← inferType cur
          decompileChild subCtx advTy cur
        let children ← advBody
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let distTex? ← do
          let fromInner ← findEntityLatex? ctx.tbl inner label? isDistinguisherType
          match fromInner with
          | some s => pure (some s)
          | none => findEntityLatex? ctx.tbl expected label? isDistinguisherType
        let distPhrase : Array Inline := match distTex? with
          | some d => #[.text "We exhibit the explicit compatible distinguisher ", .inlineMath d]
          | none => #[.text "We exhibit an explicit compatible distinguisher"]
        let content : Array Inline :=
          distPhrase ++
          #[.text "; since every compatible distinguisher's advantage is bounded by ",
            .inlineMath "\\Delta", .text ", its advantage shows that "] ++
          conclDisp
        let step ← mkVerboseStep ctx s!"vcc-exhibit-dist-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 24. `Lower_bound_advantage_of D`
    | "lower_bound_adv" =>
        let op ← pickOpener .consequence
        let g ← buildGoalState ctx.tbl expected
        let children : Array ProofNode :=
          #[.routineReceipt s!"vcc-lower-adv-rec-{ctx.factIndex}"
              "computing the decision probabilities on both systems and applying the triangle inequality"
              1 #[] (some g)]
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let distTex? ← findEntityLatex? ctx.tbl expected label? isDistinguisherType
        let distPhrase : Array Inline := match distTex? with
          | some d => #[.inlineMath d]
          | none => #[.text "the distinguisher"]
        let content : Array Inline :=
          #[.text s!"{op} bounding the decision probabilities of "] ++ distPhrase ++
          #[.text " on the real and ideal systems separately shows that "] ++ conclDisp
        let step ← mkVerboseStep ctx s!"vcc-lower-adv-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 25. `Tightness_sandwich`
    | "tightness_sandwich" =>
        let c := inner.consumeMData
        if c.getAppFn.consumeMData.isConstOf ``And.intro && c.getAppArgs.size ≥ 4 then
          markStepEmitted
          let args := c.getAppArgs
          let p1 := args[args.size - 2]!
          let p2 := args[args.size - 1]!
          let t1 ← inferType p1
          let t2 ← inferType p2
          let sub1 ← decompileChild subCtx t1 p1
          let sub2 ← decompileChild subCtx t2 p2
          let disp1 ← formatPropSentence ctx.tbl t1 "."
          let disp2 ← formatPropSentence ctx.tbl t2 "."
          let isUpperFirst := role? == some "upper_lower"
          let lead1 := if isUpperFirst then "For the upper bound, " else "For the lower bound, "
          let lead2 := if isUpperFirst then "For the matching lower bound, " else "For the matching upper bound, "
          let step1 ← mkVerboseStep ctx s!"vcc-sandwich-1-{ctx.factIndex}"
            (#[.text lead1] ++ disp1) sub1 t1
          let step2 ← mkVerboseStep ctx s!"vcc-sandwich-2-{ctx.factIndex}"
            (#[.text lead2] ++ disp2) sub2 t2
          let conclDisp ← formatPropSentence ctx.tbl expected "."
          let closeContent : Array Inline :=
            if ctx.atRootConclusion then
              #[.text "Combining the matching lower and upper bounds establishes the tightness sandwich."]
            else
              clauseThat "Combining the matching lower and upper bounds establishes" conclDisp
          let step3 ← mkVerboseStep ctx s!"vcc-sandwich-close-{ctx.factIndex}"
            closeContent #[] expected
          return some #[step1, step2, step3]
        return some (← decompileChild ctx expected inner)

    -- 26. `We conclude` / `Combining ...`
    | "combine" =>
        let op ← pickOpener .closing
        let children ←
          if (unwrapVerboseMData? inner).isSome then
            decompileChild subCtx expected inner
          else
            decompilePremiseArgs subCtx decompileChild inner
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let content : Array Inline ← match reason? with
          | some r =>
              let rInls := stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod r))
              let conn := if isClauseProseInl conclDisp then ", which establishes that " else ", which establishes "
              pure (rInls ++ #[.text conn] ++ conclDisp)
          | none =>
              if ctx.atRootConclusion || ctx.isClosingGoal then
                pure (clauseThat s!"{op} these bounds yields" conclDisp)
              else
                pure (#[.text s!"{op} "] ++ conclDisp)
        let step ← mkVerboseStep ctx s!"vcc-combine-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    -- 27. `We reformulate` / `By cases on` / `Case` / `By telescoping sum` / `By union bound`
    | "reformulate" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            markStepEmitted
            let valNodes ← decompileChild subCtx ty val
            let tyDisp ← formatPropSentence ctx.tbl ty "."
            let lead : Array Inline := match reason? with
              | some g => #[.text "Reformulating this bound ("] ++ stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g)) ++ #[.text ") yields "]
              | none => #[.text "Equivalently, we rewrite this as "]
            let step ← mkVerboseStep ctx s!"vcc-reformulate-{ctx.factIndex}" (lead ++ tyDisp) valNodes ty
            let rest ← withLetDecl nm ty val fun fv =>
              decompileChild { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
                expected (body.instantiate1 fv)
            return some (#[step] ++ rest)
        | .app fn pProof =>
            match fn.consumeMData with
            | .lam hNm dom body bi =>
                markStepEmitted
                let rNodes ← withLocalDecl hNm bi dom fun fv =>
                  decompileChild subCtx expected (body.instantiate1 fv)
                let domDisp ← formatPropSentence ctx.tbl dom "."
                let lead : Array Inline := match reason? with
                  | some g => #[.text "Reformulating the goal ("] ++ stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g)) ++ #[.text ") yields "]
                  | none => #[.text "Equivalently, we rewrite the target inequality as "]
                let step ← mkVerboseStep ctx s!"vcc-reformulate-goal-{ctx.factIndex}" (lead ++ domDisp) rNodes dom
                let rest ← decompileChild { ctx with atRootConclusion := false, isProofStart := false, isClosingGoal := ctx.isClosingGoal } dom pProof
                return some (#[step] ++ rest)
            | _ => return some (← decompileChild ctx expected inner)
        | _ =>
            return some (← decompileChild ctx expected inner)

    | "cases" =>
        return some (← decompileChild ctx expected inner)

    | "case" =>
        markStepEmitted
        let hd := match label? with
          | some l => if l.endsWith "." then l else s!"{l}."
          | none => "Case."
        let brk : ProofNode := .flowNote s!"vcc-case-{ctx.factIndex}" hd "paragraph"
        let bodyNodes ← decompileChild { ctx with isProofStart := false } expected inner
        return some (#[brk] ++ bodyNodes)

    | "telescoping" =>
        markStepEmitted
        let g ← buildGoalState ctx.tbl expected
        let details ← decompileChild { subCtx with lemmaDepth := subCtx.config.maxLemmaDepth } expected inner
        let children : Array ProofNode := #[.routineReceipt s!"vcc-tele-rec-{ctx.factIndex}"
          "telescoping intermediate hybrid sums" (max 1 details.size) details (some g)]
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let step ← mkVerboseStep ctx s!"vcc-telescoping-{ctx.factIndex}"
          (#[.text "By a telescoping sum over consecutive hybrids, "] ++ conclDisp) children expected (originOf env inner)
        return some #[step]

    | "union_bound" =>
        markStepEmitted
        let g ← buildGoalState ctx.tbl expected
        let details ← decompileChild { subCtx with lemmaDepth := subCtx.config.maxLemmaDepth } expected inner
        let children : Array ProofNode := #[.routineReceipt s!"vcc-union-rec-{ctx.factIndex}"
          "summing per-pair event probabilities via Finset union bound" (max 1 details.size) details (some g)]
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let step ← mkVerboseStep ctx s!"vcc-union-{ctx.factIndex}"
          (#[.text "By the union bound, "] ++ conclDisp) children expected (originOf env inner)
        return some #[step]

    | "paper_define_hybrid" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let (leanTy, roleDesc) ← try
                pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
              catch _ =>
                pure ("", "Intermediate hybrid system.")
              registerScopedNotationInspector (declTagFromCtx ctx) symTex valTex leanTy (reason?.getD roleDesc) "hybrid"
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let isRelClause (g : String) : Bool :=
                let low := g.trimAscii.toString.toLower
                low.startsWith "which " || low.startsWith "where " ||
                low.startsWith "in which " || low.startsWith "such that " ||
                low.startsWith "that "
              let gClean := reason?.map (fun g => (stripTrailingPeriod g).trimAscii.toString) |>.getD ""
              let hasReason := !gClean.isEmpty
              let hasRel := hasReason && isRelClause gClean
              let defMath : Array Inline :=
                if hasSubstantialMath valTex then
                  #[.displayMath s!"{symTex} := {valTex}" (if hasRel then "," else ".")]
                else
                  #[.inlineMath s!"{symTex} := {valTex}"]
              let prose : Array Inline :=
                if hasReason then
                  if hasRel then
                    let gInl := parseProseWithMath (lowercaseFirst gClean)
                    if hasSubstantialMath valTex then
                      #[.text "Define the intermediate hybrid "] ++ defMath ++ #[.text " "] ++ gInl ++ #[.text "."]
                    else
                      #[.text "Define the intermediate hybrid "] ++ defMath ++ #[.text ", "] ++ gInl ++ #[.text "."]
                  else
                    let gInl := parseProseWithMath (capitalizeFirst gClean)
                    if hasSubstantialMath valTex then
                      #[.text "Define the intermediate hybrid "] ++ defMath ++ #[.text " "] ++ gInl ++ #[.text "."]
                    else
                      #[.text "Define the intermediate hybrid "] ++ defMath ++ #[.text ". "] ++ gInl ++ #[.text "."]
                else
                  if hasSubstantialMath valTex then
                    #[.text "Define the intermediate hybrid "] ++ defMath
                  else
                    #[.text "Define the intermediate hybrid "] ++ defMath ++ #[.text "."]
              let step : ProofNode :=
                .step s!"paper-hybrid-{symTex}-{ctx.factIndex}" prose #[] (some goal)
              let nextTbl ← extendTblWithLocalAlias ctx.tbl fv val symTex valTex
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    | "paper_hybrid_hop" =>
        let emitHop := fun (isLet : Bool) (hNm : Name) (dom : Expr) (val body : Expr) (bi : BinderInfo) => do
          markStepEmitted
          let propDisp ← formatPropSentence ctx.tbl dom "."
          let hopChildren : Array ProofNode ←
            if exprContainsSorryAx val then
              let g ← buildGoalState ctx.tbl dom
              pure #[.step s!"paper-hop-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
            else
              pure #[]
          let content : Array Inline := match reason? with
            | some r =>
                let lead := sanitizeReasonCore r true
                parseProseWithMath s!"{lead}, " ++ propDisp
            | none =>
                #[.text "Between consecutive hybrids, "] ++ propDisp
          let step ← mkVerboseStep ctx s!"paper-hop-{ctx.factIndex}" content hopChildren dom (originOf env val)
          let cont (fv : Expr) :=
            let nextCtx := { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
            decompileChild nextCtx expected (body.instantiate1 fv)
          let rest ← if isLet then withLetDecl hNm dom val cont else withLocalDecl hNm bi dom cont
          return some (#[step] ++ rest)
        match inner.consumeMData with
        | .letE hNm dom val body _ => emitHop true hNm dom val body .default
        | .app fn val =>
            match fn.consumeMData with
            | .lam hNm dom body bi => emitHop false hNm dom val body bi
            | _ => return some (← decompileChild ctx expected inner)
        | _ => return some (← decompileChild ctx expected inner)

    | "paper_conclude_triangle" =>
        markStepEmitted
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let children : Array ProofNode ←
          if exprContainsSorryAx inner then
            let g ← buildGoalState ctx.tbl expected
            pure #[.step s!"paper-tri-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
          else
            pure #[]
        let content := #[.text "By the triangle inequality across the intermediate hybrids, "] ++ conclDisp
        let step ← mkVerboseStep ctx s!"paper-triangle-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    | "paper_bad_event" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let (leanTy, roleDesc) ← try
                pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
              catch _ =>
                pure ("", "Bad event predicate.")
              registerScopedNotationInspector (declTagFromCtx ctx) symTex valTex leanTy (reason?.getD roleDesc) "bad event"
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let prose : Array Inline := match reason? with
                | some g =>
                    let gInl := stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g))
                    #[.text "Let ", .inlineMath symTex, .text " denote the bad event "] ++ gInl ++ #[.text "."]
                | none =>
                    if hasSubstantialMath valTex then
                      #[.text "Let ", .inlineMath symTex, .text " denote the bad event ", .displayMath s!"{symTex} := {valTex}" "."]
                    else
                      #[.text "Define the bad event ", .inlineMath s!"{symTex} := {valTex}", .text "."]
              let step : ProofNode :=
                .step s!"paper-bad-{symTex}-{ctx.factIndex}" prose #[] (some goal)
              let nextTbl ← extendTblWithLocalAlias ctx.tbl fv val symTex valTex
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    | "paper_identical_until_bad" =>
        let emitEquiv := fun (isLet : Bool) (hNm : Name) (dom : Expr) (val body : Expr) (bi : BinderInfo) => do
          markStepEmitted
          let propDisp ← formatPropSentence ctx.tbl dom "."
          let children : Array ProofNode ←
            if exprContainsSorryAx val then
              let g ← buildGoalState ctx.tbl dom
              pure #[.step s!"paper-untilbad-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
            else
              pure #[]
          let content := #[.text "The systems agree identically until the bad event occurs: "] ++ propDisp
          let step ← mkVerboseStep ctx s!"paper-untilbad-{ctx.factIndex}" content children dom (originOf env val)
          let cont (fv : Expr) :=
            let nextCtx := { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
            decompileChild nextCtx expected (body.instantiate1 fv)
          let rest ← if isLet then withLetDecl hNm dom val cont else withLocalDecl hNm bi dom cont
          return some (#[step] ++ rest)
        match inner.consumeMData with
        | .letE hNm dom val body _ => emitEquiv true hNm dom val body .default
        | .app fn val =>
            match fn.consumeMData with
            | .lam hNm dom body bi => emitEquiv false hNm dom val body bi
            | _ => return some (← decompileChild ctx expected inner)
        | _ => return some (← decompileChild ctx expected inner)

    | "paper_conclude_diff_lemma" =>
        markStepEmitted
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let children : Array ProofNode ←
          if exprContainsSorryAx inner then
            let g ← buildGoalState ctx.tbl expected
            pure #[.step s!"paper-diff-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
          else
            pure #[]
        let content := match reason? with
          | some r =>
              let clean := stripTrailingPeriod r
              #[.text "By the Difference Lemma ("] ++ parseProseWithMath clean ++ #[.text "), "] ++ conclDisp
          | none =>
              #[.text "By the Difference Lemma, "] ++ conclDisp
        let step ← mkVerboseStep ctx s!"paper-diff-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    | "paper_split_transcripts" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let (leanTy, roleDesc) ← try
                pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
              catch _ =>
                pure ("", "Bad transcript predicate.")
              registerScopedNotationInspector (declTagFromCtx ctx) symTex valTex leanTy (reason?.getD roleDesc) "transcript partition"
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let prose : Array Inline := match reason? with
                | some g =>
                    let gInl := stripTrailingPunctInlines (parseProseWithMath (stripTrailingPeriod g))
                    #[.text "Partition transcripts into good and bad via ", .inlineMath symTex, .text ", "] ++ gInl ++ #[.text "."]
                | none =>
                    if hasSubstantialMath valTex then
                      #[.text "Partition transcripts into good and bad via ", .inlineMath symTex, .text ": ", .displayMath s!"{symTex} := {valTex}" "."]
                    else
                      #[.text "Partition transcripts into good and bad via ", .inlineMath s!"{symTex} := {valTex}", .text "."]
              let step : ProofNode :=
                .step s!"paper-split-{symTex}-{ctx.factIndex}" prose #[] (some goal)
              let nextTbl ← extendTblWithLocalAlias ctx.tbl fv val symTex valTex
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[step] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    | "paper_bound_bad_mass" | "paper_bound_good_ratio" =>
        let isBad := kind == "paper_bound_bad_mass"
        let emitHStep := fun (isLet : Bool) (hNm : Name) (dom : Expr) (val body : Expr) (bi : BinderInfo) => do
          markStepEmitted
          let propDisp ← formatPropSentence ctx.tbl dom "."
          let children : Array ProofNode ←
            if exprContainsSorryAx val then
              let g ← buildGoalState ctx.tbl dom
              pure #[.step s!"paper-hstep-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
            else
              pure #[]
          let lead := if isBad then "For bad transcripts, " else "For every good transcript, "
          let step ← mkVerboseStep ctx s!"paper-hstep-{ctx.factIndex}" (#[.text lead] ++ propDisp) children dom (originOf env val)
          let cont (fv : Expr) :=
            let nextCtx := { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
            decompileChild nextCtx expected (body.instantiate1 fv)
          let rest ← if isLet then withLetDecl hNm dom val cont else withLocalDecl hNm bi dom cont
          return some (#[step] ++ rest)
        match inner.consumeMData with
        | .letE hNm dom val body _ => emitHStep true hNm dom val body .default
        | .app fn val =>
            match fn.consumeMData with
            | .lam hNm dom body bi => emitHStep false hNm dom val body bi
            | _ => return some (← decompileChild ctx expected inner)
        | _ => return some (← decompileChild ctx expected inner)

    | "paper_conclude_h_coeff" | "paper_h_coeff" =>
        markStepEmitted
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let children : Array ProofNode ←
          if exprContainsSorryAx inner then
            let g ← buildGoalState ctx.tbl expected
            pure #[.step s!"paper-hcoeff-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
          else
            pure #[]
        let step ← mkVerboseStep ctx s!"paper-hcoeff-{ctx.factIndex}"
          (#[.text "By the H-coefficient theorem, "] ++ conclDisp) children expected (originOf env inner)
        return some #[step]

    | "paper_cc_compose" =>
        markStepEmitted
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let children : Array ProofNode ←
          if exprContainsSorryAx inner then
            let g ← buildGoalState ctx.tbl expected
            pure #[.step s!"paper-compose-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
          else
            pure #[]
        let content : Array Inline := match reason? with
          | some r =>
              let lead := sanitizeReasonCore r true
              parseProseWithMath s!"{lead}, " ++ conclDisp
          | none =>
              #[.text "By serial composition, "] ++ conclDisp
        let step ← mkVerboseStep ctx s!"paper-compose-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    | "paper_cc_substitute" =>
        markStepEmitted
        let conclDisp ← formatPropSentence ctx.tbl expected "."
        let children : Array ProofNode ←
          if exprContainsSorryAx inner then
            let g ← buildGoalState ctx.tbl expected
            pure #[.step s!"paper-subst-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
          else
            pure #[]
        let content : Array Inline := match label? with
          | some cLbl =>
              if isClauseProseInl conclDisp then
                #[.text "Absorbing ", .inlineMath cLbl, .text " into the distinguisher shows that "] ++ conclDisp
              else
                #[.text "Absorbing ", .inlineMath cLbl, .text " into the distinguisher gives "] ++ conclDisp
          | none =>
              #[.text "By converter absorption, "] ++ conclDisp
        let step ← mkVerboseStep ctx s!"paper-subst-{ctx.factIndex}" content children expected (originOf env inner)
        return some #[step]

    | "paper_reduction" =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let title := reason?.getD s!"Reduction adversary {nm}"
              let rawBody := role?.getD ""
              let (leanTy, roleDesc) ← try
                pure (← ppCleanType ty, ← formatParameterRole ctx.tbl ty)
              catch _ =>
                pure ("", "Constructed reduction adversary.")
              registerScopedNotationInspector (declTagFromCtx ctx) symTex valTex leanTy roleDesc "adversary"
              let goal ← buildGoalState ctx.tbl expected
              markStepEmitted
              let introStep : ProofNode :=
                .step s!"paper-red-intro-{ctx.factIndex}"
                  #[.text "Construct the reduction adversary ", .inlineMath symTex, .text " as follows."]
                  #[] (some goal)
              let pLines := parsePaperReductionLines rawBody
              let boxNode : ProofNode :=
                .pseudocodeBox s!"paper-red-box-{ctx.factIndex}" title "reduction" pLines (some goal)
              let nextTbl ← extendTblWithLocalAlias ctx.tbl fv val symTex valTex
              let rest ← decompileChild { ctx with tbl := nextTbl, isProofStart := false } expected (body.instantiate1 fv)
              return some (#[introStep, boxNode] ++ rest)
        | _ => return some (← decompileChild ctx expected inner)

    | "paper_dist_lower_bound" =>
        let emitLower := fun (isLet : Bool) (hNm : Name) (dom : Expr) (val body : Expr) (bi : BinderInfo) => do
          markStepEmitted
          let propDisp ← formatPropSentence ctx.tbl dom "."
          let children : Array ProofNode ←
            if exprContainsSorryAx val then
              let g ← buildGoalState ctx.tbl dom
              pure #[.step s!"paper-lower-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
            else
              pure #[]
          let step ← mkVerboseStep ctx s!"paper-lower-{ctx.factIndex}"
            (#[.text "This distinguisher achieves the lower bound "] ++ propDisp)
            children dom (originOf env val)
          let cont (fv : Expr) :=
            let nextCtx := { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
            decompileChild nextCtx expected (body.instantiate1 fv)
          let rest ← if isLet then withLetDecl hNm dom val cont else withLocalDecl hNm bi dom cont
          return some (#[step] ++ rest)
        match inner.consumeMData with
        | .letE hNm dom val body _ => emitLower true hNm dom val body .default
        | .app fn val =>
            match fn.consumeMData with
            | .lam hNm dom body bi => emitLower false hNm dom val body bi
            | _ => return some (← decompileChild ctx expected inner)
        | _ =>
            markStepEmitted
            let conclDisp ← formatPropSentence ctx.tbl expected "."
            let children : Array ProofNode ←
              if exprContainsSorryAx inner then
                let g ← buildGoalState ctx.tbl expected
                pure #[.step s!"paper-lower-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
              else
                pure #[]
            let step ← mkVerboseStep ctx s!"paper-lower-{ctx.factIndex}"
              (#[.text "This distinguisher achieves the lower bound "] ++ conclDisp)
              children expected (originOf env inner)
            return some #[step]

    | "paper_contradict_bound" =>
        markStepEmitted
        let children : Array ProofNode ←
          if exprContainsSorryAx inner then
            let g ← buildGoalState ctx.tbl expected
            pure #[.step s!"paper-contra-sorry-{ctx.factIndex}" #[.text "[UNPROVED: sorry]"] #[] (some g)]
          else
            pure #[]
        let reasonTxt := match reason? with
          | some r => stripTrailingPeriod (r.trimAscii.toString.replace "⊥" "the assumed bound")
          | none => "the assumed upper bound"
        let prose := parseProseWithMath s!"This contradicts {reasonTxt}."
        let step ← mkVerboseStep ctx s!"paper-contra-{ctx.factIndex}" prose children expected (originOf env inner)
        return some #[step]

    | _ =>
        return some (← decompileChild ctx expected inner)

initialize
  registerRuleExplainer verboseCCExplainer

end Informalization.Verbose.Trace
