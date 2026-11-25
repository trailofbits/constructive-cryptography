/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Explanation
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Presentation
import Informalization.Core.Overlay
import Informalization.Core.ContextProfile
import Informalization.Core.Ontology
import Informalization.Core.Routine
import Informalization.Core.ProofGraph

/-!
# Kernel-Embedded Presentation Spine (`P0.4`)

Replaces transient `KVMap`/`InfoTree`-only proof structure with **kernel-transparent Spine
combinators** embedded directly in checked proof terms, guaranteeing zero `.olean` vs. Infoview
serialization divergence:

* All 12 Spine node shapes (`overview`, `setupEntity`, `gameDef`, `claimBlock`, `sinceStep`,
  `calcChain`, `caseSplit`, `inductionStep`, `obtainStep`, `sufficesStep`, `concludeStep`,
  `ccSpineLeaf`).
* Kernel-embedded typed interpolation anchors (`spineExpr`, `spineProp`) so `${expr}` and `$[prop]`
  survive `.olean` serialization with exact live `Expr` types and provenance (`ProseTrust`).
* **Non-suppression invariant**: `concludeStep` / `spineConclude` NEVER drops kernel `expected`;
  `setupEntity` ALWAYS records formal `valTex` in symbol cards even when prose is summarized.
* **`ccSpineLeaf` depth-1 isolation**: isolates automated/legacy subproof leaves cleanly at
  depth 1 with `diagramHtml?` capped at `depth ≤ 1`.
-/

namespace Informalization.Core.Spine

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Explanation
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Presentation
open Informalization.Core.Overlay
open Informalization.Core.ContextProfile
open Informalization.Core.Ontology
open Informalization.Core.Routine
open Informalization.Core.ProofGraph

/-! ## 1. Lightweight Source Span (`InfoTree.CustomInfo` ONLY) -/

/-- Source-span annotation recorded in `InfoTree.CustomInfo` for interactive navigation ONLY.
All semantic content and prose structure live inside the kernel proof term. -/
structure SpineSpanInfo where
  kind : String
  idHint : String
  deriving TypeName

/-! ## 2. Kernel-Transparent Spine Combinators (Zero Trust Expansion) -/

/-- Structural kind of a kernel-embedded Spine proof step (12 canonical node constructors). -/
inductive SpineTag : Type
  | overview
  | setupEntity
  | gameDef
  | claimBlock
  | sinceStep
  | calcChain
  | caseSplit
  | inductionStep
  | obtainStep
  | sufficesStep
  | concludeStep
  | ccSpineLeaf
  deriving DecidableEq, Repr, Inhabited

universe u

/-- Kernel-transparent nil anchor list (`Unit`). -/
abbrev spineNil : Unit := ()

/-- Kernel-transparent pair/cons of anchor nodes (`Unit`). -/
abbrev spineCons (_ _ : Unit) : Unit := ()

/-- Kernel-transparent typed expression anchor carrying an arbitrary live `Expr` subterm. -/
abbrev spineExpr {α : Sort u} (_val : α) : Unit := ()

/-- Kernel-transparent proved-proposition anchor carrying a checked witness `h : P`. -/
abbrev spineProp {P : Prop} (_h : P) : Unit := ()

/-- Primary kernel-embedded Spine wrapper. Completely defeq-transparent (`= proof`). -/
abbrev spineNode
    (_tag : SpineTag) (_idHint : String) (_text : String)
    (_startsPara : Bool) (_leadHeading : String) (_trust : String)
    (_witness : Unit) {P : Prop} (proof : P) : P :=
  proof

/-- Non-suppressing kernel conclusion wrapper: carries prose intuition + anchors while
preserving the exact checked conclusion `proof : P`. -/
abbrev spineConclude
    (_reason : String) (_startsPara : Bool) (_witness : Unit)
    {P : Prop} (proof : P) : P :=
  proof

/-- Kernel-embedded `With role` override bound directly to live typed expression `_val`. -/
abbrev spineRole {α : Sort u} (_val : α) (_role : String) {P : Prop} (proof : P) : P :=
  proof

/-- Kernel-embedded scoped paper notation bound directly to live typed expression `_val`. -/
abbrev spineNotation {α : Sort u} (_val : α) (_sym _gloss : String)
    {P : Prop} (proof : P) : P :=
  proof

/-! ## 3. Spine Detection & Anchor Extraction -/

/-- Fast $O(\text{DAG})$ test whether an expression carries kernel-embedded Spine nodes. -/
def hasPresentationSpine (e : Expr) : Bool :=
  e.foldConsts (init := false) fun n acc =>
    acc || n == ``spineNode || n == ``spineConclude || n == ``spineRole || n == ``spineNotation

private def decodeStringLit? (e : Expr) : Option String :=
  match e.consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

private def decodeBoolConst? (e : Expr) : Option Bool :=
  match e.consumeMData with
  | .const ``Bool.true _ => some true
  | .const ``Bool.false _ => some false
  | _ => none

private def decodeSpineTag? (e : Expr) : Option SpineTag :=
  match e.consumeMData with
  | .const ``SpineTag.overview _ => some .overview
  | .const ``SpineTag.setupEntity _ => some .setupEntity
  | .const ``SpineTag.gameDef _ => some .gameDef
  | .const ``SpineTag.claimBlock _ => some .claimBlock
  | .const ``SpineTag.sinceStep _ => some .sinceStep
  | .const ``SpineTag.calcChain _ => some .calcChain
  | .const ``SpineTag.caseSplit _ => some .caseSplit
  | .const ``SpineTag.inductionStep _ => some .inductionStep
  | .const ``SpineTag.obtainStep _ => some .obtainStep
  | .const ``SpineTag.sufficesStep _ => some .sufficesStep
  | .const ``SpineTag.concludeStep _ => some .concludeStep
  | .const ``SpineTag.ccSpineLeaf _ => some .ccSpineLeaf
  | _ => none

private def decodeProseTrust? (s : String) : Option ProseTrust :=
  match s with
  | "kernelFormula" => some .kernelFormula
  | "kernelProvedClaim" => some .kernelProvedClaim
  | "typedRef" => some .typedRef
  | "intuitionGloss" => some .intuitionGloss
  | _ => none

/-- Extract ordered `(isPropAnchor, expr)` anchors from a `spineCons`/`spineNil` kernel tree.
* For `spineExpr {α} val`: returns `(false, val)`
* For `spineProp {P} h`: returns `(true, P)` (and carries checked witness `h`). -/
partial def extractAnchorArray (w : Expr) : Array (Bool × Expr) :=
  let c := w.consumeMData
  let fn := c.getAppFn.consumeMData
  let args := c.getAppArgs
  if fn.isConstOf ``spineCons && args.size ≥ 2 then
    extractAnchorArray args[0]! ++ extractAnchorArray args[1]!
  else if fn.isConstOf ``spineExpr && args.size ≥ 2 then
    #[(false, args[1]!)]
  else if fn.isConstOf ``spineProp && args.size ≥ 1 then
    #[(true, args[0]!)]
  else
    #[]

private def findProjectDataKey? (env : Environment) (e : Expr) : Option String :=
  match e.getAppFn.consumeMData with
  | .const c _ =>
      if isCoreOrMathlibIn env c || Lean.isPrivateName c then none
      else match env.find? c with
        | some (.defnInfo _) | some (.inductInfo _) => some c.toString
        | _ => none
  | _ => none

/-- Render a Spine template string (containing optional `@@EXPR:i@@` / `@@PROP:i@@` sentinels)
against extracted kernel anchor expressions, tagging each resulting `Inline` with exact
`ProseTrust` and optional inspector `dataKey`. -/
def renderSpineTemplate (tbl : SymbolTable) (tmpl : String)
    (anchors : Array (Bool × Expr)) :
    MetaM (Array Inline × Array (Option ProseTrust × Option String)) := do
  let env ← getEnv
  let mut inls : Array Inline := #[]
  let mut metas : Array (Option ProseTrust × Option String) := #[]
  let pushTextSeg (seg : String) (inls : Array Inline)
      (metas : Array (Option ProseTrust × Option String)) :=
    let parsed := parseProseWithMath seg
    let nextInls := inls ++ parsed
    let nextMetas := metas ++ parsed.map fun _ => (some .intuitionGloss, none)
    (nextInls, nextMetas)
  let arr := tmpl.toList.toArray
  let mut textBuf : List Char := []
  let mut i := 0
  while i < arr.size do
    let isExprTag := i + 7 ≤ arr.size &&
      String.ofList (arr.extract i (i + 7)).toList == "@@EXPR:"
    let isPropTag := i + 7 ≤ arr.size &&
      String.ofList (arr.extract i (i + 7)).toList == "@@PROP:"
    if isExprTag || isPropTag then
      let mut j := i + 7
      let mut digits : List Char := []
      while j < arr.size && arr[j]!.isDigit do
        digits := arr[j]! :: digits
        j := j + 1
      if j + 2 ≤ arr.size && arr[j]! == '@' && arr[j + 1]! == '@' && !digits.isEmpty then
        let idx := (String.ofList digits.reverse).toNat!
        if !textBuf.isEmpty then
          let seg := String.ofList textBuf.reverse
          let (ni, nm) := pushTextSeg seg inls metas
          inls := ni; metas := nm
          textBuf := []
        if let some (isPropAnchor, anchorExpr) := anchors[idx]? then
          let dk? := findProjectDataKey? env anchorExpr
          if isPropAnchor then
            let rendered ← renderProposition tbl anchorExpr
            inls := inls ++ rendered
            for r in rendered do
              let itemDk? := match r with
                | .inlineMath _ | .displayMath _ _ => dk?
                | _ => none
              metas := metas.push (some .kernelProvedClaim, itemDk?)
          else
            let tex ← exprToLatex anchorExpr tbl
            inls := inls.push (.inlineMath tex)
            metas := metas.push (some .kernelFormula, dk?)
        i := j + 2
        continue
    textBuf := arr[i]! :: textBuf
    i := i + 1
  if !textBuf.isEmpty then
    let seg := String.ofList textBuf.reverse
    let (ni, nm) := pushTextSeg seg inls metas
    inls := ni; metas := nm
  return (inls, metas)

/-! ## 4. Top-Level Role & Notation Extraction from Kernel Terms (Ontology Hooks) -/

private partial def collectSpineRolesAux (fvars : Array Expr) (e : Expr)
    (acc : Std.HashMap FVarId String) (fuel : Nat := 64) :
    MetaM (Std.HashMap FVarId String) := do
  if fuel == 0 then return acc
  let c := e.consumeMData
  let fn := c.getAppFn.consumeMData
  let args := c.getAppArgs
  if fn.isConstOf ``spineRole && args.size ≥ 5 then
    let val := args[1]!
    let roleStr := decodeStringLit? args[2]! |>.getD ""
    let rest := args[4]!
    let mut nextAcc := acc
    if !roleStr.isEmpty then
      if let .fvar id := val.consumeMData then
        nextAcc := nextAcc.insert id
          (Informalization.Core.ContextProfile.mergeRoleStrings nextAcc[id]? roleStr)
    return ← collectSpineRolesAux fvars rest nextAcc (fuel - 1)
  if fn.isConstOf ``spineNotation && args.size ≥ 6 then
    return ← collectSpineRolesAux fvars args[5]! acc (fuel - 1)
  if fn.isConstOf ``spineNode && args.size ≥ 9 then
    return ← collectSpineRolesAux fvars args[8]! acc (fuel - 1)
  match c with
  | .letE _ _ val body _ => collectSpineRolesAux fvars (body.instantiate1 val) acc (fuel - 1)
  | .app (.lam _ _ body _) val => collectSpineRolesAux fvars (body.instantiate1 val) acc (fuel - 1)
  | _ => return acc

private partial def collectSpineNotationsAux (e : Expr) (fuel : Nat := 64) :
    Array (Expr × String × Option String) :=
  if fuel == 0 then #[]
  else
    let c := e.consumeMData
    let fn := c.getAppFn.consumeMData
    let args := c.getAppArgs
    if fn.isConstOf ``spineNotation && args.size ≥ 6 then
      let val := args[1]!
      let sym := decodeStringLit? args[2]! |>.getD ""
      let gloss := decodeStringLit? args[3]! |>.getD ""
      let rest := collectSpineNotationsAux args[5]! (fuel - 1)
      if sym.isEmpty then rest
      else #[(val, sym, if gloss.isEmpty then none else some gloss)] ++ rest
    else if fn.isConstOf ``spineRole && args.size ≥ 5 then
      collectSpineNotationsAux args[4]! (fuel - 1)
    else if fn.isConstOf ``spineNode && args.size ≥ 9 then
      collectSpineNotationsAux args[8]! (fuel - 1)
    else match c with
      | .letE _ _ val body _ => collectSpineNotationsAux (body.instantiate1 val) (fuel - 1)
      | .app (.lam _ _ body _) val => collectSpineNotationsAux (body.instantiate1 val) (fuel - 1)
      | _ => #[]

initialize
  registerTopProofRoleHook fun cur fvars => collectSpineRolesAux fvars cur {}
  registerTopProofNotationHook fun cur _ => pure (collectSpineNotationsAux cur)

/-! ## 5. Top-Down Spine Extractor (`RuleExplainer`, Priority 1000) -/

private def appendPeriodClean (inls : Array Inline) (metas : Array (Option ProseTrust × Option String)) :
    Array Inline × Array (Option ProseTrust × Option String) :=
  if inls.isEmpty then (inls, metas)
  else match inls.back? with
    | some (.displayMath _ _) => (inls, metas)
    | some (.text t) =>
        let trimmed := t.trimAsciiEnd.toString
        if trimmed.endsWith "." || trimmed.endsWith ":" then (inls, metas)
        else (inls.pop.push (.text (trimmed ++ ".")), metas)
    | _ => (inls.push (.text "."), metas.push (some .intuitionGloss, none))

private def isForwardEntityRole (leadHeading : String) : Bool :=
  let low := leadHeading.toLower
  (low.splitOn "adversary").length > 1 || (low.splitOn "simulator").length > 1

private def makeConcludeContent (ctx : DecompCtx) (expected : Expr)
    (reason : String) (witness : Expr) :
    MetaM (Array Inline × Array (Option ProseTrust × Option String)) := do
  let anchors := extractAnchorArray witness
  let conclInl ← renderProposition ctx.tbl expected
  let conclMetas : Array (Option ProseTrust × Option String) :=
    conclInl.map fun
      | .inlineMath _ | .displayMath _ _ => (some .kernelProvedClaim, none)
      | _ => (some .kernelProvedClaim, none)
  if reason.trimAscii.isEmpty then
    let lead := #[.text "Therefore, "] ++ conclInl
    let lm := #[(some .intuitionGloss, none)] ++ conclMetas
    return appendPeriodClean lead lm
  else
    let (rInls, rMetas) ← renderSpineTemplate ctx.tbl reason anchors
    let combined := rInls ++ #[.text ", which establishes "] ++ conclInl
    let cm := rMetas ++ #[(some .intuitionGloss, none)] ++ conclMetas
    return appendPeriodClean combined cm

/-- Kernel-embedded Spine `RuleExplainer`. Takes priority over legacy heuristics whenever
`spineNode` / `spineConclude` / `spineRole` / `spineNotation` is present in the proof term. -/
partial def extractSpineNode :
    DecompCtx → DecompileChild → Expr → Expr →
    StateRefT DiscourseState MetaM (Option (Array ProofNode)) := fun ctx decompileChild expected proof => do
  let c := proof.consumeMData
  let fn := c.getAppFn.consumeMData
  let args := c.getAppArgs
  let subCtx : DecompCtx := {
    ctx with
    lastFactFVar? := none
    factIndex := 0
    atRootConclusion := false
    isProofStart := false
    isClosingGoal := false
  }
  -- Transparent kernel role / notation wrappers
  if fn.isConstOf ``spineRole && args.size ≥ 5 then
    return some (← decompileChild ctx expected args[4]!)
  if fn.isConstOf ``spineNotation && args.size ≥ 6 then
    let val := args[1]!
    let sym := decodeStringLit? args[2]! |>.getD ""
    let gloss := decodeStringLit? args[3]! |>.getD ""
    let rest := match args[5]!.consumeMData with
      | .app (.lam _ _ b _) v => b.instantiate1 v
      | other => other
    if !sym.isEmpty then
      try
        let normVal ← normalizeForPresentation val
        let tblWithout := { ctx.tbl with exprAliases := ctx.tbl.exprAliases.filter (·.2 != sym) }
        let rhsTex ← exprToLatex normVal tblWithout
        let leanTy ← try
          let fmt ← ppExpr (← inferType normVal)
          pure fmt.pretty
        catch _ => pure ""
        let desc := if gloss.trimAscii.isEmpty then "Scoped paper notation." else gloss
        registerProofNotationInspector {
          key := s!"spine:notation:{sym}"
          display := sym
          kind := .localShorthand s!"{sym} = {rhsTex}" desc
          leanName? := none
          leanType := leanTy
          roleBadge? := some "notation"
        }
      catch _ => pure ()
      let nextTbl ← ctx.tbl.withNormalizedExprAlias val sym
      let nextTbl := nextTbl.withExprAlias val.consumeMData sym
      return some (← decompileChild { ctx with tbl := nextTbl } expected rest)
    return some (← decompileChild ctx expected rest)

  -- Non-suppressing conclusion wrapper (`spineConclude`)
  if fn.isConstOf ``spineConclude && args.size ≥ 5 then
    let reason := decodeStringLit? args[0]! |>.getD ""
    let startsPara := decodeBoolConst? args[1]! |>.getD false
    let witness := args[2]!
    let inner := args[4]!
    let (content, inlineMeta) ← makeConcludeContent ctx expected reason witness
    let children ← decompileChild subCtx expected inner
    let goal ← buildGoalState ctx.tbl expected
    return some #[.step s!"spine-conclude-{ctx.factIndex}" content children (some goal)
      none none false false startsPara none (some .kernelProvedClaim) inlineMeta]

  -- Main 12-kind `spineNode`
  if fn.isConstOf ``spineNode && args.size ≥ 9 then
    let some tag := decodeSpineTag? args[0]! | return none
    let idHint := decodeStringLit? args[1]! |>.getD "step"
    let tmpl := decodeStringLit? args[2]! |>.getD ""
    let startsPara := decodeBoolConst? args[3]! |>.getD false
    let leadHeadRaw := decodeStringLit? args[4]! |>.getD ""
    let leadHead? := if leadHeadRaw.trimAscii.isEmpty then none else some leadHeadRaw
    let trustStr := decodeStringLit? args[5]! |>.getD ""
    let nodeTrust? := decodeProseTrust? trustStr
    let witness := args[6]!
    let inner := args[8]!
    let anchors := extractAnchorArray witness
    let nodeId := s!"spine-{idHint}-{ctx.factIndex}"
    let goal ← buildGoalState ctx.tbl expected

    match tag with
    | .overview =>
        let (inls, im) ← renderSpineTemplate ctx.tbl tmpl anchors
        let (content, inlineMeta) := appendPeriodClean inls im
        let stp := ProofNode.step nodeId content #[] (some goal)
          none none false false true leadHead? (nodeTrust? <|> some .intuitionGloss) inlineMeta
        let rest ← decompileChild { ctx with isProofStart := false } expected inner
        return some (#[stp] ++ rest)

    | .setupEntity | .gameDef =>
        let isGame := tag == .gameDef
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            return ← withLetDecl nm ty val fun fv => do
              let symTex ← exprToLatex fv ctx.tbl
              let valTex ← exprToLatex val ctx.tbl
              let (tInl, tMeta) ←
                if tmpl.trimAscii.isEmpty then pure (#[], #[])
                else renderSpineTemplate ctx.tbl tmpl anchors
              let glossSummary := String.intercalate "" (tInl.toList.map Inline.collectText) |>.trimAscii.toString
              let badge :=
                if isGame then "game"
                else if leadHead? == some "Adversary" then "adversary"
                else if leadHead? == some "Hybrid" then "hybrid"
                else "notation"
              try
                let leanTy ← (← ppExpr ty).pretty |> pure
                registerProofNotationInspector {
                  key := s!"spine:{badge}:{symTex}"
                  display := symTex
                  kind := .localShorthand s!"{symTex} = {valTex}"
                    (if glossSummary.isEmpty then s!"Defined {badge}." else glossSummary)
                  leanName? := none
                  leanType := leanTy
                  roleBadge? := some badge
                }
              catch _ => pure ()
              let (inls, im) ←
                if tInl.isEmpty then
                  let base : Array Inline := #[.text "Define ", .inlineMath s!"{symTex} := {valTex}"]
                  pure (appendPeriodClean base #[(some .intuitionGloss, none), (some .kernelFormula, none)])
                else
                  -- Non-suppression: keep explicit checked `sym := val` accessible in prose
                  let defInl := #[.inlineMath s!"{symTex} := {valTex}", .text " ("] ++ tInl ++ #[.text ")"]
                  let defMeta := #[(some .kernelFormula, none), (some .intuitionGloss, none)] ++ tMeta ++ #[(some .intuitionGloss, none)]
                  pure (appendPeriodClean (#[.text "Define "] ++ defInl) (#[(some .intuitionGloss, none)] ++ defMeta))
              let hd? :=
                if isGame then
                  let cleanNm := cleanBinderName nm "G"
                  leadHead? <|> some s!"{capitalizeFirst cleanNm}."
                else leadHead?
              let sp := isGame || startsPara
              let rest ← decompileChild { ctx with isProofStart := false } expected (body.instantiate1 fv)
              let stp := ProofNode.step nodeId inls #[] (some goal)
                none none false false sp hd? (nodeTrust? <|> some .kernelFormula) im
              return some (#[stp] ++ rest)
        | _ =>
            let (inls, im) ← renderSpineTemplate ctx.tbl tmpl anchors
            let (content, inlineMeta) := appendPeriodClean inls im
            let stp := ProofNode.step nodeId content #[] (some goal)
              none none false false startsPara leadHead? (nodeTrust? <|> some .kernelFormula) inlineMeta
            let rest ← decompileChild subCtx expected inner
            return some (#[stp] ++ rest)

    | .claimBlock =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            let children ← decompileChild subCtx ty val
            let propInl ← renderProposition ctx.tbl ty
            let propMeta : Array (Option ProseTrust × Option String) :=
              propInl.map fun _ => (some .kernelProvedClaim, none)
            let (inls, im) ←
              if tmpl.trimAscii.isEmpty then
                let lead := if ctx.factIndex == 0 then "We claim that " else "Next, we claim that "
                pure (appendPeriodClean (#[.text lead] ++ propInl) (#[(some .intuitionGloss, none)] ++ propMeta))
              else
                let (tInl, tMeta) ← renderSpineTemplate ctx.tbl tmpl anchors
                pure (appendPeriodClean
                  (#[.text "We claim "] ++ propInl ++ #[.text " ("] ++ tInl ++ #[.text ")"])
                  (#[(some .intuitionGloss, none)] ++ propMeta ++ #[(some .intuitionGloss, none)] ++ tMeta ++ #[(some .intuitionGloss, none)]))
            let subGoal ← buildGoalState ctx.tbl ty
            let stp := ProofNode.step nodeId inls children (some subGoal)
              none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) im
            let rest ← withLetDecl nm ty val fun fv =>
              decompileChild { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
                expected (body.instantiate1 fv)
            return some (#[stp] ++ rest)
        | _ =>
            let children ← decompileChild subCtx expected inner
            let (inls, im) ← renderSpineTemplate ctx.tbl tmpl anchors
            let (content, inlineMeta) := appendPeriodClean inls im
            return some #[.step nodeId content children (some goal)
              none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) inlineMeta]

    | .sinceStep =>
        match inner.consumeMData with
        | .letE nm ty val body _ =>
            let children ← decompileChild subCtx ty val
            let propInl ← renderProposition ctx.tbl ty
            let propMeta : Array (Option ProseTrust × Option String) :=
              propInl.map fun _ => (some .kernelProvedClaim, none)
            let premCount := anchors.size
            let leadStr := if premCount ≥ 2 then "Combining the preceding assumptions, we obtain "
                           else "Since the cited bound holds, we obtain "
            let (content, inlineMeta) ←
              if tmpl.trimAscii.isEmpty then
                pure (appendPeriodClean (#[.text leadStr] ++ propInl) (#[(some .intuitionGloss, none)] ++ propMeta))
              else
                let (tInl, tMeta) ← renderSpineTemplate ctx.tbl tmpl anchors
                pure (appendPeriodClean (tInl ++ #[.text ": "] ++ propInl)
                  (tMeta ++ #[(some .intuitionGloss, none)] ++ propMeta))
            let subGoal ← buildGoalState ctx.tbl ty
            let stp := ProofNode.step nodeId content children (some subGoal)
              none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) inlineMeta
            let rest ← withLetDecl nm ty val fun fv =>
              decompileChild { ctx with lastFactFVar? := some fv.fvarId!, factIndex := ctx.factIndex + 1, isProofStart := false }
                expected (body.instantiate1 fv)
            return some (#[stp] ++ rest)
        | _ =>
            let (content, inlineMeta) ← makeConcludeContent ctx expected tmpl witness
            let children ← decompileChild subCtx expected inner
            return some #[.step nodeId content children (some goal)
              none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) inlineMeta]

    | .calcChain =>
        let children ← decompileChild ctx expected inner
        if tmpl.trimAscii.isEmpty then
          return some children
        let (inls, im) ← renderSpineTemplate ctx.tbl tmpl anchors
        let (content, inlineMeta) := appendPeriodClean inls im
        return some #[.step nodeId content children (some goal)
          none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) inlineMeta]

    | .caseSplit | .inductionStep | .obtainStep =>
        let children ← decompileChild subCtx expected inner
        let defaultLead := match tag with
          | .caseSplit => "By case analysis"
          | .inductionStep => "Proceeding by induction"
          | _ => "Unpacking the existential witness"
        let (content, inlineMeta) ←
          if tmpl.trimAscii.isEmpty then
            let conclInl ← renderProposition ctx.tbl expected
            let cm := conclInl.map fun _ => (some .kernelProvedClaim, none)
            pure (appendPeriodClean (#[.text s!"{defaultLead}, "] ++ conclInl) (#[(some .intuitionGloss, none)] ++ cm))
          else
            let (tInl, tMeta) ← renderSpineTemplate ctx.tbl tmpl anchors
            pure (appendPeriodClean tInl tMeta)
        return some #[.step nodeId content children (some goal)
          none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) inlineMeta]

    | .sufficesStep =>
        let children ← decompileChild subCtx expected inner
        let subProp? : Option Expr := match inner.consumeMData with
          | .letE _ subTy _ _ _ => some subTy
          | _ => none
        let targetProp := subProp?.getD expected
        let propInl ← renderProposition ctx.tbl targetProp
        let propMeta : Array (Option ProseTrust × Option String) :=
          propInl.map fun _ => (some .kernelProvedClaim, none)
        let (inls, im) ←
          if tmpl.trimAscii.isEmpty then
            pure (#[.text "It suffices to show "] ++ propInl, #[(some .intuitionGloss, none)] ++ propMeta)
          else
            let (tInl, tMeta) ← renderSpineTemplate ctx.tbl tmpl anchors
            pure (tInl ++ #[.text ", it suffices to show "] ++ propInl,
              tMeta ++ #[(some .intuitionGloss, none)] ++ propMeta)
        let (content, inlineMeta) := appendPeriodClean inls im
        return some #[.step nodeId content children (some goal)
          none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) inlineMeta]

    | .concludeStep =>
        let (content, inlineMeta) ← makeConcludeContent ctx expected tmpl witness
        let children ← decompileChild subCtx expected inner
        return some #[.step nodeId content children (some goal)
          none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) inlineMeta]

    | .ccSpineLeaf =>
        -- Isolated depth-1 CC leaf: keep lemma expansion tightly bounded at depth ≤ 1
        let leafCtx : DecompCtx := {
          ctx with
          config := { ctx.config with maxLemmaDepth := ctx.lemmaDepth + 1 }
          atRootConclusion := false
          isProofStart := false
        }
        let children ← decompileChild leafCtx expected inner
        if tmpl.trimAscii.isEmpty then
          return some children
        let (inls, im) ← renderSpineTemplate ctx.tbl tmpl anchors
        let (content, inlineMeta) := appendPeriodClean inls im
        return some #[.step nodeId content children (some goal)
          none none false false startsPara leadHead? (nodeTrust? <|> some .kernelProvedClaim) inlineMeta]

  return none

def spineRuleExplainer : RuleExplainer where
  priority := 1000
  explain := extractSpineNode

initialize
  registerRuleExplainer spineRuleExplainer

end Informalization.Core.Spine
