/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Ontology
import Informalization.Core.Presentation
import Informalization.Core.Overlay
import Informalization.Core.Explanation
import Informalization.CC.Registry

/-!
# Authentic Constructive Cryptography Ontology & 2D LaTeX Handlers

Registers domain-specific `LeanTeX.AppHandler`, `Ontology.TypeHandler`, and
`Ontology.PropHandler` rules grounded strictly in the Constructive Cryptography
literature (Maurer–Renner 2016, Maurer 2011, Jost–Maurer 2020, CR18, Banfi 2023):

* **Resources**: *"a resource $R$ with interface $A$"* or *"with interfaces $H$ and $P$"*
  (arity-driven singular/plural inflection via `Ontology.interfaceAccessory`).
* **Converters**: *"a converter $\alpha$ with inside interface $B$ and outside interface $A$"*.
* **Attachment**: juxtaposition $\alpha R$ (no `•` bullet); right/adversarial attachment
  $S\sigma$ for `H ◁ σ`; left/honest application $\kappa R$ for `κ ▷ P`.
* **Constructions & Indifferentiability**: $\mathcal{R} \xrightarrow{\pi} \mathcal{S}$,
  $\mathcal{R} \xrightarrow{\pi;\,\varepsilon} \mathcal{S}$, and $(\mathcal{S}^*)^\varepsilon$
  for `epsilonRelaxation ε (simulatorImage Σ 𝒮)`.
* **Distinguishing & Substitution**: $\Delta(R, S)$, $R \simeq_\varepsilon S$, $R \parallel S$,
  distinguisher absorption $D\alpha$, and closure under absorbing $\alpha$.
* **Games & MBOs**: $G \mathrel{|\!\equiv} T$ and the underlying system $G^-$ obtained by
  ignoring the MBO.
-/

namespace Informalization.CC.Ontology

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Explanation
open Informalization.CC.Registry

/-! ## Helpers for Extracting CC AST Shapes -/

private def argFromEnd? (args : Array Expr) (offset : Nat) : Option Expr :=
  if offset < args.size then args[args.size - 1 - offset]? else none

/-- Unwrap a singleton specification `{R}` to `R` (MR16 convention: writing $R \xrightarrow{\pi} S$
in lieu of $\{R\} \xrightarrow{\pi} \{S\}$). -/
private def unwrapSingletonSpec (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOf ``Singleton.singleton then
    match e.getAppArgs.back? with
    | some inner => inner
    | none => e
  else e

/-- Recognize `H ◁ σ` (`whiskerLeft H σ`), returning `(H, σ)`. -/
private def matchWhiskerLeft? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.getAppFn.consumeMData.isConstOf whiskerLeftName then
    let args := e.getAppArgs
    if args.size ≥ 5 then
      -- whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : X ⊗ Y₁ ⟶ X ⊗ Y₂
      some (args[args.size - 4]!, args[args.size - 1]!)
    else none
  else none

/-- Recognize `κ ▷ P` (`whiskerRight κ P`), returning `(κ, P)`. -/
private def matchWhiskerRight? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.getAppFn.consumeMData.isConstOf whiskerRightName then
    let args := e.getAppArgs
    if args.size ≥ 5 then
      -- whiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) : X₁ ⊗ Y ⟶ X₂ ⊗ Y
      some (args[args.size - 2]!, args[args.size - 1]!)
    else none
  else none

private def countHeadForalls : Expr → Nat
  | .forallE _ _ b _ => countHeadForalls b + 1
  | .mdata _ b => countHeadForalls b
  | _ => 0

private def epsilonBaseArity? (env : Environment) (fn : Expr) : Option Nat :=
  match fn.constName? with
  | some head =>
      if head == epsilonRelaxationName || head == specEpsilonRelaxationName then
        (env.find? head).map (fun info => countHeadForalls info.type)
      else none
  | none => none

/-- Recognize an unapplied `epsilonRelaxation ε` expression, returning `ε`. -/
private def matchEpsilonRelaxationFn? (env : Environment) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  match epsilonBaseArity? env fn with
  | some baseArity =>
      if baseArity > 0 && args.size == baseArity then args[baseArity - 1]? else none
  | none => none

/-- Recognize `(epsilonRelaxation ε) S` (directly after `DFunLike.coe` stripping, via
`DFunLike.coe`, or via `Relaxation.relaxedBy`), returning `(ε, S)`. -/
private def matchEpsilonRelaxationApp? (env : Environment) (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if let some baseArity := epsilonBaseArity? env fn then
    if baseArity > 0 && args.size ≥ baseArity + 1 then
      some (args[baseArity - 1]!, args[baseArity]!)
    else none
  else if fn.isConstOf ``DFunLike.coe && args.size ≥ 6 then
    let relaxFn := args[args.size - 2]!
    let specArg := args[args.size - 1]!
    match matchEpsilonRelaxationFn? env relaxFn with
    | some eps => some (eps, specArg)
    | none => none
  else if fn.isConstOf relaxedByName && args.size ≥ 2 then
    let specArg := args[args.size - 2]!
    let relaxFn := args[args.size - 1]!
    match matchEpsilonRelaxationFn? env relaxFn with
    | some eps => some (eps, specArg)
    | none => none
  else none

/-- Recognize `simulatorImage Σ S` or `star Σ S`, returning `(Σ, S)`. -/
private def matchSimulatorOrStar? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if (fn.isConstOf simulatorImageName || fn.isConstOf starName) && args.size ≥ 2 then
    some (args[args.size - 2]!, args[args.size - 1]!)
  else none

/-- Check whether `HSMul.hSMul` is a CC converter attachment action (rather than numeric scalar
multiplication). -/
private def isCCAttachmentHSMul (args : Array Expr) : MetaM Bool := do
  if args.size < 6 then return false
  let inst := args[3]!.consumeMData
  let instHead := inst.getAppFn.consumeMData
  if instHead.isConstOf instHSMulConverterResourceName ||
     instHead.isConstOf instHSMulTypedSystemName ||
     instHead.isConstOf instHSMulHomTypedSystemName ||
     instHead.isConstOf instHSMulConverterGameName then
    return true
  let convTy := args[0]!
  let resTy := args[1]!
  let isConv := (← converterInterfaces? convTy).isSome
  let isTarget := (← resourceInterface? resTy).isSome || (← gameInterface? resTy).isSome
  return isConv && isTarget

/-- Join two juxtaposed CC math factors (`\alpha R`, `S\sigma`, `\mathrm{protocol}\,\mathrm{real}`):
inserts a thin space `\,` whenever two multi-letter `\mathrm{...}` tokens would otherwise touch. -/
private def juxtapose (left right : String) : String :=
  if left.startsWith "\\mathrm{" || right.startsWith "\\mathrm{" then
    s!"{left}\\,{right}"
  else if left.endsWith "}" || left.endsWith ")" then
    s!"{left}{right}"
  else
    s!"{left} {right}"

/-- Render converter attachment `conv • res` in authentic Maurer–Renner paper juxtaposition:
* `(H ◁ σ) • S` renders as `S\sigma` (right/adversarial interface attachment);
* `(κ ▷ P) • R` renders as `\kappa R` (left/honest interface application);
* `α • R` renders as `\alpha R` (no `•` bullet). -/
private def renderAttachmentLatex (rec : Recurse) (conv res : Expr) : MetaM (String × Nat) := do
  let conv := conv.consumeMData
  let res := res.consumeMData
  if let some (_, sigma) := matchWhiskerLeft? conv then
    let rTex ← rec 78 res
    let sTex ← rec 78 sigma
    return (juxtapose rTex sTex, 78)
  if let some (kappa, _) := matchWhiskerRight? conv then
    let kTex ← rec 78 kappa
    let rTex ← rec 78 res
    return (juxtapose kTex rTex, 78)
  let cTex ← rec 78 conv
  let rTex ← rec 78 res
  return (juxtapose cTex rTex, 78)

/-- Render a specification target cleanly, unwrapping singletons and formatting
`(S^*)^\varepsilon` for `epsilonRelaxation ε (simulatorImage Σ S)` or `star Σ S`. -/
private def renderSpecLatex (tbl : SymbolTable) (rec : Recurse) (spec : Expr) : MetaM String := do
  let _ := tbl
  let env ← getEnv
  if let some (eps, inner) := matchEpsilonRelaxationApp? env spec then
    let epsTex ← rec 0 eps
    if let some (_, base) := matchSimulatorOrStar? inner then
      let baseTex ← rec 82 (unwrapSingletonSpec base)
      return "\\left(" ++ baseTex ++ "^{*}\\!\\right)^{" ++ epsTex ++ "}"
    else
      let innerTex ← rec 82 (unwrapSingletonSpec inner)
      if (innerTex.splitOn "^").length > 1 || innerTex.contains ' ' then
        return "\\left(" ++ innerTex ++ "\\right)^{" ++ epsTex ++ "}"
      else
        return innerTex ++ "^{" ++ epsTex ++ "}"
  if let some (_, base) := matchSimulatorOrStar? spec then
    let baseTex ← rec 82 (unwrapSingletonSpec base)
    return baseTex ++ "^{*}"
  let specC := spec.consumeMData
  if specC.getAppFn.consumeMData.isConstOf `Commons.Indifferentiability.specification &&
     specC.getAppArgs.size ≥ 3 then
    let args := specC.getAppArgs
    let baseTex ← rec 82 (unwrapSingletonSpec args[args.size - 3]!)
    let epsTex ← rec 0 args[args.size - 1]!
    return "\\left(" ++ baseTex ++ "^{*}\\!\\right)^{" ++ epsTex ++ "}"
  rec 60 (unwrapSingletonSpec spec)

/-! ## 1. 2D LaTeX Application Handlers (`LeanTeX.AppHandler`) -/

private def attachHandler : AppHandler where
  head := attachName
  priority := 200
  run := fun _ rec _ args => do
    let some res := argFromEnd? args 0 | return none
    let some conv := argFromEnd? args 1 | return none
    return some (← renderAttachmentLatex rec conv res)

private def typedAttachHandler : AppHandler where
  head := typedConverterAttachName
  priority := 200
  run := fun _ rec _ args => do
    let some res := argFromEnd? args 0 | return none
    let some conv := argFromEnd? args 1 | return none
    return some (← renderAttachmentLatex rec conv res)

private def attachGameHandler : AppHandler where
  head := attachGameName
  priority := 200
  run := fun _ rec _ args => do
    let some game := argFromEnd? args 0 | return none
    let some conv := argFromEnd? args 1 | return none
    return some (← renderAttachmentLatex rec conv game)

private def typedAttachGameHandler : AppHandler where
  head := typedConverterAttachGameName
  priority := 200
  run := fun _ rec _ args => do
    let some game := argFromEnd? args 0 | return none
    let some conv := argFromEnd? args 1 | return none
    return some (← renderAttachmentLatex rec conv game)

private def hSMulAttachHandler : AppHandler where
  head := ``HSMul.hSMul
  priority := 200
  run := fun _ rec _ args => do
    unless ← isCCAttachmentHSMul args do return none
    let some res := argFromEnd? args 0 | return none
    let some conv := argFromEnd? args 1 | return none
    return some (← renderAttachmentLatex rec conv res)

private def whiskerLeftHandler : AppHandler where
  head := whiskerLeftName
  priority := 180
  run := fun _ rec e _ => do
    let some (h, sigma) := matchWhiskerLeft? e | return none
    let hTex ← rec 80 h
    let sTex ← rec 65 sigma
    return some ("\\mathbf{1}_{" ++ hTex ++ "} \\parallel " ++ sTex, 60)

private def whiskerRightHandler : AppHandler where
  head := whiskerRightName
  priority := 180
  run := fun _ rec e _ => do
    let some (kappa, p) := matchWhiskerRight? e | return none
    let kTex ← rec 65 kappa
    let pTex ← rec 80 p
    return some (kTex ++ " \\parallel \\mathbf{1}_{" ++ pTex ++ "}", 60)

private def compHandler : AppHandler where
  head := categoryCompName
  priority := 170
  run := fun _ rec e args => do
    let ty ← inferType e
    unless (← converterInterfaces? ty).isSome do return none
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    return some (s!"{← rec 72 l} \\circ {← rec 72 r}", 72)

private def typedCompHandler : AppHandler where
  head := typedConverterCompName
  priority := 170
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    return some (s!"{← rec 72 l} \\circ {← rec 72 r}", 72)

private def idHandler : AppHandler where
  head := categoryIdName
  priority := 170
  run := fun _ rec e args => do
    let ty ← inferType e
    unless (← converterInterfaces? ty).isSome do return none
    match argFromEnd? args 0 with
    | some iface => return some ("\\mathbf{1}_{" ++ (← rec 80 iface) ++ "}", 90)
    | none => return some ("\\mathbf{1}", 90)

private def typedIdHandler : AppHandler where
  head := typedConverterIdName
  priority := 170
  run := fun _ rec _ args => do
    match argFromEnd? args 0 with
    | some iface => return some ("\\mathbf{1}_{" ++ (← rec 80 iface) ++ "}", 90)
    | none => return some ("\\mathbf{1}", 90)

private def tensorHomHandler : AppHandler where
  head := tensorHomName
  priority := 170
  run := fun _ rec e args => do
    let ty ← inferType e
    unless (← converterInterfaces? ty).isSome do return none
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    return some (s!"{← rec 60 l} \\parallel {← rec 60 r}", 60)

private def typedConvParallelHandler : AppHandler where
  head := typedConverterParallelName
  priority := 170
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    return some (s!"{← rec 60 l} \\parallel {← rec 60 r}", 60)

private def parallelHandler (head : Name) : AppHandler where
  head := head
  priority := 190
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    return some (s!"{← rec 60 l} \\parallel {← rec 60 r}", 60)

private def interfaceTensorHandler (head : Name) : AppHandler where
  head := head
  priority := 180
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    return some (s!"{← rec 62 l} \\otimes {← rec 62 r}", 62)

private def dummyHandler (head : Name) : AppHandler where
  head := head
  priority := 180
  run := fun _ _ _ _ => return some ("\\mathbf{1}_{\\varnothing}", 90)

private def specMapHandler : AppHandler where
  head := specMapName
  priority := 190
  run := fun _ rec _ args => do
    let some spec := argFromEnd? args 0 | return none
    let some conv := argFromEnd? args 1 | return none
    return some (← renderAttachmentLatex rec conv (unwrapSingletonSpec spec))

private def constructsHandler : AppHandler where
  head := constructsName
  priority := 200
  run := fun tbl rec _ args => do
    let some tgt := argFromEnd? args 0 | return none
    let some src := argFromEnd? args 1 | return none
    let some conv := argFromEnd? args 2 | return none
    let srcTex ← renderSpecLatex tbl rec src
    let convTex ← rec 0 conv
    let tgtTex ← renderSpecLatex tbl rec tgt
    return some (srcTex ++ " \\xrightarrow{" ++ convTex ++ "} " ++ tgtTex, 25)

private def constructsWithinHandler : AppHandler where
  head := constructsWithinName
  priority := 200
  run := fun tbl rec _ args => do
    let some err := argFromEnd? args 0 | return none
    let some tgt := argFromEnd? args 1 | return none
    let some src := argFromEnd? args 2 | return none
    let some conv := argFromEnd? args 3 | return none
    let srcTex ← renderSpecLatex tbl rec src
    let convTex ← rec 0 conv
    let errTex ← rec 0 err
    let tgtTex ← renderSpecLatex tbl rec tgt
    return some (srcTex ++ " \\xrightarrow{" ++ convTex ++ ";\\," ++ errTex ++ "} " ++ tgtTex, 25)

private def substitutesWithinHandler : AppHandler where
  head := substitutesWithinName
  priority := 200
  run := fun _ rec _ args => do
    let some rhs := argFromEnd? args 0 | return none
    let some lhs := argFromEnd? args 1 | return none
    let some err := argFromEnd? args 2 | return none
    let lhsTex ← rec 50 lhs
    let rhsTex ← rec 50 rhs
    let errTex ← rec 0 err
    return some (lhsTex ++ " \\simeq_{" ++ errTex ++ "} " ++ rhsTex, 50)

private def distanceHandler (head : Name) : AppHandler where
  head := head
  priority := 200
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    return some ("\\Delta\\!\\left(" ++ (← rec 0 l) ++ ", " ++ (← rec 0 r) ++ "\\right)", 85)

private def advantageDistanceHandler : AppHandler where
  head := advantageDistanceName
  priority := 190
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    let some cls := argFromEnd? args 2 | return none
    return some ("\\Delta^{" ++ (← rec 0 cls) ++ "}\\!\\left(" ++ (← rec 0 l) ++ ", " ++ (← rec 0 r) ++ "\\right)", 85)

private def distinguisherAdvantageValHandler (head : Name) : AppHandler where
  head := head
  priority := 190
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    let some d := argFromEnd? args 2 | return none
    return some ("\\Delta^{" ++ (← rec 0 d) ++ "}\\!\\left(" ++ (← rec 0 l) ++ ", " ++ (← rec 0 r) ++ "\\right)", 85)

private def distinguisherProbHandler (head : Name) : AppHandler where
  head := head
  priority := 190
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some d := argFromEnd? args 1 | return none
    return some (s!"\\Pr\\!\\left[{← rec 80 d}\\!\\left({← rec 0 r}\\right) = 1\\right]", 85)

private partial def firstTwoExplicitIndices? (ty : Expr) (i : Nat := 0)
    (first? : Option Nat := none) : Option (Nat × Nat) :=
  match ty with
  | .mdata _ b => firstTwoExplicitIndices? b i first?
  | .forallE _ _ b bi =>
      if bi == .default then
        match first? with
        | none => firstTwoExplicitIndices? b (i + 1) (some i)
        | some idx0 => some (idx0, i)
      else
        firstTwoExplicitIndices? b (i + 1) first?
  | _ => none

private def absorbHandler (head : Name) : AppHandler where
  head := head
  priority := 190
  run := fun _ rec _ args => do
    let env ← getEnv
    let some info := env.find? head | return none
    let some (idx0, idx1) := firstTwoExplicitIndices? info.type | return none
    let some dist := args[idx0]? | return none
    let some conv := args[idx1]? | return none
    let baseTex := juxtapose (← rec 80 dist) (← rec 80 conv)
    if let some target := args[idx1 + 1]? then
      return some (s!"{baseTex}({← rec 0 target})", 80)
    return some (baseTex, 80)

private def dfunLikeEpsilonHandler : AppHandler where
  head := ``DFunLike.coe
  priority := 200
  run := fun tbl rec e _ => do
    let env ← getEnv
    if (matchEpsilonRelaxationApp? env e).isSome then
      return some (← renderSpecLatex tbl rec e, 82)
    return none

private def relaxedByHandler : AppHandler where
  head := relaxedByName
  priority := 200
  run := fun tbl rec e _ => do
    let env ← getEnv
    if (matchEpsilonRelaxationApp? env e).isSome then
      return some (← renderSpecLatex tbl rec e, 82)
    return none

private def epsilonRelaxationBareHandler (head : Name) : AppHandler where
  head := head
  priority := 180
  run := fun tbl rec e _ => do
    let env ← getEnv
    if (matchEpsilonRelaxationApp? env e).isSome then
      return some (← renderSpecLatex tbl rec e, 82)
    if let some err := matchEpsilonRelaxationFn? env e then
      return some ("(\\cdot)^{" ++ (← rec 0 err) ++ "}", 82)
    return none

private def simulatorOrStarHandler (head : Name) : AppHandler where
  head := head
  priority := 195
  run := fun tbl rec e _ => do
    return some (← renderSpecLatex tbl rec e, 82)

private def visibleHandler (head : Name) : AppHandler where
  head := head
  priority := 195
  run := fun _ rec _ args => do
    let some g := argFromEnd? args 0 | return none
    return some ((← rec 85 g) ++ "^{-}", 85)

private def condEquivHandler (head : Name) : AppHandler where
  head := head
  priority := 195
  run := fun _ rec _ args => do
    let some t := argFromEnd? args 0 | return none
    let some g := argFromEnd? args 1 | return none
    return some ((← rec 50 g) ++ " \\mathrel{|\\!\\equiv} " ++ (← rec 50 t), 50)

private def gameEquivHandler : AppHandler where
  head := rsGameEquivalentName
  priority := 195
  run := fun _ rec _ args => do
    let some h := argFromEnd? args 0 | return none
    let some g := argFromEnd? args 1 | return none
    return some ((← rec 50 g) ++ " \\equiv_{g} " ++ (← rec 50 h), 50)

private def winProbabilityHandler (head : Name) (gameFromEnd distFromEnd : Nat) : AppHandler where
  head := head
  priority := 190
  run := fun _ rec _ args => do
    let some g := argFromEnd? args gameFromEnd | return none
    let some d := argFromEnd? args distFromEnd | return none
    return some ("\\Gamma^{" ++ (← rec 0 d) ++ "}\\!\\left(" ++ (← rec 0 g) ++ "\\right)", 85)

private def closedUnderLatexHandler : AppHandler where
  head := closedUnderName
  priority := 190
  run := fun _ rec _ args => do
    let some conv := argFromEnd? args 0 | return none
    return some ("\\mathcal{D} \\text{ closed under absorbing } " ++ (← rec 0 conv), 25)

private partial def collectExplicitConstArgs (ty : Expr) (args : Array Expr)
    (i : Nat := 0) (acc : Array Expr := #[]) : Array Expr :=
  if i < args.size then
    match ty with
    | .mdata _ b => collectExplicitConstArgs b args i acc
    | .forallE _ _ b bi =>
        let acc' := if bi == .default then acc.push args[i]! else acc
        collectExplicitConstArgs b args (i + 1) acc'
    | _ =>
        -- Trailing arguments past syntactic telescope
        acc ++ args.extract i args.size
  else acc

private def explicitConstArgs (head : Name) (args : Array Expr) : MetaM (Array Expr) := do
  let some info := (← getEnv).find? head | return args
  return collectExplicitConstArgs info.type args

/-- Unwrap `Interface.inputDomain A` (or `Domain.ofInputs (Interface.domain A) ...`) to `A`. -/
private def unwrapInputDomain? (d : Expr) : MetaM (Option Expr) := do
  let d ← normalizeForPresentation d
  let fn := d.getAppFn.consumeMData
  let args := d.getAppArgs
  if fn.isConstOf ``SystemAlgebra.Interface.inputDomain && args.size == 1 then
    return some args[0]!
  if fn.isConstOf ``SystemAlgebra.Domain.ofInputs && args.size ≥ 3 then
    let domFn := (args[args.size - 3]!).consumeMData
    if domFn.getAppFn.consumeMData.isConstOf ``SystemAlgebra.Interface.domain then
      return domFn.getAppArgs.back?
    if let .proj s 6 ifaceExpr := domFn then
      if s == ``SystemAlgebra.Interface then
        return some ifaceExpr
  return none

private def isProbDistHandler : AppHandler where
  head := ``Probability.Distribution.isProbDist
  priority := 200
  run := fun _ rec _ args => do
    let some mu := argFromEnd? args 0 | return none
    return some ((← rec 80 mu) ++ " \\in \\mathcal{P}", 50)

private def queryBoundedHandler : AppHandler where
  head := ``SystemAlgebra.QueryBounded
  priority := 200
  run := fun _ rec _ args => do
    let some e := argFromEnd? args 0 | return none
    let some n := argFromEnd? args 1 | return none
    return some ("\\mathrm{queries}\\!\\left(" ++ (← rec 0 e) ++ "\\right) \\le " ++ (← rec 0 n), 50)

private def inputDomainHandler : AppHandler where
  head := ``SystemAlgebra.Interface.inputDomain
  priority := 200
  run := fun _ rec _ args => do
    if args.size == 1 then
      return some ("\\mathcal{D}\\!\\left(" ++ (← rec 0 args[0]!) ++ "\\right)", 85)
    if args.size ≥ 3 then
      let iface := args[0]!
      let h := args[args.size - 2]!
      let x := args[args.size - 1]!
      return some ("\\mathrm{adm}_{" ++ (← rec 0 iface) ++ "}\\!\\left(" ++ (← rec 0 h) ++ ", " ++ (← rec 0 x) ++ "\\right)", 85)
    return none

private def domainAdmitsHandler : AppHandler where
  head := ``SystemAlgebra.Domain.admits
  priority := 200
  run := fun _ rec _ args => do
    let some x := argFromEnd? args 0 | return none
    let some h := argFromEnd? args 1 | return none
    let some d := argFromEnd? args 2 | return none
    if let some iface ← unwrapInputDomain? d then
      return some ("\\mathrm{adm}_{" ++ (← rec 0 iface) ++ "}\\!\\left(" ++ (← rec 0 h) ++ ", " ++ (← rec 0 x) ++ "\\right)", 85)
    return some ("\\mathrm{adm}_{" ++ (← rec 0 d) ++ "}\\!\\left(" ++ (← rec 0 h) ++ ", " ++ (← rec 0 x) ++ "\\right)", 85)

private def domainCompatibleHandler : AppHandler where
  head := ``SystemAlgebra.Domain.Compatible
  priority := 200
  run := fun _ rec _ args => do
    let some e := argFromEnd? args 0 | return none
    let some d := argFromEnd? args 1 | return none
    let target ← match ← unwrapInputDomain? d with
      | some iface => rec 0 iface
      | none => rec 0 d
    return some ((← rec 80 e) ++ " \\perp_{\\mathrm{adm}} " ++ target, 50)

private def rsCompatibleHandler : AppHandler where
  head := ``SystemAlgebra.RandomSystem.Compatible
  priority := 200
  run := fun _ rec _ args => do
    let some s := argFromEnd? args 0 | return none
    let some r := argFromEnd? args 1 | return none
    return some ((← rec 80 s) ++ " \\perp_{\\mathrm{adm}} " ++ (← rec 0 r), 50)

private def kernelMassHandler : AppHandler where
  head := ``SystemAlgebra.RandomSystem.kernelMass
  priority := 200
  run := fun _ rec _ args => do
    let exp ← explicitConstArgs ``SystemAlgebra.RandomSystem.kernelMass args
    if exp.size == 2 then
      return some ("\\mu^{\\mathrm{id}}_{" ++ (← rec 0 exp[0]!) ++ ",\\," ++ (← rec 0 exp[1]!) ++ "}", 90)
    if exp.size == 3 then
      return some ("\\mu^{\\mathrm{id}}_{" ++ (← rec 0 exp[0]!) ++ ",\\," ++ (← rec 0 exp[1]!) ++ "}\\!\\left(" ++ (← rec 0 exp[2]!) ++ "\\right)", 85)
    return none

private def revealMassHandler : AppHandler where
  head := ``SystemAlgebra.RandomSystem.revealMass
  priority := 200
  run := fun _ rec _ args => do
    let exp ← explicitConstArgs ``SystemAlgebra.RandomSystem.revealMass args
    if exp.size == 3 then
      return some ("\\mu^{\\mathrm{rev}}_{" ++ (← rec 0 exp[0]!) ++ ",\\," ++ (← rec 0 exp[1]!) ++ "}", 90)
    if exp.size == 4 then
      return some ("\\mu^{\\mathrm{rev}}_{" ++ (← rec 0 exp[0]!) ++ ",\\," ++ (← rec 0 exp[1]!) ++ "}\\!\\left(" ++ (← rec 0 exp[3]!) ++ "\\right)", 85)
    return none

private def kernelLawHandler : AppHandler where
  head := ``SystemAlgebra.RandomSystem.kernelLaw
  priority := 200
  run := fun _ rec _ args => do
    let exp ← explicitConstArgs ``SystemAlgebra.RandomSystem.kernelLaw args
    if exp.size == 4 then
      return some ("\\mathcal{L}^{\\mathrm{id}}_{" ++ (← rec 0 exp[0]!) ++ ",\\," ++ (← rec 0 exp[1]!) ++ "}\\!\\left(" ++ (← rec 0 exp[2]!) ++ ", " ++ (← rec 0 exp[3]!) ++ "\\right)", 85)
    if exp.size == 5 then
      return some ("\\mathcal{L}^{\\mathrm{id}}_{" ++ (← rec 0 exp[0]!) ++ ",\\," ++ (← rec 0 exp[1]!) ++ "}\\!\\left(" ++ (← rec 0 exp[2]!) ++ ", " ++ (← rec 0 exp[3]!) ++ "\\right)\\!\\left(" ++ (← rec 0 exp[4]!) ++ "\\right)", 85)
    return none

private def revealLawHandler : AppHandler where
  head := ``SystemAlgebra.RandomSystem.revealLaw
  priority := 200
  run := fun _ rec _ args => do
    let exp ← explicitConstArgs ``SystemAlgebra.RandomSystem.revealLaw args
    if exp.size == 5 then
      return some ("\\mathcal{L}^{\\mathrm{rev}}_{" ++ (← rec 0 exp[0]!) ++ ",\\," ++ (← rec 0 exp[1]!) ++ "}\\!\\left(" ++ (← rec 0 exp[3]!) ++ ", " ++ (← rec 0 exp[4]!) ++ "\\right)", 85)
    if exp.size == 6 then
      return some ("\\mathcal{L}^{\\mathrm{rev}}_{" ++ (← rec 0 exp[0]!) ++ ",\\," ++ (← rec 0 exp[1]!) ++ "}\\!\\left(" ++ (← rec 0 exp[3]!) ++ ", " ++ (← rec 0 exp[4]!) ++ "\\right)\\!\\left(" ++ (← rec 0 exp[5]!) ++ "\\right)", 85)
    return none

/-! ## 2. Authentic CC Type Handlers (`Ontology.TypeHandler`) -/

private def stripWithPrefix (acc : String) : String :=
  if acc.startsWith "with " then (acc.drop 5).toString else acc

private def isScalarRealCodomain (e : Expr) : Bool :=
  let c := e.consumeMData
  c == mkConst `Real || c == mkConst `NNReal || c == mkConst `ENNReal

private def isPortDomain? (dom : Expr) : Bool :=
  let d := dom.consumeMData
  if d.getAppFn.consumeMData.isConstOf ``SystemAlgebra.Interface.I then true
  else if let .proj s 0 _ := d then s == ``SystemAlgebra.Interface
  else if let .const c _ := d.getAppFn.consumeMData then
    (match c with | .str _ "Port" => true | _ => false) || c == `Port
  else false

private def extractTranscriptIface? (sig : Expr) (projIdx : Nat) (fnName : Name) : Option Expr :=
  match sig.getAppArgs.back?.map Expr.consumeMData with
  | none => none
  | some last =>
      let b := match last with
        | .lam _ _ fam _ => fam.consumeMData
        | other => other
      let f := b.getAppFn.consumeMData
      if f.isConstOf fnName then b.getAppArgs[0]?
      else match f with
        | .proj ``SystemAlgebra.Interface idx iface =>
            if idx == projIdx then some iface else none
        | _ => none

private def isTranscriptList? (ty : Expr) : Option (Option Expr) :=
  let t := ty.consumeMData
  if !t.getAppFn.consumeMData.isConstOf ``List then none
  else match t.getAppArgs.back? with
    | none => none
    | some elemTy =>
        let elemClean := elemTy.consumeMData
        if !elemClean.getAppFn.consumeMData.isConstOf ``Prod || elemClean.getAppArgs.size != 2 then none
        else
          let lhs := elemClean.getAppArgs[0]!.consumeMData
          let rhs := elemClean.getAppArgs[1]!.consumeMData
          if !lhs.getAppFn.consumeMData.isConstOf ``Sigma || !rhs.getAppFn.consumeMData.isConstOf ``Sigma then none
          else
            match extractTranscriptIface? lhs 1 ``SystemAlgebra.Interface.X,
                  extractTranscriptIface? rhs 2 ``SystemAlgebra.Interface.Y with
            | some il, some ir => if il == ir then some (some il) else some none
            | _, _ => some none

private def ccTypeHandler : TypeHandler where
  priority := 200
  matchType := fun tbl ty => do
    let ty ← normalizeForPresentation ty
    -- 1. Suppress ambient CC category/family universe parameters from repeated lemma headers
    let fam ← collectAmbientFamilies
    if ty.isSort then
      -- Only mark as ambient if a local variable of this type is a CC category; handled below
      pure ()
    if let .forallE _ dom body _ := ty then
      if !body.hasLooseBVar 0 && body.isSort then
        if fam.categories.any (fun c => c == dom.consumeMData) ||
           dom.consumeMData == mkConst interfaceName then
          return some { noun := ⟨"resource family", "resource families"⟩, isAmbient := true }
    -- 2. Interface carrier (`A : Interface` or `A : C`)
    if ← isInterfaceType ty then
      return some { noun := nounInterface }
    -- 3. Resource (`Phi A` or `TypedSystem A`): arity-driven "with interface A" / "with interfaces H and P"
    -- Respect `@[interface_resource_noun]` / `informal_noun` on any interface constant first.
    if let some iface ← resourceInterface? ty then
      let acc ← interfaceAccessory tbl iface
      if let .const ifaceHead _ := iface.getAppFn.consumeMData then
        let env ← getEnv
        if let some (sg, pl) := (Core.Overlay.getOverlay env ifaceHead).noun? <|>
            (Core.Presentation.getMathPresentation env ifaceHead).interfaceResourceNoun? then
          return some { noun := ⟨sg, pl⟩, accessories := [acc] }
      return some { noun := nounResource, accessories := [acc] }
    -- 4. Converter (`A ⟶ B`, `Converter C A B`, or `TypedConverter A B`)
    if let some (outIface, inIface) ← converterInterfaces? ty then
      let inTex ← exprToLatex inIface tbl
      let outTex ← exprToLatex outIface tbl
      return some {
        noun := nounConverter
        accessories := [s!"with inside interface \\({inTex}\\) and outside interface \\({outTex}\\)"]
      }
    -- 5. Specification (`Specification (Phi A)` or `Set (Phi A)`)
    if let some iface ← specificationInterface? ty then
      let acc ← interfaceAccessory tbl iface
      return some { noun := nounSpecification, accessories := [s!"of resources {acc}"] }
    -- 6. Class of simulators / converters (`Set (P ⟶ Q)` or `EndoFamily A`)
    let fn := ty.getAppFn.consumeMData
    let args := ty.getAppArgs
    if fn.isConstOf endoFamilyName && args.size ≥ 1 then
      let acc ← interfaceAccessory tbl args.back!
      return some {
        noun := ⟨"class of converters", "classes of converters"⟩
        accessories := [acc]
      }
    if (fn.isConstOf ``Set || fn.isConstOf specificationName) && args.size ≥ 1 then
      if let some (outIface, inIface) ← converterInterfaces? args.back! then
        let inTex ← exprToLatex inIface tbl
        let outTex ← exprToLatex outIface tbl
        return some {
          noun := ⟨"class of converters", "classes of converters"⟩
          accessories := [s!"with inside interface \\({inTex}\\) and outside interface \\({outTex}\\)"]
        }
    -- 7. Game (`Game A` or `TypedGame A`)
    if let some iface ← gameInterface? ty then
      let acc ← interfaceAccessory tbl iface
      return some { noun := nounGame, accessories := [acc] }
    -- 7b. Solver (`TypedSolver A` or `Domain.SolverBehavior ...`)
    if fn.isConstOf typedSolverName && args.size ≥ 1 then
      let acc ← interfaceAccessory tbl args.back!
      return some { noun := ⟨"solver", "solvers"⟩, accessories := [acc] }
    if fn.isConstOf `SystemAlgebra.Domain.SolverBehavior then
      return some { noun := ⟨"solver", "solvers"⟩ }
    -- 8. Distinguisher (`D A`, `TypedDistinguisher A`)
    if let some iface ← distinguisherInterface? ty then
      let acc ← interfaceAccessory tbl iface
      return some { noun := nounDistinguisher, accessories := [acc] }
    -- 8b. Game/distinguisher solver pair `(Phi A → ℝ) × (Game A → ℝ)`
    if fn.isConstOf ``Prod && args.size == 2 then
      if let (.forallE _ rTy rOut _, .forallE _ gTy gOut _) := (args[0]!, args[1]!) then
        if rOut.consumeMData == mkConst `Real && gOut.consumeMData == mkConst `Real then
          if let (some rIface, some gIface) := (← resourceInterface? rTy, ← gameInterface? gTy) then
            if rIface == gIface then
              let acc ← interfaceAccessory tbl rIface
              return some { noun := ⟨"solver", "solvers"⟩, accessories := [acc] }
    -- 9. H-coefficient witness (`HCoefficient R S error`)
    if isHCoefficientType ty then
      let hArgs := ty.getAppArgs
      if hArgs.size ≥ 3 then
        let rTex ← exprToLatex hArgs[hArgs.size - 3]! tbl
        let sTex ← exprToLatex hArgs[hArgs.size - 2]! tbl
        let errTex ← exprToLatex hArgs[hArgs.size - 1]! tbl
        return some {
          noun := ⟨"H-coefficient witness", "H-coefficient witnesses"⟩
          accessories := [s!"for \\({rTex}\\) and \\({sTex}\\) with error bound \\({errTex}\\)"]
          isWitness := true
        }
      return some { noun := ⟨"H-coefficient witness", "H-coefficient witnesses"⟩, isWitness := true }
    -- 10. Substitution implication witness
    if isImplicationType ty then
      return some { noun := ⟨"substitution chain", "substitution chains"⟩, isWitness := true }
    -- 10b. Context-aware CC functional/arrow types (per-port budgets, advantage bounds, games, families)
    if let .forallE _ dom body _ := ty then
      if !body.hasLooseBVar 0 then
        -- a) Per-port query budget `Port → ℕ` / `A.I → ℕ`
        if body.consumeMData.isConstOf ``Nat && isPortDomain? dom then
          let domTex ← exprToLatex dom tbl
          return some {
            noun := ⟨"per-port query budget", "per-port query budgets"⟩
            accessories := [s!"on \\({domTex}\\)"]
          }
        -- b) Distinguisher advantage bound `Distinguisher(I) → ℝ / ℝ≥0 / ℝ≥0∞`
        if isScalarRealCodomain body then
          if let some iface ← distinguisherInterface? dom then
            let ifacePhrase := stripWithPrefix (← interfaceAccessory tbl iface)
            return some {
              noun := ⟨"distinguisher advantage bound", "distinguisher advantage bounds"⟩
              accessories := [s!"for {ifacePhrase}"]
            }
          let dFn := dom.getAppFn.consumeMData
          if (dFn.isConstOf ``SystemAlgebra.Domain.Distinguisher ||
              dFn.isConstOf ``SystemAlgebra.Domain.DistinguisherBehavior) &&
             dom.getAppArgs.size ≥ 1 then
            let domArg := dom.getAppArgs.back!
            if let some iface ← unwrapInputDomain? domArg then
              let ifacePhrase := stripWithPrefix (← interfaceAccessory tbl iface)
              return some {
                noun := ⟨"distinguisher advantage bound", "distinguisher advantage bounds"⟩
                accessories := [s!"for {ifacePhrase}"]
              }
            let domTex ← exprToLatex domArg tbl
            return some {
              noun := ⟨"distinguisher advantage bound", "distinguisher advantage bounds"⟩
              accessories := [s!"on \\({domTex}\\)"]
            }
          -- c) Game winning-probability functional `Game(A) → ℝ / ℝ≥0 / ℝ≥0∞`
          if let some iface ← gameInterface? dom then
            let aTex ← exprToLatex iface tbl
            return some {
              noun := ⟨"winning-probability function", "winning-probability functions"⟩
              accessories := [s!"on games over \\({aTex}\\)"]
            }
        -- d) Indexed family of converters `K → (H' ⟶ H)`
        if !dom.consumeMData.isForall then
          if let some (outIface, inIface) ← converterInterfaces? body then
            let kTex ← exprToLatex dom tbl
            let inTex ← exprToLatex inIface tbl
            let outTex ← exprToLatex outIface tbl
            return some {
              noun := ⟨"indexed family of converters", "indexed families of converters"⟩
              accessories := [s!"indexed by \\({kTex}\\) from \\({inTex}\\) to \\({outTex}\\)"]
            }
    -- 10c. Deterministic environment `SystemAlgebra.DDE`
    if fn.isConstOf ``SystemAlgebra.DDE then
      return some { noun := ⟨"deterministic environment", "deterministic environments"⟩ }
    -- 10d. Query/reply transcript `List ((Σ i, X i) × (Σ i, Y i))` and extended transcript `(h, z)`
    if let some iface? := isTranscriptList? ty then
      let accessories ← match iface? with
        | some iface => do
            let ifaceTex ← exprToLatex iface tbl
            pure [s!"over \\({ifaceTex}\\)"]
        | none => pure []
      return some { noun := ⟨"transcript", "transcripts"⟩, accessories }
    if fn.isConstOf ``Prod && args.size == 2 then
      if (isTranscriptList? args[0]!).isSome then
        return some { noun := ⟨"extended transcript", "extended transcripts"⟩ }
    -- 11. Query history predicate on `List (Sigma (fun i => Interface.X A i))`
    if let .forallE _ dom body _ := ty then
      if !body.hasLooseBVar 0 && body == .sort .zero then
        if dom.getAppFn.consumeMData.isConstOf ``List then
          if let some elemTy := dom.getAppArgs.back? then
            if elemTy.getAppFn.consumeMData.isConstOf ``Sigma then
              if let some (.lam _ _ fam _) := elemTy.getAppArgs.back? then
                if fam.getAppFn.consumeMData.isConstOf `SystemAlgebra.Interface.X then
                  if let some ifaceExpr := fam.getAppArgs[0]? then
                    let ifaceTex ← exprToLatex ifaceExpr tbl
                    return some {
                      noun := ⟨"predicate", "predicates"⟩
                      accessories := [s!"on query histories over \\({ifaceTex}\\)"]
                    }
    return none

/-! ## 3. Maurer-Voice CC Proposition Handlers (`Ontology.PropHandler`) -/

/-- Describe a converter application in authentic CC prose, distinguishing left/honest and
right/adversarial interface attachment cleanly. -/
def describeConverterRole (tbl : SymbolTable) (conv : Expr) : MetaM String := do
  if let some (h, sigma) := matchWhiskerLeft? conv then
    let hTex ← exprToLatex h tbl
    let sTex ← exprToLatex sigma tbl
    return s!"attaching \\({sTex}\\) at the right interface (leaving \\({hTex}\\) untouched)"
  if let some (kappa, p) := matchWhiskerRight? conv then
    let kTex ← exprToLatex kappa tbl
    let pTex ← exprToLatex p tbl
    return s!"applying \\({kTex}\\) at the left interface (leaving \\({pTex}\\) untouched)"
  let cTex ← exprToLatex conv tbl
  return s!"protocol \\({cTex}\\)"

/-- Describe a game's underlying system obtained by ignoring the MBO (`G⁻`). -/
def describeUnderlyingGameSystem (tbl : SymbolTable) (game : Expr) : MetaM String := do
  let gTex ← exprToLatex game tbl
  return "the underlying system \\(" ++ gTex ++ "^{-}\\)" ++ " obtained by ignoring the MBO"

private def ccPropHandler : PropHandler where
  priority := 200
  renderProp := fun tbl prop => do
    let prop ← normalizeForPresentation prop
    -- 0. Prefix-closed predicate quantifier: `∀ s t, s <+: t → P t → P s`
    if let .forallE _ _ (.forallE _ _ body _) _ := prop then
      if let .forallE _ prefDom (.forallE _ ptDom psDom _) _ := body then
        if prefDom.getAppFn.consumeMData.isConstOf `List.IsPrefix then
          let predFn := psDom.getAppFn.consumeMData
          if predFn == ptDom.getAppFn.consumeMData && !predFn.hasLooseBVars then
            let predTex ← exprToLatex predFn tbl
            return some #[.text "the predicate ", .inlineMath predTex, .text " is prefix-closed"]
    let fn := prop.getAppFn.consumeMData
    let args := prop.getAppArgs
    -- 0b. Admissibility via Domain.admits projection `(A.inputDomain).admits h x` or over-applied `inputDomain A h x`
    let renderAdmitsProp (domExpr hExpr xExpr : Expr) : MetaM (Option (Array Inline)) := do
      let xTex ← exprToLatex xExpr tbl
      let hTex ← exprToLatex hExpr tbl
      if let some iface ← unwrapInputDomain? domExpr then
        let iTex ← exprToLatex iface tbl
        return some #[
          .text "the query ", .inlineMath xTex,
          .text " is admissible after transcript ", .inlineMath hTex,
          .text " on ", .inlineMath iTex
        ]
      let dTex ← exprToLatex domExpr tbl
      return some #[
        .text "the query ", .inlineMath xTex,
        .text " is admissible after transcript ", .inlineMath hTex,
        .text " in ", .inlineMath dTex
      ]
    if let .proj ``SystemAlgebra.Domain 0 domExpr := fn then
      if let (some hExpr, some xExpr) := (argFromEnd? args 1, argFromEnd? args 0) then
        if let some out ← renderAdmitsProp domExpr hExpr xExpr then
          return some out
    let some head := fn.constName? | return none
    if head == ``SystemAlgebra.Domain.admits then
      if let (some dExpr, some hExpr, some xExpr) := (argFromEnd? args 2, argFromEnd? args 1, argFromEnd? args 0) then
        return ← renderAdmitsProp dExpr hExpr xExpr
    if head == ``SystemAlgebra.Interface.inputDomain && args.size ≥ 3 then
      return ← renderAdmitsProp (mkApp (.const ``SystemAlgebra.Interface.inputDomain []) args[0]!) args[args.size - 2]! args[args.size - 1]!
    -- 0c. Normalized probability distribution predicate `isProbDist μ`
    if head == ``Probability.Distribution.isProbDist then
      if let some muExpr := argFromEnd? args 0 then
        let muTex ← exprToLatex muExpr tbl
        return some #[.inlineMath muTex, .text " is a valid probability distribution"]
    -- 0d. Query-bounded environment `QueryBounded n E`
    if head == ``SystemAlgebra.QueryBounded then
      if let (some nExpr, some eExpr) := (argFromEnd? args 1, argFromEnd? args 0) then
        let eTex ← exprToLatex eExpr tbl
        let nTex ← exprToLatex nExpr tbl
        let qWord := if nTex == "1" then " query" else " queries"
        return some #[
          .text "the environment ", .inlineMath eTex,
          .text " respects the query budget of ", .inlineMath nTex, .text qWord
        ]
    -- 0e. Compatible environment / strategy predicates
    if head == ``SystemAlgebra.Domain.Compatible then
      if let (some dExpr, some eExpr) := (argFromEnd? args 1, argFromEnd? args 0) then
        let eTex ← exprToLatex eExpr tbl
        let targetTex ← match ← unwrapInputDomain? dExpr with
          | some iface => exprToLatex iface tbl
          | none => exprToLatex dExpr tbl
        return some #[
          .text "the environment ", .inlineMath eTex,
          .text " is compatible with ", .inlineMath targetTex
        ]
    if head == ``SystemAlgebra.RandomSystem.Compatible then
      if let (some rExpr, some sExpr) := (argFromEnd? args 1, argFromEnd? args 0) then
        let sTex ← exprToLatex sExpr tbl
        let rTex ← exprToLatex rExpr tbl
        return some #[
          .text "the strategy ", .inlineMath sTex,
          .text " is compatible with ", .inlineMath rTex
        ]
    let protocolLead (convTex : String) : Array Inline :=
      if convTex == "\\mathrm{protocol}" || convTex == "protocol" then #[.text "the protocol"]
      else #[.text "protocol ", .inlineMath convTex]
    -- 1. Exact construction: `Constructs π ℛ 𝒮`
    if head == constructsName && args.size ≥ 3 then
      let some tgt := argFromEnd? args 0 | return none
      let some src := argFromEnd? args 1 | return none
      let some conv := argFromEnd? args 2 | return none
      let srcTex ← exprToLatex (unwrapSingletonSpec src) tbl
      let convTex ← exprToLatex conv tbl
      let tgtTex ← exprToLatex (unwrapSingletonSpec tgt) tbl
      let verb := verbConstruct.conjugate .singular
      if let some (eps, inner) := matchEpsilonRelaxationApp? (← getEnv) tgt then
        let epsTex ← exprToLatex eps tbl
        if let some (_, base) := matchSimulatorOrStar? inner then
          let baseTex ← exprToLatex (unwrapSingletonSpec base) tbl
          return some (protocolLead convTex ++ #[
            .text s!" {verb} the ", .inlineMath epsTex,
            .text "-relaxed simulator specification ",
            .inlineMath ("\\left(" ++ baseTex ++ "^{*}\\right)^{" ++ epsTex ++ "}"),
            .text " from ", .inlineMath srcTex
          ])
        return some (protocolLead convTex ++ #[
          .text s!" {verb} ", .inlineMath tgtTex,
          .text " from ", .inlineMath srcTex,
          .text " within error ", .inlineMath epsTex
        ])
      return some (protocolLead convTex ++ #[
        .text s!" {verb} ", .inlineMath tgtTex,
        .text " from ", .inlineMath srcTex
      ])
    -- 2. Approximate construction: `ConstructsWithin π ℛ 𝒮 ε`
    if head == constructsWithinName && args.size ≥ 4 then
      let some err := argFromEnd? args 0 | return none
      let some tgt := argFromEnd? args 1 | return none
      let some src := argFromEnd? args 2 | return none
      let some conv := argFromEnd? args 3 | return none
      let srcTex ← exprToLatex (unwrapSingletonSpec src) tbl
      let convTex ← exprToLatex conv tbl
      let tgtTex ← exprToLatex (unwrapSingletonSpec tgt) tbl
      let errTex ← exprToLatex err tbl
      let verb := verbConstruct.conjugate .singular
      return some (protocolLead convTex ++ #[
        .text s!" {verb} ", .inlineMath tgtTex,
        .text " from ", .inlineMath srcTex,
        .text " within error ", .inlineMath errTex
      ])
    -- 3. Concrete substitution: `R ≃[ε] S`
    if head == substitutesWithinName && args.size ≥ 3 then
      let some rhs := argFromEnd? args 0 | return none
      let some lhs := argFromEnd? args 1 | return none
      let some err := argFromEnd? args 2 | return none
      let lhsTex ← exprToLatex lhs tbl
      let rhsTex ← exprToLatex rhs tbl
      let errTex ← exprToLatex err tbl
      return some #[
        .text "the resource ", .inlineMath lhsTex,
        .text " can be substituted by ", .inlineMath rhsTex,
        .text " within error ", .inlineMath errTex
      ]
    -- 4. Distinguisher class closure under absorbing a converter: `ClosedUnder α`
    if head == closedUnderName && args.size ≥ 1 then
      let some conv := argFromEnd? args 0 | return none
      let convTex ← exprToLatex conv tbl
      return some #[
        .text "the distinguisher class ", .inlineMath "\\mathcal{D}",
        .text " is closed under absorbing ", .inlineMath convTex
      ]
    -- 5. Conditional equivalence of a game and a resource: `G |≡ T`
    if (head == conditionallyEquivalentName || head == rsConditionallyEquivalentName) && args.size ≥ 2 then
      let some tgt := argFromEnd? args 0 | return none
      let some game := argFromEnd? args 1 | return none
      let gameTex ← exprToLatex game tbl
      let tgtTex ← exprToLatex tgt tbl
      return some #[
        .text "the game ", .inlineMath gameTex,
        .text " is conditionally equivalent to ", .inlineMath tgtTex
      ]
    -- 6. Equivalence as games: `G ≡_g H`
    if head == rsGameEquivalentName && args.size ≥ 2 then
      let some h := argFromEnd? args 0 | return none
      let some g := argFromEnd? args 1 | return none
      let gTex ← exprToLatex g tbl
      let hTex ← exprToLatex h tbl
      return some #[
        .text "the games ", .inlineMath gTex, .text " and ", .inlineMath hTex,
        .text " are equivalent as games"
      ]
    -- 7. Monotone binary output predicate
    if head == monotoneMBOName && args.size ≥ 1 then
      let some g := argFromEnd? args 0 | return none
      let gTex ← exprToLatex g tbl
      return some #[
        .text "the system ", .inlineMath gTex,
        .text " carries a monotone binary output (MBO)"
      ]
    -- 8. Distance upper bound: `Δ R S ≤ ε`
    if head == ``LE.le && args.size ≥ 2 then
      let some rhs := argFromEnd? args 0 | return none
      let some lhs := argFromEnd? args 1 | return none
      let lhsHead := lhs.getAppFn.consumeMData
      if lhsHead.isConstOf distanceName || lhsHead.isConstOf transcriptDistanceName then
        let lhsArgs := lhs.getAppArgs
        if let (some r1, some r2) := (argFromEnd? lhsArgs 1, argFromEnd? lhsArgs 0) then
          let r1Tex ← exprToLatex r1 tbl
          let r2Tex ← exprToLatex r2 tbl
          let epsTex ← exprToLatex rhs tbl
          return some #[
            .text "the distinguishing advantage between ", .inlineMath r1Tex,
            .text " and ", .inlineMath r2Tex,
            .text " is at most ", .inlineMath epsTex
          ]
    -- 9. Membership in an ε-relaxation: `R ∈ (S^*)^ε` or `R ∈ S^ε`
    if head == ``Membership.mem && args.size ≥ 2 then
      let some setExpr := argFromEnd? args 0 | return none
      let some elemExpr := argFromEnd? args 1 | return none
      if let some (eps, inner) := matchEpsilonRelaxationApp? (← getEnv) setExpr then
        let elemTex ← exprToLatex elemExpr tbl
        let epsTex ← exprToLatex eps tbl
        let fullTex ← exprToLatex prop tbl
        if let some (_, base) := matchSimulatorOrStar? inner then
          let baseTex ← exprToLatex (unwrapSingletonSpec base) tbl
          return some #[
            .text "the resource ", .inlineMath elemTex,
            .text " lies within error ", .inlineMath epsTex,
            .text " of the simulator-relaxed specification ", .inlineMath (baseTex ++ "^{*}"),
            .text " (", .inlineMath fullTex, .text ")"
          ]
        let innerTex ← exprToLatex (unwrapSingletonSpec inner) tbl
        return some #[
          .text "the resource ", .inlineMath elemTex,
          .text " lies within error ", .inlineMath epsTex,
          .text " of ", .inlineMath innerTex,
          .text " (", .inlineMath fullTex, .text ")"
        ]
    return none

/-- Low-priority fallback handler for generic `Prod` (`ordered pair`) and `Set` (`subset of X`)
after CC-specific patterns (`Set (P ⟶ Q)`, `Set (Phi A)`, solver `Prod`) have had first claim. -/
private def ccGenericContainerTypeHandler : TypeHandler where
  priority := 50
  matchType := fun tbl ty => do
    let ty ← instantiateMVars ty
    let fn := ty.getAppFn.consumeMData
    let args := ty.getAppArgs
    if fn.isConstOf ``Prod && args.size == 2 then
      return some { noun := ⟨"ordered pair", "ordered pairs"⟩ }
    if fn.isConstOf ``Set && args.size ≥ 1 then
      let elemTex ← exprToLatex args.back! tbl
      return some {
        noun := ⟨"subset", "subsets"⟩
        accessories := [s!"of \\({elemTex}\\)"]
      }
    return none

/-! ## 4. Module Initialization (Auto-Registration) -/

/-- Register all CC 2D LaTeX, type ontology, and Maurer-voice proposition handlers. -/
def registerAll : IO Unit := do
  -- 2D LaTeX application handlers
  registerAppHandler attachHandler
  registerAppHandler typedAttachHandler
  registerAppHandler attachGameHandler
  registerAppHandler typedAttachGameHandler
  registerAppHandler hSMulAttachHandler
  registerAppHandler whiskerLeftHandler
  registerAppHandler whiskerRightHandler
  registerAppHandler compHandler
  registerAppHandler typedCompHandler
  registerAppHandler idHandler
  registerAppHandler typedIdHandler
  registerAppHandler tensorHomHandler
  registerAppHandler typedConvParallelHandler
  registerAppHandler (parallelHandler parallelName)
  registerAppHandler (parallelHandler specParallelName)
  registerAppHandler (parallelHandler typedSystemParallelName)
  registerAppHandler (interfaceTensorHandler tensorObjName)
  registerAppHandler (interfaceTensorHandler interfaceTensorName)
  registerAppHandler (dummyHandler dummyName)
  registerAppHandler (dummyHandler specDummyName)
  registerAppHandler (dummyHandler typedSystemDummyName)
  registerAppHandler specMapHandler
  registerAppHandler constructsHandler
  registerAppHandler constructsWithinHandler
  registerAppHandler substitutesWithinHandler
  registerAppHandler (distanceHandler distanceName)
  registerAppHandler (distanceHandler transcriptDistanceName)
  registerAppHandler advantageDistanceHandler
  registerAppHandler (distinguisherAdvantageValHandler distinguisherAdvantageValName)
  registerAppHandler (distinguisherAdvantageValHandler `ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.advantage)
  registerAppHandler (distinguisherAdvantageValHandler `SystemAlgebra.Domain.Distinguisher.advantage)
  registerAppHandler (distinguisherAdvantageValHandler `SystemAlgebra.Domain.DistinguisherBehavior.advantage)
  registerAppHandler (distinguisherProbHandler distinguisherProbabilityName)
  registerAppHandler (distinguisherProbHandler `SystemAlgebra.Domain.Distinguisher.probability)
  registerAppHandler (distinguisherProbHandler `SystemAlgebra.TypedDistinguisher.probability)
  registerAppHandler (distinguisherProbHandler `SystemAlgebra.RandomSystem.decisionProbability)
  registerAppHandler (absorbHandler absorbName)
  registerAppHandler (absorbHandler typedDistinguisherAbsorbName)
  registerAppHandler (absorbHandler gamesAbsorbName)
  registerAppHandler dfunLikeEpsilonHandler
  registerAppHandler relaxedByHandler
  registerAppHandler (epsilonRelaxationBareHandler epsilonRelaxationName)
  registerAppHandler (epsilonRelaxationBareHandler specEpsilonRelaxationName)
  registerAppHandler (simulatorOrStarHandler simulatorImageName)
  registerAppHandler (simulatorOrStarHandler starName)
  registerAppHandler (simulatorOrStarHandler `Commons.Indifferentiability.specification)
  registerAppHandler (visibleHandler visibleName)
  registerAppHandler (visibleHandler rsVisibleName)
  registerAppHandler (visibleHandler typedGameVisibleName)
  registerAppHandler (condEquivHandler conditionallyEquivalentName)
  registerAppHandler (condEquivHandler rsConditionallyEquivalentName)
  registerAppHandler gameEquivHandler
  registerAppHandler (winProbabilityHandler rsWinProbabilityName 2 1)
  registerAppHandler (winProbabilityHandler typedSolverWinProbabilityName 0 1)
  registerAppHandler closedUnderLatexHandler
  registerAppHandler isProbDistHandler
  registerAppHandler queryBoundedHandler
  registerAppHandler inputDomainHandler
  registerAppHandler domainAdmitsHandler
  registerAppHandler domainCompatibleHandler
  registerAppHandler rsCompatibleHandler
  registerAppHandler kernelMassHandler
  registerAppHandler revealMassHandler
  registerAppHandler kernelLawHandler
  registerAppHandler revealLawHandler
  -- Type & proposition ontology handlers
  registerTypeHandler ccTypeHandler
  registerTypeHandler ccGenericContainerTypeHandler
  registerPropHandler ccPropHandler
  Core.Presentation.registerCCKnownCarrierHook fun ty => do
    let t := ty.consumeMData
    let fn := t.getAppFn.consumeMData
    let args := t.getAppArgs
    let isIface ← isInterfaceType t
    let isRes := (← resourceInterface? t).isSome
    let isConv := (← converterInterfaces? t).isSome
    let isSpec := (← specificationInterface? t).isSome
    let isConvClass ←
      if (fn.isConstOf ``Set || fn.isConstOf specificationName) && args.size ≥ 1 then
        pure (← converterInterfaces? args.back!).isSome
      else pure false
    let isSolver := fn.isConstOf `SystemAlgebra.Domain.SolverBehavior
    let isGame := (← gameInterface? t).isSome
    let isDist := (← distinguisherInterface? t).isSome
    return isIface || isRes || isConv || isSpec || isConvClass || isSolver || isGame || isDist

initialize registerAll

end Informalization.CC.Ontology
