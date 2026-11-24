/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Ontology
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

/-- Recognize an `epsilonRelaxation ε` expression, returning `ε`. -/
private def matchEpsilonRelaxationFn? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  if fn.isConstOf epsilonRelaxationName || fn.isConstOf specEpsilonRelaxationName then
    e.getAppArgs.back?
  else none

/-- Recognize `epsilonRelaxation ε S` (either via `DFunLike.coe` or `Relaxation.relaxedBy`),
returning `(ε, S)`. -/
private def matchEpsilonRelaxationApp? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf ``DFunLike.coe && args.size ≥ 6 then
    let relaxFn := args[args.size - 2]!
    let specArg := args[args.size - 1]!
    match matchEpsilonRelaxationFn? relaxFn with
    | some eps => some (eps, specArg)
    | none => none
  else if fn.isConstOf relaxedByName && args.size ≥ 2 then
    let specArg := args[args.size - 2]!
    let relaxFn := args[args.size - 1]!
    match matchEpsilonRelaxationFn? relaxFn with
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
  if let some (eps, inner) := matchEpsilonRelaxationApp? spec then
    let epsTex ← rec 0 eps
    if let some (_, base) := matchSimulatorOrStar? inner then
      let baseTex ← rec 82 (unwrapSingletonSpec base)
      return "\\left(" ++ baseTex ++ "^{*}\\!\\right)^{" ++ epsTex ++ "}"
    else
      let innerTex ← rec 82 (unwrapSingletonSpec inner)
      return innerTex ++ "^{" ++ epsTex ++ "}"
  if let some (_, base) := matchSimulatorOrStar? spec then
    let baseTex ← rec 82 (unwrapSingletonSpec base)
    return baseTex ++ "^{*}"
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

private def distinguisherAdvantageValHandler : AppHandler where
  head := distinguisherAdvantageValName
  priority := 190
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some l := argFromEnd? args 1 | return none
    let some d := argFromEnd? args 2 | return none
    return some ("\\Delta^{" ++ (← rec 0 d) ++ "}\\!\\left(" ++ (← rec 0 l) ++ ", " ++ (← rec 0 r) ++ "\\right)", 85)

private def distinguisherProbHandler : AppHandler where
  head := distinguisherProbabilityName
  priority := 190
  run := fun _ rec _ args => do
    let some r := argFromEnd? args 0 | return none
    let some d := argFromEnd? args 1 | return none
    return some (s!"\\Pr\\!\\left[{← rec 80 d}\\!\\left({← rec 0 r}\\right) = 1\\right]", 85)

private def absorbHandler (head : Name) : AppHandler where
  head := head
  priority := 190
  run := fun _ rec _ args => do
    let some conv := argFromEnd? args 0 | return none
    let some dist := argFromEnd? args 1 | return none
    return some (s!"{← rec 80 dist}{← rec 80 conv}", 80)

private def dfunLikeEpsilonHandler : AppHandler where
  head := ``DFunLike.coe
  priority := 200
  run := fun tbl rec e _ => do
    if (matchEpsilonRelaxationApp? e).isSome then
      return some (← renderSpecLatex tbl rec e, 82)
    return none

private def relaxedByHandler : AppHandler where
  head := relaxedByName
  priority := 200
  run := fun tbl rec e _ => do
    if (matchEpsilonRelaxationApp? e).isSome then
      return some (← renderSpecLatex tbl rec e, 82)
    return none

private def epsilonRelaxationBareHandler (head : Name) : AppHandler where
  head := head
  priority := 180
  run := fun _ rec _ args => do
    let some err := argFromEnd? args 0 | return none
    return some ("(\\cdot)^{" ++ (← rec 0 err) ++ "}", 82)

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

/-! ## 2. Authentic CC Type Handlers (`Ontology.TypeHandler`) -/

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
    if let some iface ← resourceInterface? ty then
      let acc ← interfaceAccessory tbl iface
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
    -- 8. Distinguisher or solver (`D A`, `TypedDistinguisher A`, `TypedSolver A`)
    if let some iface ← distinguisherInterface? ty then
      let acc ← interfaceAccessory tbl iface
      return some { noun := nounDistinguisher, accessories := [acc] }
    -- 9. H-coefficient witness
    if isHCoefficientType ty then
      return some { noun := ⟨"H-coefficient witness", "H-coefficient witnesses"⟩ }
    -- 10. Substitution implication witness
    if isImplicationType ty then
      return some { noun := ⟨"substitution chain", "substitution chains"⟩ }
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
    let fn := prop.getAppFn.consumeMData
    let args := prop.getAppArgs
    let some head := fn.constName? | return none
    -- 1. Exact construction: `Constructs π ℛ 𝒮`
    if head == constructsName && args.size ≥ 3 then
      let some tgt := argFromEnd? args 0 | return none
      let some src := argFromEnd? args 1 | return none
      let some conv := argFromEnd? args 2 | return none
      let srcTex ← exprToLatex (unwrapSingletonSpec src) tbl
      let convTex ← exprToLatex conv tbl
      let tgtTex ← exprToLatex (unwrapSingletonSpec tgt) tbl
      let verb := verbConstruct.conjugate .singular
      if let some (eps, inner) := matchEpsilonRelaxationApp? tgt then
        let epsTex ← exprToLatex eps tbl
        if let some (_, base) := matchSimulatorOrStar? inner then
          let baseTex ← exprToLatex (unwrapSingletonSpec base) tbl
          return some #[
            .text "protocol ", .inlineMath convTex,
            .text s!" {verb} the ", .inlineMath epsTex,
            .text "-relaxed simulator specification ",
            .inlineMath ("\\left(" ++ baseTex ++ "^{*}\\right)^{" ++ epsTex ++ "}"),
            .text " from ", .inlineMath srcTex
          ]
        return some #[
          .text "protocol ", .inlineMath convTex,
          .text s!" {verb} ", .inlineMath tgtTex,
          .text " from ", .inlineMath srcTex,
          .text " within error ", .inlineMath epsTex
        ]
      return some #[
        .text "protocol ", .inlineMath convTex,
        .text s!" {verb} ", .inlineMath tgtTex,
        .text " from ", .inlineMath srcTex
      ]
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
      return some #[
        .text "protocol ", .inlineMath convTex,
        .text s!" {verb} ", .inlineMath tgtTex,
        .text " from ", .inlineMath srcTex,
        .text " within error ", .inlineMath errTex
      ]
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
            .text "the distinguishing distance between ", .inlineMath r1Tex,
            .text " and ", .inlineMath r2Tex,
            .text " is at most ", .inlineMath epsTex
          ]
    -- 9. Membership in an ε-relaxation: `R ∈ (S^*)^ε` or `R ∈ S^ε`
    if head == ``Membership.mem && args.size ≥ 2 then
      let some setExpr := argFromEnd? args 0 | return none
      let some elemExpr := argFromEnd? args 1 | return none
      if let some (eps, inner) := matchEpsilonRelaxationApp? setExpr then
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
  registerAppHandler distinguisherAdvantageValHandler
  registerAppHandler distinguisherProbHandler
  registerAppHandler (absorbHandler absorbName)
  registerAppHandler (absorbHandler typedDistinguisherAbsorbName)
  registerAppHandler (absorbHandler gamesAbsorbName)
  registerAppHandler dfunLikeEpsilonHandler
  registerAppHandler relaxedByHandler
  registerAppHandler (epsilonRelaxationBareHandler epsilonRelaxationName)
  registerAppHandler (epsilonRelaxationBareHandler specEpsilonRelaxationName)
  registerAppHandler (simulatorOrStarHandler simulatorImageName)
  registerAppHandler (simulatorOrStarHandler starName)
  registerAppHandler (visibleHandler visibleName)
  registerAppHandler (visibleHandler rsVisibleName)
  registerAppHandler (visibleHandler typedGameVisibleName)
  registerAppHandler (condEquivHandler conditionallyEquivalentName)
  registerAppHandler (condEquivHandler rsConditionallyEquivalentName)
  registerAppHandler gameEquivHandler
  registerAppHandler (winProbabilityHandler rsWinProbabilityName 2 1)
  registerAppHandler (winProbabilityHandler typedSolverWinProbabilityName 0 1)
  registerAppHandler closedUnderLatexHandler
  -- Type & proposition ontology handlers
  registerTypeHandler ccTypeHandler
  registerPropHandler ccPropHandler

initialize registerAll

end Informalization.CC.Ontology
