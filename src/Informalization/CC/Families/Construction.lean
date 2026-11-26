/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Grammar
import Informalization.Core.Hygiene
import Informalization.Core.LeanTeX
import Informalization.Core.Ontology
import Informalization.Core.ProofGraph
import ConstructiveCryptography.Construction.Basic
import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import ConstructiveCryptography.CryptographicAlgebra.Epsilon
import ConstructiveCryptography.CryptographicAlgebra.Star
import ConstructiveCryptography.CryptographicAlgebra.SimulatorComposition
import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability

/-!
# Family A: Constructive Cryptography Constructions & Indifferentiability

Generic Kyle Miller symbolic rule explainers for the Constructive Cryptography construction
calculus (Maurer–Renner 2016, Jost–Maurer 2020):
* exact and approximate constructions (`Constructs`, `ConstructsWithin`),
* serial and parallel composition (`serial`, `parallel`, `serial_epsilonRelaxation`),
* context-insensitivity (`left_context`, `right_context`: $U \parallel R \xrightarrow{\pi} U \parallel S$),
* simulator witnesses and indifferentiability composition (`constructs_of_simulatorImage`,
  `constructs_of_simulator`, `serial_simulatorImage`, `mixed_application_of_indifferentiability`),
* relaxation lifting (`epsilonRelaxation`, `star`, `simulatorImage_comp`).

Every explainer matches on compile-time-checked Lean constants and recursively delegates all
checked sub-proofs to `decompileChild` so clicking `⊕` descends across lemma boundaries
without repetition.
-/

namespace Informalization.CC.Families.Construction

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph

/-- Extract an explicit converter/simulator argument at a given position from the end,
falling back gracefully if not a non-Prop term. -/
private def renderArgFromEnd? (tbl : SymbolTable) (args : Array Expr) (offsetFromEnd : Nat) :
    MetaM (Option String) := do
  if offsetFromEnd ≥ args.size then return none
  let arg := args[args.size - 1 - offsetFromEnd]!
  try
    let ty ← inferType arg
    if ← isProp ty then return none
    return some (← exprToLatex arg tbl)
  catch _ => return none

/-- Helper to construct a checked `ProofNode.step` with live goal state (no nested diagrams). -/
private def mkFamilyStep (ctx : DecompCtx) (id : String) (content : Array Inline)
    (children : Array ProofNode) (expected : Expr) (origin : Name) :
    StateRefT DiscourseState MetaM ProofNode := do
  modify (·.markEmitted)
  let goal ← buildGoalState ctx.tbl expected
  return .step id content children (some goal) none (some origin.toString)

/-- Explainer for serial, parallel, and context-insensitive CC construction steps. -/
def constructionCompositionExplainer : RuleExplainer where
  priority := 145
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkFamilyStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial ||
       head == ``ConstructiveCryptography.Construction.Constructible.serial then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-serial-{head}" (fun conclInl =>
        #[.text "By serial composition, "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-serial-approx-{head}" (fun conclInl =>
        #[.text "By serial composition, summing the error bounds gives "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulators then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-serial-sim-{head}" (fun conclInl =>
        #[.text "By serial composition and simulator commutation, "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel ||
       head == ``ConstructiveCryptography.Specification.Constructs.parallel then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-parallel-{head}" (fun conclInl =>
        #[.text "By parallel composition, "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-parallel-approx-{head}" (fun conclInl =>
        #[.text "By parallel composition, summing the error bounds gives "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context ||
       head == ``ConstructiveCryptography.Specification.Constructs.left_context ||
       head == ``ConstructiveCryptography.Specification.Constructs.right_context then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-context-{head}" (fun conclInl =>
        #[.text "By context-insensitivity, "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-context-approx-{head}" (fun conclInl =>
        #[.text "By context-insensitivity, "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.mono then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-mono-{head}" (fun conclInl =>
        #[.text "By monotonicity of construction, "] ++ conclInl ++ #[.text "."]) children
    return none

/-- Explainer for simulator witnesses, indifferentiability composition, and relaxations. -/
def indifferentiabilityExplainer : RuleExplainer where
  priority := 150
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let args := proof.getAppArgs
    let some head := fn.constName? | return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkFamilyStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulatorImage ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_star_of_simulator ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_star_of_simulator then
      let children ← decompilePremiseArgs ctx decompileChild proof
      let simTex? ← renderArgFromEnd? ctx.tbl args 2
      let simPhrase : Array Inline := match simTex? with
        | some s => #[.text "Exhibiting the simulator ", .inlineMath s, .text " yields "]
        | none => #[.text "Exhibiting an admitted simulator yields "]
      return ← finish s!"cc-sim-witness-{head}" (fun conclInl =>
        simPhrase ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulatorImage_whiskerRight then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-indiff-serial-{head}" (fun conclInl =>
        #[.text "By serial composition under indifferentiability, "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.mixed_application_of_indifferentiability ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.mixed_application_of_indifferentiability_whiskerRight then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-indiff-mixed-{head}" (fun conclInl =>
        #[.text "Averaging over a common simulator by non-expansion and convexity gives "] ++
        conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.simulatorImage ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.simulatorImage then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-sim-image-lift-{head}" (fun conclInl =>
        #[.text "Since the honest protocol and simulator act on disjoint interfaces, "] ++
        conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.epsilonRelaxation ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.star ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.star then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-relax-lift-{head}" (fun conclInl =>
        #[.text "Lifting along the relaxation gives "] ++ conclInl ++ #[.text "."]) children
    if head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.simulatorImage_comp ||
       head == ``ConstructiveCryptography.CryptographicAlgebra.Specification.simulatorImage_comp_subset then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-sim-comp-{head}" (fun conclInl =>
        #[.text "Composing successive simulators serially gives "] ++ conclInl ++ #[.text "."]) children
    return none

initialize
  registerRuleExplainer constructionCompositionExplainer
  registerRuleExplainer indifferentiabilityExplainer

end Informalization.CC.Families.Construction
