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
import RandomSystems.System.Automaton
import RandomSystems.Converter.Program
import RandomSystems.Converter.ProgramAttachment
import RandomSystems.Converter.ParallelPDS
import RandomSystems.Typed.Automaton
import RandomSystems.Typed.Functional
import RandomSystems.Typed.Memoryless
import RandomSystems.Typed.SamplingAlgebra
import RandomSystems.Typed.SamplingDistance
import RandomSystems.Typed.ParallelAll
import RandomSystems.Typed.ParallelAllAttachment
import RandomSystems.Typed.ParallelAllContext
import Commons.Definitions.Ideal

/-!
# Family E: Systems, Converters, Bisimulation, Memoryless Sources & Sampling Algebra

Generic Kyle Miller symbolic explainers for concrete random-system and converter realizations:
* Automaton & program bisimulation / state-relation equivalence (`automatonSystem_eq_of_bisim`,
  `Program.combine_bisim`, `DDC.ofProgram_eq_of_stateMap`, `DDC.ofProgram_eq_of_stateRel`,
  `TypedSystem.ofAutomaton_map_congr`, `TypedSystem.eq_ofFunction`, `URF.lazy_eq`);
* Memoryless sources and DSL converter inlining (`MemorylessSource.eq_ofMemoryless`,
  `TypedSystem.source_eq_ofMemoryless`, `TypedSystem.parallel_ofMemoryless`,
  `TypedConverter.ofProgram_smul_ofMemoryless`, `ofPreservingProgram_smul_ofMemoryless`,
  `ofCostedProgram_smul_ofMemoryless`);
* Retained-sample algebra (`TypedSystem.sample_prod`, `sample_comm`, `sample_fTransform`,
  `parallel_sample_left`, `parallel_sample_right`, `TypedConverter.smul_sample`,
  `TypedSystem.transcriptDistance_sample_le`);
* Indexed parallel families (`TypedConverter.parallelAll_attach`, `parallelAllContext_smul`).
-/

namespace Informalization.CC.Families.Systems

open Lean Meta
open Informalization.Core.Grammar
open Informalization.Core.Hygiene
open Informalization.Core.LeanTeX
open Informalization.Core.Ontology
open Informalization.Core.Explanation
open Informalization.Core.ProofGraph

private def mkStep (ctx : DecompCtx) (id : String) (content : Array Inline)
    (children : Array ProofNode) (expected : Expr) (origin : Name) :
    StateRefT DiscourseState MetaM ProofNode := do
  modify (·.markEmitted)
  let goal ← buildGoalState ctx.tbl expected
  return .step id content children (some goal) none (some origin.toString)

/-- Explainer for automaton/converter bisimulation, state-relation equivalence, and functional
or lazy realizations of random systems. -/
def bisimulationAndRealizationExplainer : RuleExplainer where
  priority := 140
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    if head == ``SystemAlgebra.automatonSystem_eq_of_bisim ||
       head == ``SystemAlgebra.Program.combine_bisim ||
       head == ``SystemAlgebra.Program.invoke_bisim ||
       head == ``SystemAlgebra.parallelStep_bisim ||
       head == ``SystemAlgebra.IsBisim.comp then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-bisim-{head}" (fun conclInl =>
        #[.text "By state bisimulation, "] ++ conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.DDC.ofProgram_eq_of_stateMap ||
       head == ``SystemAlgebra.DDC.ofProgramOn_eq_of_stateMap ||
       head == ``SystemAlgebra.DDC.ofProgram_eq_of_stateRel ||
       head == ``SystemAlgebra.DDC.ofProgramOn_eq_of_stateRel ||
       head == ``SystemAlgebra.TypedSystem.ofAutomaton_map_congr then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-staterel-{head}" (fun conclInl =>
        #[.text "Since both state representations induce identical input-output behavior, "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.TypedSystem.eq_ofFunction then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-func-{head}" (fun conclInl =>
        #[.text "Since the system answers every query deterministically according to the prescribed function, "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.TypedSystem.parallel_ofAutomaton then
      return ← finish s!"cc-par-auto-{head}" (fun conclInl =>
        #[.text "Composing the independent automata in parallel yields "] ++
        conclInl ++ #[.text "."]) #[]
    if head == ``Commons.URF.lazy_eq then
      return ← finish s!"cc-lazy-urf-{head}" (fun conclInl =>
        #[.text "Lazy and eager uniform random-function sampling induce identical transcript distributions: "] ++
        conclInl ++ #[.text "."]) #[]
    return none

/-- Explainer for memoryless sources, DSL converter attachment laws, sampling algebra, and
indexed parallel families (`ParallelAll`). -/
def memorylessAndSamplingExplainer : RuleExplainer where
  priority := 140
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let finish (id : String) (mkMsg : Array Inline → Array Inline)
        (children : Array ProofNode) := do
      let conclInl ← renderProposition ctx.tbl expected
      let node ← mkStep ctx id (mkMsg conclInl) children expected head
      return some #[node]
    if head == ``Commons.MemorylessSource.eq_ofMemoryless ||
       head == ``Commons.MemorylessSource.memoryless_eq ||
       head == ``SystemAlgebra.TypedSystem.source_eq_ofMemoryless ||
       head == ``SystemAlgebra.TypedSystem.source_eq_memoryless then
      return ← finish s!"cc-mem-src-{head}" (fun conclInl =>
        #[.text "Since each query draws an independent fresh reply, "] ++
        conclInl ++ #[.text "."]) #[]
    if head == ``SystemAlgebra.TypedSystem.parallel_ofMemoryless ||
       head == ``SystemAlgebra.TypedSystem.parallel_eq_ofMemoryless ||
       head == ``SystemAlgebra.TypedSystem.parallel_eq_memoryless then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-mem-par-{head}" (fun conclInl =>
        #[.text "Composing independent memoryless systems in parallel gives "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.TypedConverter.ofProgram_smul_ofMemoryless ||
       head == ``SystemAlgebra.TypedConverter.ofPreservingProgram_smul_ofMemoryless ||
       head == ``SystemAlgebra.TypedConverter.ofCostedProgram_smul_ofMemoryless ||
       head == ``SystemAlgebra.TypedConverter.ofProgram_smul_memoryless ||
       head == ``SystemAlgebra.TypedConverter.ofPreservingProgram_smul_memoryless ||
       head == ``SystemAlgebra.TypedConverter.ofCostedProgram_smul_memoryless ||
       head == ``SystemAlgebra.TypedConverter.ofPreservingProgram_comp_rightContext_smul_memoryless then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-mem-prog-{head}" (fun conclInl =>
        #[.text "Inlining the converter against fresh inside replies gives "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.TypedSystem.sample_prod ||
       head == ``SystemAlgebra.TypedSystem.sample_comm ||
       head == ``SystemAlgebra.TypedSystem.sample_fTransform then
      return ← finish s!"cc-sample-alg-{head}" (fun conclInl =>
        #[.text "Reorganizing the initial sample gives "] ++
        conclInl ++ #[.text "."]) #[]
    if head == ``SystemAlgebra.TypedSystem.parallel_sample_left ||
       head == ``SystemAlgebra.TypedSystem.parallel_sample_right ||
       head == ``SystemAlgebra.TypedConverter.smul_sample then
      return ← finish s!"cc-sample-hoist-{head}" (fun conclInl =>
        #[.text "Pulling the initial sample outside gives "] ++
        conclInl ++ #[.text "."]) #[]
    if head == ``SystemAlgebra.TypedSystem.transcriptDistance_sample_le then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-sample-dist-{head}" (fun conclInl =>
        #[.text "Averaging over the shared initial sample gives "] ++
        conclInl ++ #[.text "."]) children
    if head == ``SystemAlgebra.TypedConverter.parallelAll_attach ||
       head == ``SystemAlgebra.TypedConverter.parallelAllContext_smul ||
       head == ``SystemAlgebra.TypedSystem.parallelAll_admits_iff then
      let children ← decompilePremiseArgs ctx decompileChild proof
      return ← finish s!"cc-parall-{head}" (fun conclInl =>
        #[.text "Attaching converters componentwise across the indexed family gives "] ++
        conclInl ++ #[.text "."]) children
    return none

initialize
  registerRuleExplainer bisimulationAndRealizationExplainer
  registerRuleExplainer memorylessAndSamplingExplainer

end Informalization.CC.Families.Systems
