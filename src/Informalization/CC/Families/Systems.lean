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

private def pickMaurerOpener (kind : TransitionKind) :
    StateRefT DiscourseState MetaM String := do
  let st ← get
  let (op, st') := st.pickOpener kind
  set st'
  return op

private def mkStep (ctx : DecompCtx) (id : String) (content : Array Inline)
    (children : Array ProofNode) (expected : Expr) (origin : Name) :
    StateRefT DiscourseState MetaM ProofNode := do
  let goal ← buildGoalState ctx.tbl expected
  let diagHtml ← (← diagramHookRef.get) expected
  return .step id content children (some goal) diagHtml (some origin.toString)

/-- Explainer for automaton/converter bisimulation, state-relation equivalence, and functional
or lazy realizations of random systems. -/
def bisimulationAndRealizationExplainer : RuleExplainer where
  priority := 140
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let conclInl ← renderProposition ctx.tbl expected
    if head == ``SystemAlgebra.automatonSystem_eq_of_bisim ||
       head == ``SystemAlgebra.Program.combine_bisim ||
       head == ``SystemAlgebra.Program.invoke_bisim ||
       head == ``SystemAlgebra.parallelStep_bisim ||
       head == ``SystemAlgebra.IsBisim.comp then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} by state bisimulation—preserving the invariant relation between internal states while producing identical replies to every query—we obtain "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-bisim-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.DDC.ofProgram_eq_of_stateMap ||
       head == ``SystemAlgebra.DDC.ofProgramOn_eq_of_stateMap ||
       head == ``SystemAlgebra.DDC.ofProgram_eq_of_stateRel ||
       head == ``SystemAlgebra.DDC.ofProgramOn_eq_of_stateRel ||
       head == ``SystemAlgebra.TypedSystem.ofAutomaton_map_congr then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} because the two state representations induce identical input-output behavior on every draw, their resulting systems coincide: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-staterel-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.TypedSystem.eq_ofFunction then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} since the system answers every admissible query history deterministically with probability one according to the prescribed function, "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-func-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.TypedSystem.parallel_ofAutomaton then
      let op ← pickMaurerOpener .elaboration
      let content : Array Inline :=
        #[.text s!"{op} running two independent automata in parallel is equivalent to a single product automaton initialized from the product state distribution: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-par-auto-{head}" content #[] expected head
      return some #[node]
    if head == ``Commons.URF.lazy_eq then
      let op ← pickMaurerOpener .elaboration
      let content : Array Inline :=
        #[.text s!"{op} lazy sampling—recording replies and drawing uniformly only on fresh inputs—has the exact same cumulative transcript distribution as an eagerly sampled uniform random function: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-lazy-urf-{head}" content #[] expected head
      return some #[node]
    return none

/-- Explainer for memoryless sources, DSL converter attachment laws, sampling algebra, and
indexed parallel families (`ParallelAll`). -/
def memorylessAndSamplingExplainer : RuleExplainer where
  priority := 140
  explain ctx decompileChild expected proof := do
    let fn := proof.getAppFn.consumeMData
    let some head := fn.constName? | return none
    let conclInl ← renderProposition ctx.tbl expected
    if head == ``Commons.MemorylessSource.eq_ofMemoryless ||
       head == ``Commons.MemorylessSource.memoryless_eq ||
       head == ``SystemAlgebra.TypedSystem.source_eq_ofMemoryless ||
       head == ``SystemAlgebra.TypedSystem.source_eq_memoryless then
      let op ← pickMaurerOpener .elaboration
      let content : Array Inline :=
        #[.text s!"{op} because each admissible query draws an independent fresh reply from the source distribution, "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-mem-src-{head}" content #[] expected head
      return some #[node]
    if head == ``SystemAlgebra.TypedSystem.parallel_ofMemoryless ||
       head == ``SystemAlgebra.TypedSystem.parallel_eq_ofMemoryless ||
       head == ``SystemAlgebra.TypedSystem.parallel_eq_memoryless then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} composing independent memoryless systems in parallel yields a memoryless system replying according to the queried component's law: "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-mem-par-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.TypedConverter.ofProgram_smul_ofMemoryless ||
       head == ``SystemAlgebra.TypedConverter.ofPreservingProgram_smul_ofMemoryless ||
       head == ``SystemAlgebra.TypedConverter.ofCostedProgram_smul_ofMemoryless ||
       head == ``SystemAlgebra.TypedConverter.ofProgram_smul_memoryless ||
       head == ``SystemAlgebra.TypedConverter.ofPreservingProgram_smul_memoryless ||
       head == ``SystemAlgebra.TypedConverter.ofCostedProgram_smul_memoryless ||
       head == ``SystemAlgebra.TypedConverter.ofPreservingProgram_comp_rightContext_smul_memoryless then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} inlining the converter program against fresh inside replies shows that each invocation yields the state-independent reply law, establishing "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-mem-prog-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.TypedSystem.sample_prod ||
       head == ``SystemAlgebra.TypedSystem.sample_comm ||
       head == ``SystemAlgebra.TypedSystem.sample_fTransform then
      let op ← pickMaurerOpener .elaboration
      let content : Array Inline :=
        #[.text s!"{op} by the algebra of retained initial draws (regrouping, reordering, or pushing forward the sampling law), "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-sample-alg-{head}" content #[] expected head
      return some #[node]
    if head == ``SystemAlgebra.TypedSystem.parallel_sample_left ||
       head == ``SystemAlgebra.TypedSystem.parallel_sample_right ||
       head == ``SystemAlgebra.TypedConverter.smul_sample then
      let op ← pickMaurerOpener .elaboration
      let content : Array Inline :=
        #[.text s!"{op} hoisting the retained initial draw outside the parallel composition or converter attachment leaves every transcript probability unchanged, giving "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-sample-hoist-{head}" content #[] expected head
      return some #[node]
    if head == ``SystemAlgebra.TypedSystem.transcriptDistance_sample_le then
      let op ← pickMaurerOpener .consequence
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} averaging the componentwise distinguishing bounds over the common initial draw preserves the uniform error bound, yielding "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-sample-dist-{head}" content children expected head
      return some #[node]
    if head == ``SystemAlgebra.TypedConverter.parallelAll_attach ||
       head == ``SystemAlgebra.TypedConverter.parallelAllContext_smul ||
       head == ``SystemAlgebra.TypedSystem.parallelAll_admits_iff then
      let op ← pickMaurerOpener .elaboration
      let children ← decompilePremiseArgs ctx decompileChild proof
      let content : Array Inline :=
        #[.text s!"{op} attaching converters across an indexed parallel family acts independently on each tagged component, yielding "] ++
        conclInl ++ #[.text "."]
      let node ← mkStep ctx s!"cc-parall-{head}" content children expected head
      return some #[node]
    return none

initialize
  registerRuleExplainer bisimulationAndRealizationExplainer
  registerRuleExplainer memorylessAndSamplingExplainer

end Informalization.CC.Families.Systems
