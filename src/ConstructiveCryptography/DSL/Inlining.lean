import ConstructiveCryptography.DSL.Equations
import ConstructiveCryptography.InterfaceCategory
import RandomSystems.Typed.DSL.Tactics

/-! # Inlining a declared component

`inline` expands the compiler's wrappers (`component_definitions`) to the attached program
constructor, rewrites the attachment of the program to an automaton as their combined automaton
and simplifies with the generated equations. The optional `[definitions]` are further user
aliases to unfold first. The law is selected by the displayed constructor head (`ofProgram`,
`ofPreservingProgram`, `ofCostedProgram`), so it keeps that converter's domain guarantee and
never asks for a different budget: `TypedConverter.ofProgram_smul_ofAutomaton` and its
port-preserving and costed forms. A converter with its own source is first reshaped by the
serial, right-context and parallel-automaton laws:

```text
  (P ≫ rightContext B (ofAutomaton C g ν)) • ofAutomaton B f μ
    = P • (ofAutomaton B f μ ∥ ofAutomaton C g ν)         comp_smul, attach_rightContext
    = P • ofAutomaton (B ⊗ C) (parallelStep f g) (μ × ν)  parallel_ofAutomaton
    = ofAutomaton A (P.combine (parallelStep f g)) …       the automaton law of P's constructor
```

`inline using hR` takes an explicit memorylessness certificate
`hR : R.1 = memoryless _ (portLaw ν)` and applies the memoryless composition law of the displayed
constructor (`TypedConverter.ofProgram_smul_memoryless` and its port-preserving and costed
forms), for `C` the converter of a program `P` with call bound `b`:

```text
  (C • R).1 = memoryless _ (portLaw κ)   ⇐   ∀ s o u, P.memorylessReplyLaw ν s o u b [] = κ o u
```

It then splits the generated `Option` state and the procedure labels, and rewrites each reply
law with the generated invocation equations. A second certificate `hT` is for the converter's
own source `T` beside its inside system; the program then runs against `parallelLaw ν ν'`.

The command uses only the supplied definitions, named attachment laws and generated equations.
The caller proves the remaining identities of laws (identity or composed pushforwards, product
laws) and any state-dependent obligations.
-/

namespace SystemAlgebra.DSL

open Lean Elab Tactic Meta

/-- Expose one reply law per procedure, distinguishing the first invocation (`none`) from resumed
ones (`some s`). Only the compiler's `Option` state and procedure labels are split. -/
def exposeInvocationLaws : TacticM Unit := do
  let state := mkIdent (← liftMetaM <| mkFreshUserName `state)
  let port := mkIdent (← liftMetaM <| mkFreshUserName `port)
  let input := mkIdent (← liftMetaM <| mkFreshUserName `input)
  evalTactic (← `(tactic| intro $state:ident $port:ident $input:ident))
  withMainContext do
    let stateId ← getFVarId state
    if (← whnf (← stateId.getType)).isAppOf ``Option then
      evalTactic (← `(tactic| cases $state:ident))
  evalTactic (← `(tactic| all_goals component_cases $port:ident))
  evalTactic (← `(tactic| all_goals
    simp -failIfUnchanged only [component_equations]))

/-- The constructor of the converter at the attachment on the left of the equality. Inspecting
this head keeps an exact-cost converter from being unfolded into a different budgeted form. -/
def attachmentConstructor : TacticM Name := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (_, lhs, _) := target.eq? | throwError "inline expects an equality of systems or laws."
  let some attachment := lhs.find? fun e =>
      e.isAppOf ``HSMul.hSMul || e.isAppOf ``TypedConverter.attach
    | throwError "No program attachment on the left of the equality."
  let args := attachment.getAppArgs
  let converter := args[args.size - 2]!
  let some constructor := converter.getAppFn.constName?
    | throwError "The attached converter is not a displayed program constructor."
  return constructor

/-- Rewrite one automaton attachment using the law for its displayed program constructor. -/
def inlineAutomaton : TacticM Unit := do
  let law ← match ← attachmentConstructor with
    | ``TypedConverter.ofProgram => pure ``TypedConverter.ofProgram_smul_ofAutomaton
    | ``TypedConverter.ofPreservingProgram =>
      pure ``TypedConverter.ofPreservingProgram_smul_ofAutomaton
    | ``TypedConverter.ofCostedProgram => pure ``TypedConverter.ofCostedProgram_smul_ofAutomaton
    | name => throwError "No automaton inlining rule for {name}."
  evalTactic (← `(tactic| rw (transparency := .default) [$(mkIdent law):ident]))

/-- Apply the memoryless composition law selected by the displayed program constructor,
keeping its budget or cost guarantee and the supplied inside-system certificate. -/
def applyMemorylessLaw (certificate : TSyntax `term) : TacticM Unit := do
  match ← attachmentConstructor with
  | ``TypedConverter.ofProgram =>
    evalTactic (← `(tactic|
      refine TypedConverter.ofProgram_smul_memoryless _ _ _ _ $certificate ?_))
  | ``TypedConverter.ofPreservingProgram =>
    evalTactic (← `(tactic|
      refine TypedConverter.ofPreservingProgram_smul_memoryless _ _ _ _ _ _ _ _ $certificate ?_))
  | ``TypedConverter.ofCostedProgram =>
    evalTactic (← `(tactic|
      refine TypedConverter.ofCostedProgram_smul_memoryless _ _ _ _ _ _ _ $certificate ?_))
  | name => throwError "No memoryless inlining rule for {name}."

/-- Inline an attachment using its proved composition law. Registered wrappers are expanded
automatically; the optional bracketed definitions are further aliases. The optional certificates
assert that the inside system, and then the converter's own source, are memoryless. -/
syntax "inline" (" [" ident,* "]")? (" using " term,+)? : tactic

elab_rules : tactic
  | `(tactic| inline $[[$defs,*]]? $[using $certs,*]?) => do
    let definitions := defs.map (·.getElems) |>.getD #[]
    unless definitions.isEmpty do
      evalTactic (← `(tactic| unfold $definitions:ident*))
    evalTactic (← `(tactic| dsimp -failIfUnchanged only [component_definitions]))
    if (← getGoals).isEmpty then throwError "No program attachment to inline."
    let certificates := certs.map (·.getElems) |>.getD #[]
    if certificates.isEmpty then
      let saved ← saveState
      try
        evalTactic (← `(tactic| rw [Interface.comp_smul, TypedConverter.attach_rightContext]))
        evalTactic (← `(tactic| simp -failIfUnchanged only
          [TypedSystem.source, TypedSystem.parallel_ofAutomaton]))
      catch _ => saved.restore
      unless (← getGoals).isEmpty do inlineAutomaton
      evalTactic (← `(tactic| all_goals simp -failIfUnchanged only [component_equations]))
    else
      if certificates.size > 2 then
        throwError "Supply the inside system's certificate and, optionally, its own source's."
      let certificate := certificates[0]!
      if certificates.size == 2 then
        let source := certificates[1]!
        evalTactic (← `(tactic| rw [Interface.comp_smul, TypedConverter.attach_rightContext]))
        applyMemorylessLaw (← `(TypedSystem.parallel_eq_memoryless $certificate $source))
      else
        applyMemorylessLaw certificate
      exposeInvocationLaws

end SystemAlgebra.DSL
