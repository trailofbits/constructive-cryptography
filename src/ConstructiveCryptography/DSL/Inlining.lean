module

public import ConstructiveCryptography.DSL.Equations
public import ConstructiveCryptography.Instances.Category
public import RandomSystems.Typed.DSL.Tactics

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
  (α ≫ rightContext B (ofAutomaton C g η)) • ofAutomaton B f ξ
    = α • (ofAutomaton B f ξ ∥ ofAutomaton C g η)         comp_smul, attach_rightContext
    = α • ofAutomaton (B ⊗ C) (parallelStep f g) (ξ × η)  parallel_ofAutomaton
    = ofAutomaton A (P.combine (parallelStep f g)) …       α's constructor law, for program P
```

A direct attachment to the two parallel automata enters this chain at its second line.

`inline using hR` takes an explicit certificate `hR : R = TypedSystem.ofMemoryless B ν`
and applies the typed memoryless composition law of the displayed constructor
(`TypedConverter.ofProgram_smul_ofMemoryless` and its port-preserving and costed forms).
For `α` the converter of a program `P` with call bound `b`:

```text
  α • R = ofMemoryless A κ   ⇐   ∀ s o u, P.memorylessReplyLaw ν s o u b [] = (κ o u).1
```

Raw goals and certificates `R.1 = memoryless _ (portLaw ν)` use the same laws through the
cumulative projection. The certificate is always supplied explicitly.

`inline` then splits the generated `Option` state and the procedure labels, and rewrites each reply
law with the generated invocation equations. A second certificate `hT` is for the converter's
own source `T` beside its inside system; the program then runs against `parallelLaw ν ν'`.

The command uses only the supplied definitions, named attachment laws and generated equations.
The caller proves the remaining identities of laws (identity or composed pushforwards, product
laws) and any state-dependent obligations.
-/

@[expose] public meta section

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

/-- The displayed converter and resource on the left of the equality. -/
def attachmentParts : TacticM (Expr × Expr) := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some (_, lhs, _) := target.eq? | throwError "inline expects an equality of systems or laws."
  let some attachment := lhs.find? fun e =>
      e.isAppOf ``HSMul.hSMul || e.isAppOf ``TypedConverter.attach
    | throwError "No program attachment on the left of the equality."
  let args := attachment.getAppArgs
  return (args[args.size - 2]!, args[args.size - 1]!)

/-- The head constant of the attached converter; selecting its law keeps an exact-cost
converter's domain guarantee. -/
def attachmentConstructor : TacticM Name := do
  let (converter, _) ← attachmentParts
  let some constructor := converter.getAppFn.constName?
    | throwError "The attached converter is not a displayed program constructor."
  return constructor

/-- Place a displayed converter's own source beside its inside resource. -/
def exposeOwnSource : TacticM Unit := do
  let (converter, _) ← attachmentParts
  unless converter.isAppOf ``CategoryTheory.CategoryStruct.comp ||
      converter.isAppOf ``TypedConverter.comp do
    throwError "No displayed serial composition with an own source."
  let args := converter.getAppArgs
  unless args.back!.isAppOf ``TypedConverter.rightContext do
    throwError "The inner converter is not a displayed right context."
  let serialLaw := if converter.isAppOf ``TypedConverter.comp then
    ``TypedConverter.comp_smul else ``Interface.comp_smul
  evalTactic (← `(tactic| rw [$(mkIdent serialLaw):ident, TypedConverter.attach_rightContext]))

/-- Rewrite one displayed automaton attachment with its constructor's composition law. -/
def inlineAutomaton : TacticM Unit := do
  let (_, resource) ← attachmentParts
  unless resource.isAppOf ``TypedSystem.ofAutomaton do
    throwError "Inside resource is not a displayed automaton; supply its memoryless certificate."
  let law ← match ← attachmentConstructor with
    | ``TypedConverter.ofProgram => pure ``TypedConverter.ofProgram_smul_ofAutomaton
    | ``TypedConverter.ofPreservingProgram =>
      pure ``TypedConverter.ofPreservingProgram_smul_ofAutomaton
    | ``TypedConverter.ofCostedProgram => pure ``TypedConverter.ofCostedProgram_smul_ofAutomaton
    | name => throwError "No automaton inlining rule for {name}."
  evalTactic (← `(tactic| rw (transparency := .default) [$(mkIdent law):ident]))

/-- Whether `statement` is an equality in `TypedSystem A`, for some interface `A`. -/
def isTypedSystemEquality (statement : Expr) : MetaM Bool := do
  let some (carrier, _, _) := statement.eq? | return false
  withNewMCtxDepth do
    let interface ← mkFreshExprMVar (mkConst ``Interface)
    isDefEq carrier (mkApp (mkConst ``TypedSystem) interface)

/-- Keep the supplied equality in the goal's carrier, projecting or lifting only at its boundary. -/
def memorylessCertificate (certificate : TSyntax `term) (typedGoal : Bool) :
    TacticM (TSyntax `term) := do
  let saved ← saveState
  let typed ← try
    withMainContext do
      let proof ← Term.elabTerm certificate none
      isTypedSystemEquality (← instantiateMVars (← inferType proof))
  finally
    -- Inspect the carrier without retaining holes; the attachment later determines them.
    saved.restore
  if typed == typedGoal then
    pure certificate
  else if typedGoal then
    `(Subtype.ext $certificate)
  else
    `(TypedSystem.eq_memoryless_of_eq_ofMemoryless $certificate)

/-- Apply the memoryless law for the displayed constructor and the goal's carrier. -/
def applyMemorylessLaw (certificate : TSyntax `term) : TacticM Unit := do
  let typed ← withMainContext do
    isTypedSystemEquality (← instantiateMVars (← getMainTarget))
  match ← attachmentConstructor with
  | ``TypedConverter.ofProgram =>
    let law := if typed then ``TypedConverter.ofProgram_smul_ofMemoryless
      else ``TypedConverter.ofProgram_smul_memoryless
    evalTactic (← `(tactic| refine $(mkIdent law):ident _ _ _ _ $certificate ?_))
  | ``TypedConverter.ofPreservingProgram =>
    let law := if typed then ``TypedConverter.ofPreservingProgram_smul_ofMemoryless
      else ``TypedConverter.ofPreservingProgram_smul_memoryless
    evalTactic (← `(tactic| refine $(mkIdent law):ident _ _ _ _ _ _ _ _ $certificate ?_))
  | ``TypedConverter.ofCostedProgram =>
    let law := if typed then ``TypedConverter.ofCostedProgram_smul_ofMemoryless
      else ``TypedConverter.ofCostedProgram_smul_memoryless
    evalTactic (← `(tactic| refine $(mkIdent law):ident _ _ _ _ _ _ _ $certificate ?_))
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
        exposeOwnSource
      catch _ => saved.restore
      evalTactic (← `(tactic| simp -failIfUnchanged only
        [TypedSystem.source, TypedSystem.parallel_ofAutomaton]))
      unless (← getGoals).isEmpty do inlineAutomaton
      evalTactic (← `(tactic| all_goals simp -failIfUnchanged only [component_equations]))
    else
      if certificates.size > 2 then
        throwError "Supply the inside system's certificate and, optionally, its own source's."
      let typed ← withMainContext do
        isTypedSystemEquality (← instantiateMVars (← getMainTarget))
      let certificate ← memorylessCertificate certificates[0]! typed
      if certificates.size == 2 then
        exposeOwnSource
        let source ← memorylessCertificate certificates[1]! typed
        let parallelCertificate ← if typed then
          `(TypedSystem.parallel_eq_ofMemoryless $certificate $source)
        else
          `(TypedSystem.parallel_eq_memoryless $certificate $source)
        applyMemorylessLaw parallelCertificate
      else
        applyMemorylessLaw certificate
      exposeInvocationLaws

end SystemAlgebra.DSL
