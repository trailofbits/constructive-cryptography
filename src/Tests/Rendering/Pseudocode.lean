import Rendering
import Examples.DSL.Components
import Tests.DSL.ParallelOutside
import Tests.DSL.Diagnostics

/-!
# Pseudocode fidelity and failure boundaries

Imported and local declarations retain their exact source. The view preserves initialization,
sampling scope, calls, branching, tuples, loops, signatures, clauses, comments and proofs.
Aliases, generated helpers, failed declarations and synthetic commands acquire no invented body.
-/

set_option linter.hashCommand false

open Lean Meta Elab Command Term CCWidget SystemAlgebra SystemAlgebra.DSL
open scoped SystemAlgebra.DSL

namespace Rendering.PseudocodeTests

elab "assert_source " name:ident " is " expected:str : command => do
  let doc ← liftCoreM (elabPseudocode name)
  unless doc.source == expected.getString && doc.reassemble == doc.source do
    throwError "source changed: {doc.source}"

elab "assert_no_source " name:ident : command => do
  unless ((sourceDocuments.getState (← getEnv)).find? name.getId).isNone do
    throwError "fabricated source for {name}"

-- These definitions were compiled in another module, without importing Rendering.
assert_source DSLExamples.SecretBit is "system SecretBit
  initialize
    secret ←$ 𝒰[Bool]
  on bit() → Bool
    return secret"

assert_source DSLExamples.FreshBits is "system FreshBits
  on bit() → Bool
    b ←$ 𝒰[Bool]
    return b"

assert_source DSLExamples.FirstRequests is "filter FirstRequests(q : Nat) : Pad
  domain h ↦ h.length ≤ q"

assert_source DSLTests.ParallelOutside.Forwarded is "system Forwarded ≔ Forward • EmptyCell"

-- Explicit and instance parameters, requirements, typed assignment and literal punctuation.
system Literal(q : Nat) [NeZero q]
  requires available : Nonempty (Fin q)
  on read() → Bool
    marker : String ← "<script>alert('x')</script> & \\alpha"
    -- Retain comments, including the words return and initialize.
    x ← (true &&
      marker == "<script>alert('x')</script> & \\alpha")
    if x
      x ← false
    return x

assert_source Literal is "system Literal(q : Nat) [NeZero q]
  requires available : Nonempty (Fin q)
  on read() → Bool
    marker : String ← \"<script>alert('x')</script> & \\\\alpha\"
    -- Retain comments, including the words return and initialize.
    x ← (true &&
      marker == \"<script>alert('x')</script> & \\\\alpha\")
    if x
      x ← false
    return x"

-- Unicode, quoted names and long tokens must remain selectable and untruncated.
system «σ with spaces»
  on longProcedureNameWhoseOriginalSpellingMustRemainVisibleAtEveryViewportWidth() → Bool
    return true

-- An ordinary Lean alias and generated implementation wrappers are not DSL declarations.
noncomputable def aliasOfSecret := DSLExamples.SecretBit (budget := 3)
assert_no_source Rendering.PseudocodeTests.aliasOfSecret
assert_no_source DSLExamples.SecretBit.program
assert_no_source DSLExamples.Padding.exact
assert_no_source DSLExamples.Counter.perPort
assert_no_source DSLTests.Diagnostics.WrongReply
assert_no_source DSLTests.Diagnostics.Budgeted

/-- error: cc_pseudocode: no recorded DSL source for Rendering.PseudocodeTests.aliasOfSecret -/
#guard_msgs in
#cc_pseudocode_show aliasOfSecret

/-- error: A system must declare at least one procedure. -/
#guard_msgs in
system Failed
  initialize
    x ← true

assert_no_source Rendering.PseudocodeTests.Failed

-- Check the partition of every imported record, including all control-flow forms.
run_cmd do
  for (_, doc) in (sourceDocuments.getState (← getEnv)).toList do
    unless doc.reassemble == doc.source do throwError "lossy source partition: {doc.declaration}"
  let fake := mkNode `systemComponentDecl #[mkAtom "system", mkIdent `Invented]
  unless (sourceDocument? "system Invented" `Invented fake #[]).isNone do
    throwError "synthetic command acquired source"
  let interfaceDoc ← liftCoreM (elabPseudocode (mkIdent ``DSLExamples.Store))
  let systemDoc ← liftCoreM (elabPseudocode (mkIdent ``DSLTests.ParallelOutside.Store))
  unless interfaceDoc.source.startsWith "interface Store" &&
      systemDoc.source.startsWith "system Store" do
    throwError "declarations with the same short name were conflated"

-- Applied arguments remain on the diagram; the expanded text remains the generic declaration.
run_cmd runTermElabM fun _ => do
  let e ← elabTerm (← `(DSLExamples.BoundedCounter 7 (budget := 2))) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let d ← parseDiagram e
  let some doc := d.elem.pseudocode? | throwError "applied DSL declaration lost its source"
  unless doc.declaration == ``DSLExamples.BoundedCounter &&
      doc.source.startsWith "system BoundedCounter(q : Nat)" do
    throwError "declaration parameters were substituted"
  unless d.elem.source == (← ppShort e) do throwError "application was discarded"

end Rendering.PseudocodeTests
