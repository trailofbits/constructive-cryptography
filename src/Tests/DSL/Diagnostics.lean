import ConstructiveCryptography.DSL

/-!
# DSL diagnostics

The DSL accepts a converter whose inside calls it can bound uniformly, a one-port interface with
a parameter without changing instance search, alphabets over the parameters their ports mention, and a component parameter named `q`. It rejects,
with the messages below, components that mention the reserved budget names, infinite alphabets, inside calls that grow with the private state,
missing replies, hidden calls, shadowed state, returns in initialization, laws that depend on
bindings, inside calls in initialization, unknown names and ill-typed replies.
-/

open SystemAlgebra SystemAlgebra.DSL
open scoped SystemAlgebra.DSL

namespace DSLTests.Diagnostics

-- A uniform bound on the inside calls is inferred from the displayed calls.
converter Forward
  inside f : Fin 16 → Fin 16
  on get(x : Fin 16) → Fin 16
    y ← f(x)
    return y

noncomputable example (q : ℕ) := Forward (budget := q)

-- A one-port interface with a parameter leaves instance search on other types unchanged.
interface Tagging(M : Type) [Fintype M]
  tag(message : M) → Bool

example : Fintype (Bool × Fin 3 × Fin 3) := inferInstance

-- Each alphabet takes only the parameters its ports mention, so instance search on the alphabet
-- at a port determines every argument.
interface Keyed(K C : Type) [Fintype K] [Fintype C]
  key() → K
  check(ciphertext : C) → Bool

example : (C : Type) → [Fintype C] → Keyed.Port → Type := Keyed.Input
example : (K : Type) → [Fintype K] → Keyed.Port → Type := Keyed.Output
example : ∀ i, Fintype ((Keyed.perPort (Fin 3) Bool fun _ => 1).X i) := inferInstance

-- A parameter named `q` keeps its meaning in the generated sources and per-port declarations.
interface Draw
  draw() → Bool

system Residue(q : ℕ) [NeZero q] : Draw
  initialize
    r ←$ 𝒰[Fin q]
  on draw() → Bool
    return decide (r.val = 0)

noncomputable example (k : ℕ) := Residue 3 (budget := k)
noncomputable example (k : ℕ) := Residue.perPort 3 (budget := fun _ => k)

-- The budget names are reserved: a component may neither bind nor reference them.
/-- error: `budget` is reserved: the generated declarations bind it for the query budget. -/
#guard_msgs in
system Budgeted(budget : ℕ) : Draw
  on draw() → Bool
    return decide (0 < 1)

/-- A global named like the exact budget. -/
def queries : ℕ := 3

/-- error: `queries` is reserved: the generated declarations bind it for the query budget. -/
#guard_msgs in
system Counted : Draw
  on draw() → Bool
    return decide (queries = 0)

/--
error: failed to synthesize instance of type class
  Fintype (Input Port.get)

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  Fintype (Output Port.get)

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
system Infinite
  on get(x : Nat) → Nat
    return x

/--
error: Could not infer a uniform internal-query bound: each invocation must make a number of
inside calls bounded independently of the private state.
-/
#guard_msgs (whitespace := lax) in
converter Growing
  inside f : Fin 2 → Fin 2
  initialize
    count ← (0 : Nat)
  on get(x : Fin 2) → Fin 2
    count ← count + 1
    for i ∈ List.range count
      y ← f(x)
    return x

/-- error: Every procedure path must return a reply. -/
#guard_msgs in
system MissingReturn
  on get(x : Fin 16) → Fin 16
    x ← x + 1

/-- error: Inside calls must occupy an entire assignment right-hand side. -/
#guard_msgs in
converter HiddenCall
  inside f : Fin 16 → Fin 16
  on get(x : Fin 16) → Fin 16
    return f(x) + 1

/-- error: Oracle parameter shadows persistent binding. -/
#guard_msgs in
system ShadowedState
  initialize
    key ← (0 : Fin 16)
  on get(key : Fin 16) → Fin 16
    return key

/-- error: Initialization has no return; its bindings persist. -/
#guard_msgs in
system InvalidInitialization
  initialize
    return 0
  on get() → Fin 16
    return 0

/--
error: A sampled law may depend on declaration parameters only; sample from a fixed law and
compute from the sample.
-/
#guard_msgs (whitespace := lax) in
system DependentLaw
  on get(n : Fin 4) → Fin 4
    x ←$ 𝒰[Fin (n.val + 1)]
    return 0

/-- error: Initialization cannot call inside ports; call them from a procedure. -/
#guard_msgs in
converter InitialCall
  inside f : Fin 16 → Fin 16
  initialize
    key ← f(0)
  on get(x : Fin 16) → Fin 16
    return key

/-- error: Unknown identifier `uninitialized` -/
#guard_msgs in
system Uninitialized
  on get() → Fin 16
    return uninitialized

/-- error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Fin 16 -/
#guard_msgs in
system WrongReply
  on get() → Fin 16
    return true

end DSLTests.Diagnostics
