module

public import RandomSystems.Typed.Memoryless
public import RandomSystems.Typed.ProbProgramAttachment
public import ConstructiveCryptography.Notation

/-!
# Memoryless systems in a common context

The typed parallel equation rewrites under an arbitrary converter. The concrete assembly
places the fair-bit source beside a memoryless component on its selected interface.
Presenting `TypedSystem.ofMemoryless` and `TypedSystem.ofFunction` as one-state automata
connects them directly to `TypedConverter.ofProgram_smul_ofProbAutomaton` in one rewrite.
-/

@[expose] public section

open CategoryTheory SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution

/-- Replacing the component pair by its combined reply law preserves the context `α`. -/
example
    -- `A`, `B` are the component interfaces; `C` is the interface exposed by `α`.
    {A B C : Interface}
    (α : TypedConverter C (Interface.tensor A B))
    -- `ν₁ i x` and `ν₂ j y` give the two components' fresh reply laws.
    (ν₁ : ∀ i, A.X i → ProbDist (A.Y i)) (ν₂ : ∀ j, B.X j → ProbDist (B.Y j)) :
    α • TypedSystem.parallel (TypedSystem.ofMemoryless A ν₁)
        (TypedSystem.ofMemoryless B ν₂) =
      α • TypedSystem.ofMemoryless (Interface.tensor A B)
        (RandomSystem.parallelLaw ν₁ ν₂) := by
  rw [TypedSystem.parallel_ofMemoryless]

/-- A fair-bit source fits beside an arbitrary memoryless system under `α`. -/
example
    -- `q` bounds the source's triggers; `B` retains its domain; `C` is exposed by `α`.
    {B C : Interface} (q : ℕ)
    (α : TypedConverter C (Interface.tensor (Interface.source Bool q) B))
    -- `ν j x` is the fresh reply law at query `x` on port `j` of `B`.
    (ν : ∀ j, B.X j → ProbDist (B.Y j)) :
    α • TypedSystem.parallel (TypedSystem.source 𝒰[Bool] q)
        (TypedSystem.ofMemoryless B ν) =
      α • TypedSystem.ofMemoryless (Interface.tensor (Interface.source Bool q) B)
        (RandomSystem.parallelLaw (fun _ _ => 𝒰[Bool]) ν) := by
  rw [TypedSystem.source_eq_ofMemoryless, TypedSystem.parallel_ofMemoryless]

/-- A converter attached to a memoryless source is presented as a combined automaton by
`ofProgram_smul_ofProbAutomaton` after one rewrite. -/
example (q : ℕ)
    (P : Program Unit Unit Unit (fun _ => Unit) (fun _ => Bool) (fun _ => Unit) (fun _ => Bool))
    (hb : P.Bounded 1) :
    let B := Interface.source Bool q
    let hB : ∀ xs, xs ≠ [] → xs.length ≤ 1 * B.bound → B.domain xs := fun xs hne hlen =>
      ⟨hne, by simpa only [B, Interface.source, Interface.queryBudget, one_mul] using hlen⟩
    TypedConverter.ofProgram (A := B) (B := B) () P hb hB •
        TypedSystem.ofMemoryless B (fun _ _ => 𝒰[Bool]) =
      TypedSystem.ofProbAutomaton B
        (P.probCombine (ProbStep.fresh fun _ _ => 𝒰[Bool]) hb)
        ((ProbDist.single ()).map fun r => ((), r)) := by
  intro B hB
  rw [TypedSystem.ofMemoryless_eq_ofProbAutomaton, TypedConverter.ofProgram_smul_ofProbAutomaton]

/-- A reply function is the one-state automaton of its point laws, so
`ofProgram_smul_ofProbAutomaton` applies directly to a program attached to it. -/
example (q : ℕ)
    (P : Program Unit Unit Unit (fun _ => Bool) (fun _ => Bool) (fun _ => Bool) (fun _ => Bool))
    (hb : P.Bounded 1) :
    let B := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) q
    let f : ∀ _ : Unit, Bool → Bool := fun _ b => !b
    let hB : ∀ xs, xs ≠ [] → xs.length ≤ 1 * B.bound → B.domain xs := fun xs hne hlen =>
      ⟨hne, by simpa only [B, Interface.queryBudget, one_mul] using hlen⟩
    TypedConverter.ofProgram (A := B) (B := B) () P hb hB • TypedSystem.ofFunction (A := B) f =
      TypedSystem.ofProbAutomaton B
        (P.probCombine (ProbStep.fresh fun i x => ProbDist.single (f i x)) hb)
        ((ProbDist.single ()).map fun r => ((), r)) := by
  intro B f hB
  rw [TypedSystem.ofFunction_eq_ofProbAutomaton, TypedConverter.ofProgram_smul_ofProbAutomaton]

/-- Concrete 1-call program flipping a memoryless fair bit, presented via one rewrite. -/
example (q : ℕ) :
    let B := Interface.source Bool q
    let P : Program Unit Unit Unit (fun _ => Unit) (fun _ => Bool) (fun _ => Unit)
        (fun _ => Bool) :=
      fun _ _ _ => callProg () () fun b => returnProg ((), !b)
    let hb : P.Bounded 1 := by
      intro _ _ _
      exact callBound_call (X := fun _ => Unit) () () _ fun _ => callBound_return 0 _
    let hB : ∀ xs, xs ≠ [] → xs.length ≤ 1 * B.bound → B.domain xs := fun xs hne hlen =>
      ⟨hne, by simpa only [B, Interface.source, Interface.queryBudget, one_mul] using hlen⟩
    TypedConverter.ofProgram (A := B) (B := B) () P hb hB •
        TypedSystem.ofMemoryless B (fun _ _ => 𝒰[Bool]) =
      TypedSystem.ofProbAutomaton B
        (P.probCombine (ProbStep.fresh fun _ _ => 𝒰[Bool]) hb)
        ((ProbDist.single ()).map fun r => ((), r)) := by
  intro B P hb hB
  rw [TypedSystem.ofMemoryless_eq_ofProbAutomaton, TypedConverter.ofProgram_smul_ofProbAutomaton]

/-- Rewriting to one-state automata composes cleanly with `cc_normalize` on converter chains. -/
example {A B C : Interface} (α : C ⟶ B) (β : B ⟶ A) (f : ∀ i, A.X i → A.Y i) :
    (α ≫ β) • TypedSystem.ofFunction (A := A) f =
      α • (β • TypedSystem.ofProbAutomaton A
        (ProbStep.fresh fun i x => ProbDist.single (f i x)) (ProbDist.single ())) := by
  rw [TypedSystem.ofFunction_eq_ofProbAutomaton]
  cc_normalize

#print axioms TypedSystem.ofMemoryless
#print axioms TypedSystem.ofMemoryless_val
#print axioms TypedSystem.ofMemoryless_eq_ofProbAutomaton
#print axioms TypedSystem.ofFunction_eq_ofProbAutomaton
#print axioms TypedSystem.source_eq_ofMemoryless
#print axioms TypedSystem.parallel_ofMemoryless
