module

public import RandomSystems.Typed.Parallel
public import RandomSystems.Typed.Functional

/-!
# Parallel replies at a zero-probability prefix

A right reply of `true` from the constant-false system is impossible but has consistent tags.
The domain projection still applies, and the left-extension law retains its zero right mass.
-/

@[expose] public section

namespace SystemAlgebra.Tests.ParallelReply

/-- One unit port, unit queries, Boolean replies, and a two-query domain. -/
abbrev bitPort := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 2

/-- Every admitted query returns `false`. -/
noncomputable def falseReply : TypedSystem bitPort := TypedSystem.ofFunction fun _ _ => false

/-- A `true` reply has zero mass under the constant-false resource. -/
lemma falseReply_true_mass : falseReply.1 [(⟨(), ()⟩, ⟨(), true⟩)] = 0 := by
  rw [falseReply, TypedSystem.ofFunction_mass, ite_eq_right]
  intro hh
  have he := hh.2 _ (List.mem_singleton_self _)
  cases he

/-- The impossible right reply is nevertheless a consistent exchange. -/
lemma right_true_consistent : RandomSystem.parallelConsistent
    (A := Σ i, bitPort.X i) (B := Σ i, bitPort.Y i)
    [(⟨some (), (⟨(), ()⟩ : Σ i, bitPort.X i)⟩,
      ⟨some (), (⟨(), true⟩ : Σ i, bitPort.Y i)⟩)] := by
  intro z hz
  obtain rfl := List.mem_singleton.mp hz
  rfl

/-- Domain projection applies even after the impossible right reply. -/
example : (bitPort.tensor bitPort).inputDomain
      [(⟨.inr (), ()⟩, ⟨.inr (), true⟩)] ⟨.inl (), ()⟩ ↔
    bitPort.inputDomain [] ⟨(), ()⟩ ∧
      (([(⟨(), ()⟩ : Σ i, bitPort.X i)] = []) ∨ bitPort.domain [⟨(), ()⟩]) :=
  tensor_inputDomain_inl_iff (A := bitPort) (B := bitPort)
    [(⟨.inr (), ()⟩, ⟨.inr (), true⟩)] right_true_consistent () ()

/-- The unchanged zero right-prefix mass makes every next left reply impossible. -/
lemma left_extension_zero (y : Bool) :
    (TypedSystem.parallel falseReply falseReply).1
      ([(⟨.inr (), ()⟩, ⟨.inr (), true⟩)] ++ [(⟨.inl (), ()⟩, ⟨.inl (), y⟩)]) = 0 := by
  rw [TypedSystem.parallel_mass_snoc_inl falseReply falseReply
    [(⟨.inr (), ()⟩, ⟨.inr (), true⟩)] right_true_consistent]
  change falseReply.1 [(⟨(), ()⟩, ⟨(), y⟩)] *
    falseReply.1 [(⟨(), ()⟩, ⟨(), true⟩)] = 0
  rw [falseReply_true_mass, mul_zero]

#print axioms tensor_inputDomain_inl_iff
#print axioms TypedSystem.parallel_mass_snoc_inl
#print axioms left_extension_zero

end SystemAlgebra.Tests.ParallelReply
