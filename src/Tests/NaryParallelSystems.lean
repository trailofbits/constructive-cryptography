import RandomSystems.Cumulative.ParallelAll

/-!
# Finite parallel systems: boundary cases

The empty family has unit mass. Tagged component histories can interleave, while a reply
carrying the wrong component tag is rejected. The domain constructor accepts heterogeneous
component alphabets.
-/

namespace SystemAlgebra.Tests

noncomputable section

section Empty

variable (D : ∀ _k : Empty, Domain Unit Unit)
  (R : ∀ k : Empty, RandomSystem Unit Unit (D k))

example : (RandomSystem.parallelAll R) [] = 1 := RandomSystem.mass_nil _

example : ¬ parallelAllInputs (K := Empty) (I := fun _ => Unit)
    (F := fun _ _ => Unit) (fun k => nomatch k) [] := by
  simp [parallelAllInputs]

end Empty

section Interleaved

variable (D : ∀ _k : Bool, Domain Unit Unit)
  (R : ∀ k : Bool, RandomSystem Unit Unit (D k))

example : RandomSystem.parallelAll R
    [(⟨true, ()⟩, ⟨true, ()⟩), (⟨false, ()⟩, ⟨false, ()⟩)] =
      R true [((), ())] * R false [((), ())] := by
  rw [RandomSystem.parallelAll_mass]
  simp [RandomSystem.parallelAllConsistent, RandomSystem.restrictExchanges]

example : ¬ (Domain.parallelAll D).admits
    [(⟨true, ()⟩, ⟨false, ()⟩)] ⟨true, ()⟩ := by
  intro hd
  have htag := hd.1 (⟨⟨true, ()⟩, ⟨false, ()⟩⟩) (by simp)
  cases htag

def zeroDomain : Domain Unit Unit where
  admits := fun _ _ => False
  bound := 0
  length_lt := by intro _ _ h; cases h

example : ¬ (Domain.parallelAll (fun _ : Bool => zeroDomain)).admits
    [(⟨true, ()⟩, ⟨true, ()⟩)] ⟨false, ()⟩ := by
  intro hd
  have hbound := hd.2.1 true (by simp)
  simp [RandomSystem.restrictExchanges, zeroDomain] at hbound

end Interleaved

example (D : ∀ b : Bool,
    Domain (if b then Bool else Unit) (if b then Unit else Bool)) :
    Domain (Σ b : Bool, if b then Bool else Unit)
      (Σ b : Bool, if b then Unit else Bool) :=
  Domain.parallelAll D

#print axioms SystemAlgebra.RandomSystem.parallelAll
#print axioms SystemAlgebra.RandomSystem.replies_parAll_iff

end
end SystemAlgebra.Tests
