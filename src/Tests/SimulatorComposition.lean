module

public import ConstructiveCryptography.CryptographicAlgebra.SimulatorComposition
public import ConstructiveCryptography.Instances.Algebra
public import RandomSystems.Typed.Context

/-!
# Simulator images with query budgets

A deterministic converter with a certificate of `a` inside calls per outside query can be
followed by one with a certificate of `b` calls. Their serial presentation has bound `b * a`.
The discard converter certifies the zero-cost case on the outside port.
-/

@[expose] public section

namespace Tests.SimulatorComposition

open CategoryTheory MonoidalCategory ConstructiveCryptography SystemAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification

/-- Simulators with some deterministic presentation certified for `q` inside calls per query. -/
def simulators (P Q : Interface) (q : ℕ) : Set (P ⟶ Q) :=
  {σ | ∃ rule : InsideOutsideSystem P.I Q.I P.X P.Y Q.X Q.Y,
    ∃ cert : IsDDCFrom Q.domain P.domain q rule, σ = TypedConverter.ofDDC rule cert}

/-- Serial composition uses the existing product bound for the two deterministic presentations. -/
lemma comp_mem {P Q R : Interface} {a b : ℕ} {σ : P ⟶ Q} {τ : Q ⟶ R}
    (outer : σ ∈ simulators P Q a) (inner : τ ∈ simulators Q R b) :
    σ ≫ τ ∈ simulators P R (b * a) := by
  obtain ⟨s, hs, rfl⟩ := outer
  obtain ⟨t, ht, rfl⟩ := inner
  exact ⟨_, hs.comp ht, (TypedConverter.ofDDC_eq_comp hs ht (hs.comp ht) rfl).symm⟩

/-- The simulator witnesses change the right port from `R` to `Q` and then to `P`. -/
example {H P Q R : Interface} (a b : ℕ) (S : Specification (TypedSystem (H ⊗ R))) :
    simulatorImage (simulators P Q a) (simulatorImage (simulators Q R b) S) ⊆
      simulatorImage (simulators P R (b * a)) S :=
  simulatorImage_comp_subset (fun _ hσ _ hτ => comp_mem hσ hτ) S

/-- Discard followed by the one-call unitor has bound `1 * 0 = 0`. The three right
ports in this example are the empty interface, `unit ⊗ R`, and `R`. -/
example {H R : Interface} (S : Specification (TypedSystem (H ⊗ R))) :
    simulatorImage ({TypedConverter.discard (Interface.unit ⊗ R)} :
        Set (Interface.unit ⟶ Interface.unit ⊗ R))
      (simulatorImage {(λ_ R).hom} S) ⊆ simulatorImage (simulators Interface.unit R 0) S := by
  apply simulatorImage_comp_subset
  intro σ outer τ inner
  obtain rfl := Set.mem_singleton_iff.mp outer
  obtain rfl := Set.mem_singleton_iff.mp inner
  -- Discard never calls inside, while the unitor forwards each call exactly once.
  have zero : TypedConverter.discard (Interface.unit ⊗ R) ∈
      simulators Interface.unit (Interface.unit ⊗ R) 0 :=
    ⟨_, discardSystem_isDDCFrom _, rfl⟩
  have one : (λ_ R).hom ∈ simulators (Interface.unit ⊗ R) R 1 := by
    obtain ⟨rule, cert, same, _⟩ := TypedConverter.exists_rename_eq_ofDDC
      (A := Interface.unit ⊗ R) (B := R) _ _ _ (Interface.leftUnitAlphabet_fst R.X)
      (Interface.leftUnitAlphabet_fst R.Y) (Interface.parallelDomain_unit_left R)
    exact ⟨rule, cert, same⟩
  exact comp_mem zero one

end Tests.SimulatorComposition
