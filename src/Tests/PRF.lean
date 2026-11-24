module

public import Commons.Definitions.PRF
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Tests for keyed PRF specifications

Exercises `KeyedPRF` using CC's custom notation (`≃[...]`, `•`, `∥`, `sample k ←$ 𝒰[K]`),
reduction-relaxation membership, converter transport (`KeyedPRF.of_converter`), tactic
interoperability (`cc_normalize`, `cc_calc mixed`), and standard-axiom checks.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.PRF

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra Probability Commons
open scoped SystemAlgebra SystemAlgebra.DSL

-- Every typed distinguisher is admitted, locally to this test module.
local instance allTests : AdmissibleDistinguishers Interface TypedDistinguisher :=
  AdmissibleDistinguishers.all

variable {K X Y : Type} [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]

/-- A PRF's keyed system lies in `KeyedPRF.specification` and its reduction relaxation. -/
example {q : ℕ} (F : K → X → Y) {error : TypedDistinguisher (Evaluation X Y q) → ENNReal}
    (h : KeyedPRF F error) :
    KeyedPRF.real F q ∈ Specification.reductionRelaxation (Distinguishers.distinguisherAdvantage
      (Phi := TypedSystem) AdmissibleDistinguishers.admissible) error {URF (Evaluation X Y q)} :=
  KeyedPRF.specification_subset_reductionRelaxation error (KeyedPRF.real_mem_specification h)

/-- Transporting a PRF bound through the identity converter preserves the error. -/
example {q : ℕ} (F : K → X → Y) {error : TypedDistinguisher (Evaluation X Y q) → ENNReal}
    (h : KeyedPRF F error) :
    KeyedPRF F (fun d => error (TypedDistinguisher.absorb d (𝟙 (Evaluation X Y q)))) :=
  KeyedPRF.of_converter (𝟙 (Evaluation X Y q)) F F (fun _ _ => Set.mem_univ _)
    (TypedConverter.identity_attach _) (TypedConverter.identity_attach _) h

/-- `cc_normalize` distributes a converter across parallel composition and pushes it inside the
retained uniform key sample of `KeyedPRF.real`. -/
example {A B : Interface} {q : ℕ} (α : A ⟶ Evaluation X Y q) (F : K → X → Y)
    (aux : TypedSystem B) :
    (α ⊗ₘ 𝟙 B) • (KeyedPRF.real F q ∥ aux) =
      (sample k ←$ 𝒰[K]; α • (system [Evaluation X Y q] _ x => F k x)) ∥ aux := by
  dsimp only [KeyedPRF.real]
  cc_normalize

/-- `cc_calc mixed` chains a `KeyedPRF` substitution step (`≃[...]`) with a statistical distance
step (`≈[...]`) without leaving open goals. -/
example {q : ℕ} (F : K → X → Y) {S : TypedSystem (Evaluation X Y q)}
    {error : TypedDistinguisher (Evaluation X Y q) → ENNReal} {δ : ENNReal}
    (h : KeyedPRF F error) (hstat : Δ (URF (Evaluation X Y q)) S ≤ δ) :
    KeyedPRF.real F q ≃[fun d => error d + δ] S := by
  cc_calc mixed
    KeyedPRF.real F q ≃[error] URF (Evaluation X Y q) := h
    _ ≈[δ] S := hstat

#print axioms KeyedPRF.real_mem_specification
#print axioms KeyedPRF.specification_subset_reductionRelaxation
#print axioms KeyedPRF.of_converter

end Tests.PRF
