module

public import Commons.Definitions.Hash.Keyed
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Tests for retained-key hash presentations and one-query collision lifting

Exercises:
* Retained-key presentations `Hash.Real.eq_sample` and `Hash.Ideal.eq_sample` using CC's
  `sample k ←$ 𝒰[K]` notation.
* Key-independent domain extension `G k = H k ∘ f` via `Hash.extractConverter (Prod.map f f) q`,
  `Hash.CR.of_extractor`, and `Hash.CR.advantage_eq_of_extractor`.
* Tactic interoperability: `cc_normalize` with `Hash.extractConverter` under parallel composition
  and retained sampling, and `cc_calc mixed` chaining a lifted `Hash.CR` (`≃[...]`) step with a
  statistical (`≈[...]`) step.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.HashExtractor

open CategoryTheory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra Probability Commons
open scoped SystemAlgebra SystemAlgebra.DSL

-- Every typed distinguisher is admitted, locally to this test module.
local instance allTests : AdmissibleDistinguishers Interface TypedDistinguisher :=
  AdmissibleDistinguishers.all

variable {K M M' T : Type} [Fintype K] [Nonempty K] [Fintype M] [Fintype M']
  [DecidableEq M] [DecidableEq M'] [DecidableEq T]

/-- Domain extension preserves collision resistance with error `d ↦ error (dα)`. -/
lemma domainExtension_CR (H : K → M → T) (f : M' → M) (hf : Function.Injective f) {q : ℕ}
    {error : TypedDistinguisher (KeyedCollision K M q) → ENNReal} (h : Hash.CR H error) :
    Hash.CR (fun k m => H k (f m))
      (fun d => error (TypedDistinguisher.absorb d (Hash.extractConverter (Prod.map f f) q))) :=
  Hash.CR.of_extractor H _ (Prod.map f f) (fun _ _ => Iff.rfl)
    (fun _ => hf.eq_iff) (fun _ _ => Set.mem_univ _) h

/-- Lossless advantage transport for every outer distinguisher. -/
example (H : K → M → T) (f : M' → M) (hf : Function.Injective f) {q : ℕ}
    (d : TypedDistinguisher (KeyedCollision K M' q)) :
    d.advantage (Hash.Real (budget := q) (fun k m => H k (f m)))
        (Hash.Ideal K M' (budget := q)) =
      (TypedDistinguisher.absorb d (Hash.extractConverter (Prod.map f f) q)).advantage
        (Hash.Real (budget := q) H) (Hash.Ideal K M (budget := q)) :=
  Hash.CR.advantage_eq_of_extractor H _ (Prod.map f f) (fun _ _ => Iff.rfl) (fun _ => hf.eq_iff) d

/-- `cc_normalize` distributes `Hash.extractConverter` across parallel composition and pushes it
inside the retained-key sample `sample k ←$ 𝒰[K]`. -/
example {B : Interface} (H : K → M → T) (f : M' → M) (q : ℕ) (aux : TypedSystem B) :
    (Hash.extractConverter (K := K) (Prod.map f f) q ⊗ₘ 𝟙 B) •
        (Hash.Real (budget := q) H ∥ aux) =
      (sample k ←$ 𝒰[K];
        Hash.extractConverter (K := K) (Prod.map f f) q •
          TypedSystem.ofFunction (A := KeyedCollision K M q) (Hash.reply H k)) ∥ aux := by
  rw [Hash.Real.eq_sample]
  cc_normalize

/-- `cc_calc mixed` chains a lifted `Hash.CR` substitution step (`≃[...]`) with a statistical
distance step (`≈[...]`) without leaving open goals. -/
example (H : K → M → T) (f : M' → M) (hf : Function.Injective f) {q : ℕ}
    {error : TypedDistinguisher (KeyedCollision K M q) → ENNReal} {δ : ENNReal}
    {S : TypedSystem (KeyedCollision K M' q)}
    (h : Hash.CR H error)
    (hstat : Δ (Hash.Ideal K M' (budget := q)) S ≤ δ) :
    Hash.Real (budget := q) (fun k m => H k (f m)) ≃[fun d =>
      error (TypedDistinguisher.absorb d (Hash.extractConverter (Prod.map f f) q)) + δ] S := by
  cc_calc mixed
    Hash.Real (budget := q) (fun k m => H k (f m))
      ≃[fun d => error (TypedDistinguisher.absorb d (Hash.extractConverter (Prod.map f f) q))]
      Hash.Ideal K M' (budget := q) := domainExtension_CR H f hf h
    _ ≈[δ] S := hstat

#print axioms TypedSystem.source_eq_ofProbAutomaton
#print axioms Hash.Real.eq_sample
#print axioms Hash.Ideal.eq_sample
#print axioms Hash.extractConverter_smul_real
#print axioms Hash.extractConverter_smul_ideal
#print axioms Hash.CR.of_extractor
#print axioms Hash.CR.advantage_eq_of_extractor

end Tests.HashExtractor
