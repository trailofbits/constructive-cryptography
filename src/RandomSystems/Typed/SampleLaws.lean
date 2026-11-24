module

public import RandomSystems.Typed.SamplingAlgebra

/-!
# Additional laws for retained samples

* `sample_const`: a retained draw ignored by the system leaves the system unchanged.
* `sample_uniform_equiv`: a bijection `e : K ≃ L` reparametrizes a uniform initial sample
  without changing the typed system.
-/

@[expose] public section

set_option autoImplicit false

namespace SystemAlgebra.TypedSystem

open Probability
open scoped SystemAlgebra

/-- An ignored draw is invisible: drawing `k ← P` and retaining the same system `R` for
every `k` equals `R`. At every transcript `h`, `∑_k P(k) · R(h) = R(h)` since `∑_k P(k) = 1`. -/
lemma sample_const {A : Interface} {K : Type}
    (P : Distribution K) [Distribution.IsProbability P] (R : TypedSystem A) :
    (sample _k ← P; R) = R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  have weight : ∑ k ∈ P.support, P k = 1 := Distribution.IsProbability.weight_eq_one
  rw [sample_mass, ← Finset.sum_mul, weight, one_mul]

open Classical in
/-- A bijection `e : K ≃ L` changes the presentation of a uniform initial sample without changing
its law. -/
lemma sample_uniform_equiv {A : Interface} {K L : Type}
    [Fintype K] [Nonempty K] [Fintype L] [Nonempty L]
    (e : K ≃ L) (R : L → TypedSystem A) :
    (sample l ←$ 𝒰[L]; R l) = (sample k ←$ 𝒰[K]; R (e k)) := by
  change TypedSystem.sample (Distribution.uniform L) R =
    TypedSystem.sample (Distribution.uniform K) (fun k => R (e k))
  have h := sample_fTransform e (Distribution.uniform K) R
  simpa only [Distribution.fTransform_equiv_uniform] using h

end SystemAlgebra.TypedSystem
