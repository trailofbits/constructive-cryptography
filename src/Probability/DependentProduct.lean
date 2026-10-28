import Probability.Distribution

/-!
# Independent finite products of heterogeneous laws

`Distribution.piDep` assigns mass `∏ k, μ k (f k)` to a dependent family of outcomes.
The index type is finite; each coordinate law has finite support, while its carrier may be
infinite. This is the probability law needed by finite parallel stochastic converters.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” Independence is an explicit choice for this product law, rather
than a consequence of disjoint interfaces.

## Main results

* `piDep_isProbDist`: normalization of products of probability laws
* `piDep_mass_forall`: componentwise events have product mass
-/

namespace Probability.Distribution

variable {K : Type} [Fintype K] [DecidableEq K]

open Classical in
/-- The independent product of finitely many finitely supported laws on different types,
`(⨂ₖ μₖ)(f) = ∏ₖ μₖ(f k)`; `Distribution.pi` is the homogeneous case. Jost, Thesis,
printed p. 17, describes a finite set of disjoint-interface resources as one resource;
this distribution makes the independence specialization explicit. -/
noncomputable def piDep {A : K → Type} (μ : ∀ k, Distribution (A k)) :
    Distribution (∀ k, A k) :=
  Finsupp.onFinset (Fintype.piFinset fun k => (μ k).support)
    (fun f => ∏ k, μ k (f k))
    (fun _f hf => Fintype.mem_piFinset.mpr fun k =>
      Finsupp.mem_support_iff.mpr fun h0 =>
        hf (Finset.prod_eq_zero (Finset.mem_univ k) h0))

open Classical in
/-- A finite independent product of probability laws is normalized. -/
lemma piDep_isProbDist {A : K → Type} {μ : ∀ k, Distribution (A k)}
    (hμ : ∀ k, (μ k).isProbDist) : (piDep μ).isProbDist := by
  refine ⟨fun f => ?_, ?_⟩
  · -- Every component mass is nonnegative, so their product is nonnegative.
    rw [piDep, Finsupp.onFinset_apply]
    exact Finset.prod_nonneg fun k _ => (hμ k).1 (f k)
  · -- The total product mass factors into the product of coordinate weights.
    rw [weight_eq_finsupp_sum, Finsupp.sum_of_support_subset (piDep μ)
      (s := Fintype.piFinset fun k => (μ k).support)
      Finsupp.support_onFinset_subset _ (fun _ _ => rfl)]
    simp only [piDep, Finsupp.onFinset_apply]
    rw [← Finset.prod_univ_sum]
    refine Finset.prod_eq_one fun k _ => ?_
    have hw := (hμ k).2
    rwa [weight_eq_finsupp_sum, Finsupp.sum] at hw

open Classical in
/-- A componentwise event under the independent product has the product of its component
probabilities. -/
lemma piDep_mass_forall {A : K → Type} (μ : ∀ k, Distribution (A k)) (Q : ∀ k, A k → Prop) :
    (piDep μ).mass (fun f => ∀ k, Q k (f k)) = ∏ k, (μ k).mass (Q k) := by
  -- Restrict to the finite product support and factor the event indicator.
  rw [mass_eq_sum_of_support_subset (piDep μ) (s := Fintype.piFinset fun k => (μ k).support)
    Finsupp.support_onFinset_subset, Finset.sum_filter]
  have h1 : ∀ f : ∀ k, A k, (if ∀ k, Q k (f k) then piDep μ f else 0) =
      ∏ k, (if Q k (f k) then μ k (f k) else 0) := by
    intro f
    rw [Finset.prod_ite_zero]
    simp [piDep, Finsupp.onFinset_apply]
  simp only [h1]
  -- Factor the finite sum and read each coordinate sum as its event mass.
  rw [← Finset.prod_univ_sum (fun k => (μ k).support) (fun k a => if Q k a then μ k a else 0)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mass_eq_sum_of_support_subset (μ k) (s := (μ k).support) subset_rfl, Finset.sum_filter]

end Probability.Distribution
