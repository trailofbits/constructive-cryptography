import Probability.Distribution

/-!
# Independent finite products of heterogeneous laws

For a finite index type `K` and finitely supported laws `μ k : Distribution (A k)` on
carriers that may differ and may be infinite, the independent product is the law on
dependent functions `f : ∀ k, A k` given by

  `(piDep μ)(f) = ∏ k, μ k (f k)`.

A factor vanishes as soon as `f k ∉ supp (μ k)`, so the support lies in the finite box
`∏ k, supp (μ k)` (`Fintype.piFinset`) and the product is again finitely supported. The laws
are raw distributions: real-valued, neither nonnegative nor normalized in general. The index
and the carriers may live in different universes.

## Main definitions

* `Distribution.piDep μ`: the independent product of the family `μ`

## Main results

* `piDep_mass_forall`: for raw laws, a rectangular event has product mass,
  `(piDep μ).mass (fun f => ∀ k, Q k (f k)) = ∏ k, (μ k).mass (Q k)`
* `piDep_isProbDist`: a finite product of probability laws is a probability law
* `piDep_eq_pi`: with one carrier `A k = A`, `piDep μ` is the homogeneous product `pi μ`
* `fTransform_piDep`: coordinatewise pushforward commutes with the product,
  `(a ↦ (k ↦ f k (a k)))_* (piDep μ) = piDep (k ↦ (f k)_* (μ k))`
* `independent_product_piDep`: two product families regroup as one family of pairs,
  `piDep μ × piDep ν = unzip_* (piDep (k ↦ μ k × ν k))`, `unzip p = ((p k).1)_k, ((p k).2)_k`

The pushforward and regrouping laws take the carrier families `A` and `B` in independent
universes and hold for raw laws.
-/

namespace Probability.Distribution

variable {K : Type*} [Fintype K]

open Classical in
/-- The independent product of the finitely supported laws `μ k` on the carriers `A k`:
`(piDep μ)(f) = ∏ k, μ k (f k)` for `f : ∀ k, A k`. Its support lies in the finite box
`∏ k, supp (μ k)`, since a factor `μ k (f k)` vanishes off `supp (μ k)`. -/
noncomputable def piDep {A : K → Type*} (μ : ∀ k, Distribution (A k)) :
    Distribution (∀ k, A k) :=
  Finsupp.onFinset (Fintype.piFinset fun k => (μ k).support)
    (fun f => ∏ k, μ k (f k))
    (fun _f hf => Fintype.mem_piFinset.mpr fun k =>
      Finsupp.mem_support_iff.mpr fun h0 =>
        hf (Finset.prod_eq_zero (Finset.mem_univ k) h0))

/-- With one carrier `A k = A`, the dependent product is the homogeneous product:
`piDep μ = pi μ`, both being `f ↦ ∏ k, μ k (f k)` for `f : K → A`. -/
lemma piDep_eq_pi {A : Type*} [DecidableEq K] (μ : K → Distribution A) :
    piDep μ = pi μ := by
  -- Pointwise, both sides unfold to `∏ k, μ k (f k)`.
  ext f
  rfl

open Classical in
/-- A finite independent product of probability laws is a probability law: each mass
`∏ k, μ k (f k)` is nonnegative, and the total weight factors,
`∑_f ∏_k μ_k(f k) = ∏_k ∑_a μ_k(a) = ∏_k 1 = 1`. -/
lemma piDep_isProbDist {A : K → Type*} {μ : ∀ k, Distribution (A k)}
    (hμ : ∀ k, (μ k).isProbDist) : (piDep μ).isProbDist := by
  refine ⟨fun f => ?_, ?_⟩
  · -- Every component mass is nonnegative, so their product is nonnegative.
    rw [piDep, Finsupp.onFinset_apply]
    exact Finset.prod_nonneg fun k _ => (hμ k).1 (f k)
  · -- Sum the weight over the box `B = ∏ k, supp μ_k`, which contains the support.
    rw [weight_eq_finsupp_sum, Finsupp.sum_of_support_subset (piDep μ)
      (s := Fintype.piFinset fun k => (μ k).support)
      Finsupp.support_onFinset_subset _ (fun _ _ => rfl)]
    simp only [piDep, Finsupp.onFinset_apply]
    -- Exchange sum and product: `∑_{f ∈ B} ∏_k μ_k(f k) = ∏_k ∑_{a ∈ supp μ_k} μ_k(a)`.
    rw [← Finset.prod_univ_sum]
    -- Each factor is the weight of `μ k`, which is one.
    refine Finset.prod_eq_one fun k _ => ?_
    have hw := (hμ k).2
    rwa [weight_eq_finsupp_sum, Finsupp.sum] at hw

open Classical in
/-- A rectangular event `{f | ∀ k, Q k (f k)}` has the product of the coordinate masses:
`(piDep μ).mass (fun f => ∀ k, Q k (f k)) = ∏ k, (μ k).mass (Q k)`. Nonnegativity and
normalization are not assumed; the identity is finite-sum algebra over the support box. -/
theorem piDep_mass_forall {A : K → Type*} (μ : ∀ k, Distribution (A k)) (Q : ∀ k, A k → Prop) :
    (piDep μ).mass (fun f => ∀ k, Q k (f k)) = ∏ k, (μ k).mass (Q k) := by
  -- Write the mass as an indicator sum over the box `B = ∏ k, supp μ_k`:
  -- `∑_{f ∈ B} 1[∀ k, Q_k(f k)] · ∏_k μ_k(f k)`.
  rw [mass_eq_sum_of_support_subset (piDep μ) (s := Fintype.piFinset fun k => (μ k).support)
    Finsupp.support_onFinset_subset, Finset.sum_filter]
  -- The rectangle's indicator distributes over the product:
  -- `1[∀ k, Q_k(f k)] · ∏_k μ_k(f k) = ∏_k 1[Q_k(f k)] · μ_k(f k)`.
  have h1 : ∀ f : ∀ k, A k, (if ∀ k, Q k (f k) then piDep μ f else 0) =
      ∏ k, (if Q k (f k) then μ k (f k) else 0) := by
    intro f
    rw [Finset.prod_ite_zero]
    simp only [piDep, Finsupp.onFinset_apply, Finset.mem_univ, forall_const]
  simp only [h1]
  -- Exchange sum and product over the box:
  -- `∑_{f ∈ B} ∏_k 1[Q_k(f k)] μ_k(f k) = ∏_k ∑_{a ∈ supp μ_k} 1[Q_k(a)] μ_k(a)`.
  rw [← Finset.prod_univ_sum (fun k => (μ k).support) (fun k a => if Q k a then μ k a else 0)]
  -- Each factor is the indicator sum defining `(μ k).mass (Q k)`.
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mass_eq_sum_of_support_subset (μ k) (s := (μ k).support) subset_rfl, Finset.sum_filter]

open Classical in
/-- A coordinatewise pushforward commutes with the finite product:
`(a ↦ (k ↦ f k (a k)))_* (∏ k, μ k) = ∏ k, (f k)_* (μ k)`. The `μ k` are finitely supported
signed distributions; neither normalization nor nonnegativity is assumed. -/
lemma fTransform_piDep {A : K → Type*} {B : K → Type*} (μ : ∀ k, Distribution (A k))
    (f : ∀ k, A k → B k) :
    fTransform (fun a k => f k (a k)) (piDep μ) =
      piDep (fun k => fTransform (f k) (μ k)) := by
  -- At `g`: the left is the `piDep μ` mass of `{a | ∀ k, f k (a k) = g k}`, a rectangle, so
  -- it factors as `∏ k, μ k {a | f k a = g k} = ∏ k, (f k)_* (μ k) (g k)`.
  ext g
  rw [fTransform_apply_eq_mass]
  calc
    _ = (piDep μ).mass (fun a => ∀ k, f k (a k) = g k) :=
      mass_congr _ fun a => ⟨fun h k => congrFun h k, fun h => funext h⟩
    _ = ∏ k, (μ k).mass (fun a => f k a = g k) :=
      piDep_mass_forall μ (fun k a => f k a = g k)
    _ = _ := by simp only [piDep, Finsupp.onFinset_apply, fTransform_apply_eq_mass]

open Classical in
/-- Two product families regroup as one product family of pairs:
`(∏ k, μ k) × (∏ k, ν k) = (p ↦ ((p k).1)_k, ((p k).2)_k)_* (∏ k, μ k × ν k)`. Each sample
`a k`, `b k` occurs once on both sides. The laws are finitely supported signed distributions;
neither normalization nor nonnegativity is assumed. -/
lemma independent_product_piDep {A : K → Type*} {B : K → Type*}
    (μ : ∀ k, Distribution (A k)) (ν : ∀ k, Distribution (B k)) :
    prod (piDep μ) (piDep ν) =
      fTransform (fun f => ((fun k => (f k).1), (fun k => (f k).2)))
        (piDep fun k => prod (μ k) (ν k)) := by
  -- Unzipping `f ↦ ((f k).1)_k, ((f k).2)_k` is injective, so the pushforward at `(a, b)` is
  -- the mass at its unique preimage `k ↦ (a k, b k)`.
  have hinj : Function.Injective
      (fun f : ∀ k, A k × B k => ((fun k => (f k).1), (fun k => (f k).2))) := by
    intro f g he
    funext k
    exact Prod.ext (congrFun (congrArg Prod.fst he) k)
      (congrFun (congrArg Prod.snd he) k)
  ext p
  obtain ⟨a, b⟩ := p
  rw [fTransform_injective_apply _ _ hinj (fun k => (a k, b k)), prod_apply]
  -- `∏ k, μ k (a k) * ν k (b k) = (∏ k, μ k (a k)) * ∏ k, ν k (b k)`.
  simp only [piDep, Finsupp.onFinset_apply, prod_apply, Finset.prod_mul_distrib]

end Probability.Distribution
