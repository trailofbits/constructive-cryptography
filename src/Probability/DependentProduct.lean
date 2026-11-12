module

public import Probability.Distribution

/-!
# Independent finite products of heterogeneous laws

For a finite index type `K` and finitely supported laws `μ k : Distribution (A k)` on
carriers that may differ and may be infinite, the independent product is the law on
dependent functions `f : ∀ k, A k` given by

  `(piDep μ)(f) = ∏ k, μ k (f k)`.

A factor vanishes as soon as `f k ∉ supp (μ k)`, so the support lies in the finite box
`∏ k, supp (μ k)` (`Fintype.piFinset`) and the product is again finitely supported. The laws
may be raw real-valued distributions or normalized laws in `ProbDist`. The index
and the carriers may live in different universes.

## Main definitions

* `Distribution.piDep μ`: the independent product of the family `μ`
* `Distribution.ProbDist.piDep μ`: the same heterogeneous product with normalization included

## Main results

* `piDep_mass_forall`: for raw laws, a rectangular event has product mass,
  `(piDep μ).mass (fun f => ∀ k, Q k (f k)) = ∏ k, (μ k).mass (Q k)`
* `piDep_isProbDist`: a finite product of probability laws is a probability law
* `piDep_uniform`: independent uniform coordinates give a uniform dependent function
* `piDep_eq_pi`: with one carrier `A k = A`, `piDep μ` is the homogeneous product `pi μ`
* `fTransform_piDep`: coordinatewise pushforward commutes with the product,
  `(a ↦ (k ↦ f k (a k)))_* (piDep μ) = piDep (k ↦ (f k)_* (μ k))`
* `fTransform_pi_comp`: selecting distinct coordinates preserves their independent product law
* `piDep_single`: independent point laws give the point law on their tuple
* `piDep_fin_zero`, `piDep_fin_succ`: ordered tuples split into their first coordinate and tail
* `fTransform_piDep_piCongrLeft`: an explicit index equivalence transports the product law
* `independent_product_piDep`: two product families regroup as one family of pairs,
  `piDep μ × piDep ν = unzip_* (piDep (k ↦ μ k × ν k))`, `unzip p = ((p k).1)_k, ((p k).2)_k`

The pushforward and regrouping laws take the carrier families `A` and `B` in independent
universes and hold for raw laws.
-/

@[expose] public section

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

/-- The product mass at `f` is the product of its coordinate masses. -/
lemma piDep_apply {A : K → Type*} (μ : ∀ k, Distribution (A k)) (f : ∀ k, A k) :
    piDep μ f = ∏ k, μ k (f k) := rfl

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
    rw [piDep_apply]
    exact Finset.prod_nonneg fun k _ => (hμ k).1 (f k)
  · -- Sum the weight over the box `B = ∏ k, supp μ_k`, which contains the support.
    rw [weight_eq_finsupp_sum, Finsupp.sum_of_support_subset (piDep μ)
      (s := Fintype.piFinset fun k => (μ k).support)
      Finsupp.support_onFinset_subset _ (fun _ _ => rfl)]
    simp only [piDep_apply]
    -- Exchange sum and product: `∑_{f ∈ B} ∏_k μ_k(f k) = ∏_k ∑_{a ∈ supp μ_k} μ_k(a)`.
    rw [← Finset.prod_univ_sum]
    -- Each factor is the weight of `μ k`, which is one.
    refine Finset.prod_eq_one fun k _ => ?_
    have hw := (hμ k).2
    rwa [weight_eq_finsupp_sum, Finsupp.sum] at hw

/-- Independent samples of different types, with mass `∏ k, μ k (f k)` at outcome `f`.
The product carries its normalization proof. -/
noncomputable def ProbDist.piDep
    -- `K` indexes the independent draws; `A k` is the outcome type at coordinate `k`.
    {A : K → Type*}
    -- `μ k` supplies both the finite-support law and its normalization.
    (μ : ∀ k, ProbDist (A k)) : ProbDist (∀ k, A k) :=
  ⟨Distribution.piDep fun k => (μ k).1, piDep_isProbDist fun k => (μ k).2⟩

/-- `(ProbDist.piDep μ).1 = piDep (fun k => (μ k).1)`. -/
@[simp] lemma ProbDist.piDep_val {A : K → Type*} (μ : ∀ k, ProbDist (A k)) :
    (ProbDist.piDep μ).1 = Distribution.piDep (fun k => (μ k).1) := rfl

/-- Independent uniform coordinates give the uniform law on the whole dependent function. -/
lemma piDep_uniform
    -- Decidable equality on `K` fixes the finite enumeration of dependent functions.
    [DecidableEq K]
    -- `A k` is the finite nonempty outcome type at coordinate `k : K`.
    {A : K → Type*} [∀ k, Fintype (A k)] [∀ k, Nonempty (A k)] :
    piDep (fun k => uniform (A k)) = uniform (∀ k, A k) := by
  -- The mass is the reciprocal of the product of the coordinate cardinalities.
  ext f
  simp only [piDep_apply, uniform_apply, one_div,
    Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

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
    simp only [piDep_apply, Finset.mem_univ, forall_const]
  simp only [h1]
  -- Exchange sum and product over the box:
  -- `∑_{f ∈ B} ∏_k 1[Q_k(f k)] μ_k(f k) = ∏_k ∑_{a ∈ supp μ_k} 1[Q_k(a)] μ_k(a)`.
  rw [← Finset.prod_univ_sum (fun k => (μ k).support) (fun k a => if Q k a then μ k a else 0)]
  -- Each factor is the indicator sum defining `(μ k).mass (Q k)`.
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mass_eq_sum_of_support_subset (μ k) (s := (μ k).support) subset_rfl, Finset.sum_filter]

/-- Selecting distinct coordinates from independent weight-one laws preserves their product law. -/
lemma fTransform_pi_comp
    -- `I` indexes the original table and `J` its selected coordinates; `Ω` carries outcomes.
    {I J Ω : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    -- `μ i` is the finitely supported signed law at coordinate `i`, with total weight one.
    (μ : I → Distribution Ω) (hμ : ∀ i, (μ i).weight = 1)
    -- `e` selects each coordinate at most once, so distinct draws remain independent.
    (e : J → I) (he : Function.Injective e) :
    fTransform (fun f j => f (e j)) (pi μ) = pi (fun j => μ (e j)) := by
  classical
  ext f
  let Q : I → Ω → Prop := fun i a => ∀ j, e j = i → a = f j
  -- Selected coordinates fix one value; all other coordinates impose no condition.
  have selected (j : J) : (μ (e j)).mass (Q (e j)) = μ (e j) (f j) := by
    calc
      _ = (μ (e j)).mass (fun a => a = f j) := mass_congr _ fun a =>
        ⟨fun ha => ha j rfl, fun ha j' hj => (he hj).symm ▸ ha⟩
      _ = _ := mass_singleton _ _
  have discarded (i : I) (hi : i ∉ Finset.univ.image e) : (μ i).mass (Q i) = 1 := by
    calc
      _ = (μ i).mass (fun _ => True) := mass_congr _ fun _ =>
        iff_true_intro (fun j hj => (hi (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩)).elim)
      _ = 1 := (mass_true _).trans (hμ i)
  rw [fTransform_apply_eq_mass]
  calc
    _ = (piDep μ).mass (fun a => ∀ i, Q i (a i)) := by
      rw [piDep_eq_pi]
      apply mass_congr
      intro a
      exact ⟨fun ha i j hj => hj ▸ congrFun ha j, fun ha => funext fun j => ha (e j) j rfl⟩
    _ = ∏ i, (μ i).mass (Q i) := piDep_mass_forall μ Q
    -- Removing unit factors leaves exactly the injective image of the selected indices.
    _ = ∏ i ∈ Finset.univ.image e, (μ i).mass (Q i) :=
      (Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => discarded i hi)).symm
    _ = ∏ j, μ (e j) (f j) := by
      rw [Finset.prod_image he.injOn]
      exact Finset.prod_congr rfl fun j _ => selected j
    _ = _ := (pi_apply _ _).symm

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
    _ = _ := by simp only [piDep_apply, fTransform_apply_eq_mass]

/-- Independent point laws give the point law on their tuple. -/
lemma piDep_single
    -- `f k` is the fixed outcome at coordinate `k` of the family `A`.
    {A : K → Type*} (f : ∀ k, A k) :
    piDep (fun k => Finsupp.single (f k) 1) = Finsupp.single f 1 := by
  classical
  apply Finsupp.ext
  intro g
  by_cases hg : g = f
  · subst g
    simp only [piDep_apply, Finsupp.single_eq_same, Finset.prod_const_one]
  · -- A different tuple differs at one coordinate, whose point mass is zero.
    obtain ⟨k, hk⟩ : ∃ k, f k ≠ g k := by
      by_contra hn
      push Not at hn
      exact hg (funext fun k => (hn k).symm)
    rw [Finsupp.single_eq_of_ne hg]
    change (∏ k, (Finsupp.single (f k) 1) (g k)) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ k) (Finsupp.single_eq_of_ne hk.symm)

/-- The empty product is the point law on the unique empty tuple. -/
lemma piDep_fin_zero
    -- `A` is an empty family of outcome types; `μ` has no coordinates to sample.
    {A : Fin 0 → Type*} (μ : ∀ i, Distribution (A i)) :
    piDep μ = Finsupp.single (fun i => Fin.elim0 i) 1 := by
  -- With no coordinates, the supplied family is also the family of empty-tuple point laws.
  have hμ : μ = fun i => Finsupp.single (Fin.elim0 i) 1 := by
    funext i
    exact Fin.elim0 i
  rw [hμ, piDep_single]

/-- An ordered product samples its first coordinate and its remaining tuple independently. -/
lemma piDep_fin_succ
    -- `A i` is the outcome type at position `i`; `μ i` is its finitely supported law.
    {n : ℕ} {A : Fin (n + 1) → Type*} (μ : ∀ i, Distribution (A i)) :
    piDep μ = fTransform
      (fun p : A 0 × ((i : Fin n) → A i.succ) => Fin.cons p.1 p.2)
      (prod (μ 0) (piDep fun i : Fin n => μ i.succ)) := by
  classical
  -- Prepending the first outcome is a bijection onto complete tuples.
  have hinj : Function.Injective
      (fun p : A 0 × ((i : Fin n) → A i.succ) => Fin.cons p.1 p.2) := by
    intro p q h
    exact Prod.ext (congrFun h 0) (funext fun i => congrFun h i.succ)
  ext f
  have he : Fin.cons (f 0) (fun i : Fin n => f i.succ) = f := Fin.cons_self_tail f
  conv_rhs => rw [← he]
  rw [fTransform_injective_apply _ _ hinj (f 0, fun i : Fin n => f i.succ), prod_apply]
  -- The tuple mass factors into coordinate zero and the product over its tail.
  change (∏ i, μ i (f i)) = μ 0 (f 0) * ∏ i : Fin n, μ i.succ (f i.succ)
  exact Fin.prod_univ_succ _

/-- Reindexing an independent tuple along an explicit equivalence preserves its product law. -/
lemma fTransform_piDep_piCongrLeft
    -- `e` identifies the chosen finite index order `L` with the original family index `K`.
    {L : Type*} [Fintype L] (e : L ≃ K)
    -- `A k` carries coordinate `k`; `μ k` is its finitely supported law.
    {A : K → Type*} (μ : ∀ k, Distribution (A k)) :
    fTransform (Equiv.piCongrLeft A e) (piDep fun i => μ (e i)) = piDep μ := by
  classical
  ext f
  -- The reindexing equivalence has exactly one preimage of each complete tuple.
  have he := (Equiv.piCongrLeft A e).apply_symm_apply f
  conv_lhs => rw [← he]
  rw [fTransform_injective_apply _ _ (Equiv.piCongrLeft A e).injective]
  simp only [piDep_apply, Equiv.piCongrLeft_symm_apply]
  exact e.prod_comp (fun k => μ k (f k))

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
  simp only [piDep_apply, prod_apply, Finset.prod_mul_distrib]

end Probability.Distribution
