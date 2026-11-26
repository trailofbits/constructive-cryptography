module

public import Probability.Kernel

/-!
# Independent products with prescribed coordinates

`pinnedProduct μ pin` keeps the independent law `μ k` at an unpinned coordinate and replaces
it by `δ_a` when `pin k = some a`. The coordinate types may differ and may be infinite.

`pinnedProduct_eq_bindK_update` samples one coordinate first and pins that value in the
remaining product. `pinnedProduct_apply_eq_of_pin` identifies its supported value.
Together they give `fTransform_pinnedProduct_apply`: the joint law of a table and one
entry equals sampling the entry and then completing the table with that entry prescribed.
The raw identities hold for signed laws; `ProbDist.pinnedProduct` retains normalization.
-/

@[expose] public section

namespace Probability.Distribution

-- `K` is the finite coordinate set; `A k` carries the outcome at coordinate `k`.
variable {K : Type*} [Fintype K] {A : K → Type*}

open Classical in
/-- The product with law `μ k` when `pin k = none` and point law `δ_a` when `pin k = some a`.
Prescribing a value replaces its factor, including when that value has zero original mass. -/
noncomputable def pinnedProduct
    -- `μ k` is the finite signed law of coordinate `k`; `pin k` optionally prescribes its value.
    (μ : ∀ k, Distribution (A k)) (pin : ∀ k, Option (A k)) : Distribution (∀ k, A k) :=
  piDep fun k => (pin k).elim (μ k) (fun a => Finsupp.single a 1)

/-- With no prescribed coordinates, the law is the original independent product. -/
lemma pinnedProduct_none (μ : ∀ k, Distribution (A k)) :
    pinnedProduct μ (fun _ => none) = piDep μ := rfl

/-- Prescribing `a` at `k` replaces exactly that factor of the product by `δ_a`. -/
lemma pinnedProduct_update [DecidableEq K]
    (μ : ∀ k, Distribution (A k)) (pin : ∀ k, Option (A k)) (k : K) (a : A k) :
    pinnedProduct μ (Function.update pin k (some a)) =
      piDep (Function.update
        (fun j => (pin j).elim (μ j) (fun b => Finsupp.single b 1)) k (Finsupp.single a 1)) := by
  classical
  unfold pinnedProduct
  congr 1
  funext j
  by_cases same : j = k
  · subst j
    simp only [Function.update_self, Option.elim_some]
  · simp only [Function.update_of_ne same]

/-- Every supported table takes the prescribed value at a pinned coordinate. -/
lemma pinnedProduct_apply_eq_of_pin
    (μ : ∀ k, Distribution (A k)) (pin : ∀ k, Option (A k))
    -- `fixed` prescribes value `a` at `k`; `supported` makes `f` a possible completed table.
    (k : K) (a : A k) (fixed : pin k = some a)
    {f : ∀ k, A k} (supported : f ∈ (pinnedProduct μ pin).support) : f k = a := by
  classical
  let factors := fun j => (pin j).elim (μ j) (fun b => Finsupp.single b 1)
  have unchanged : Function.update factors k (Finsupp.single a 1) = factors := by
    have value : factors k = Finsupp.single a 1 := by
      simp only [factors, fixed, Option.elim_some]
    rw [← value, Function.update_eq_self]
  apply eq_of_mem_support_piDep_update factors k a
  simpa only [unchanged, factors, pinnedProduct] using supported

/-- Sample coordinate `k` first, then complete the product with its sampled value prescribed. -/
lemma pinnedProduct_eq_bindK_update [DecidableEq K]
    (μ : ∀ k, Distribution (A k)) (pin : ∀ k, Option (A k)) (k : K) :
    pinnedProduct μ pin =
      bindK ((pin k).elim (μ k) (fun a => Finsupp.single a 1))
        (fun a => pinnedProduct μ (Function.update pin k (some a))) := by
  classical
  change piDep (fun j => (pin j).elim (μ j) (fun a => Finsupp.single a 1)) = _
  rw [piDep_eq_bindK_update _ k]
  apply bindK_congr
  intro a _
  exact (pinnedProduct_update μ pin k a).symm

/-- The joint table/entry law equals sampling the entry and completing its pinned table. -/
theorem fTransform_pinnedProduct_apply [DecidableEq K]
    (μ : ∀ k, Distribution (A k)) (pin : ∀ k, Option (A k))
    -- `k` selects the entry retained beside the whole sampled table.
    (k : K) :
    fTransform (fun f => (f, f k)) (pinnedProduct μ pin) =
      bindK ((pin k).elim (μ k) (fun a => Finsupp.single a 1)) (fun a =>
        fTransform (fun f => (f, a)) (pinnedProduct μ (Function.update pin k (some a)))) := by
  classical
  conv_lhs => rw [pinnedProduct_eq_bindK_update μ pin k, fTransform_bindK]
  apply bindK_congr
  intro a _
  apply fTransform_congr_support
  intro f supported
  -- The conditional product fixes the observed entry to the value sampled first.
  rw [pinnedProduct_apply_eq_of_pin μ _ k a (Function.update_self ..) supported]

namespace ProbDist

/-- Independent normalized coordinates with prescribed values replacing their factors. -/
noncomputable def pinnedProduct
    -- `μ k` is normalized; `pin k` optionally prescribes the value of coordinate `k`.
    (μ : ∀ k, ProbDist (A k)) (pin : ∀ k, Option (A k)) : ProbDist (∀ k, A k) :=
  piDep fun k => (pin k).elim (μ k) single

/-- The normalized pinned product has the corresponding raw signed-law product. -/
@[simp] lemma pinnedProduct_val
    (μ : ∀ k, ProbDist (A k)) (pin : ∀ k, Option (A k)) :
    (pinnedProduct μ pin).1 = Distribution.pinnedProduct (fun k => (μ k).1) pin := by
  apply congrArg Distribution.piDep
  funext k
  change ((pin k).elim (μ k) single).1 =
    (pin k).elim (μ k).1 (fun a => Finsupp.single a 1)
  cases pin k <;> rfl

/-- With no prescribed values, the normalized law is `ProbDist.piDep μ`. -/
lemma pinnedProduct_none (μ : ∀ k, ProbDist (A k)) :
    pinnedProduct μ (fun _ => none) = piDep μ := rfl

end ProbDist

end Probability.Distribution
