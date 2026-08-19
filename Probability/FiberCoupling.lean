/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Distribution

/-!
# The fiber coupling

Two finite-support laws `left right : Distribution A` that push forward to the **same**
law along a map `r : A → D` can always be joined: there is a law
`joint : Distribution (A × A)` carried by the fiber relation `r x = r y` whose two
marginals are `left` and `right`.  The witness is the fiberwise product

    joint (x, y) := left x * right y / (fTransform r left) (r x)   if `r x = r y`,

and `0` otherwise — the two laws made independent *conditionally on the shared
projection*.  This is the finite-support, `ℝ≥0`-valued case of the measure
gluing lemma.  The only delicate point is a fiber of measure zero, where the
definition divides by `0`; in `NNReal` that returns `0`, which is the right
answer, because such a fiber carries no mass on either side
(`apply_le_fTransform_apply`).

`exists_coupling_of_fTransform_eq` is the packaged statement, and it is what
lifts a *pointwise* gluing construction to laws over the carrier: whenever a
deterministic argument builds from `x` and `y` with `r x = r y` a single object
`glue x y` that looks like `x` through one projection and like `y` through
another, pushing `joint` forward along `fun p => glue p.1 p.2` inherits both
marginals, because `fTransform` only sees the map on the support
(`fTransform_congr`).

The section also records the three general `Distribution` facts the construction needs
and the file did not have: `mass_eq_sum_support`,
`fTransform_apply_eq_sum_support` (support-sum forms, with the decidability of
the event an explicit binder as `DESIGN.md` §4 requires) and
`apply_le_fTransform_apply` (a point never outweighs its fiber).
-/

namespace Probability

namespace Distribution

universe ua ub ud

variable {A : Type ua} {B : Type ub} {D : Type ud}

/-! ## General support-sum evaluation -/

/-- Event mass as a sum over the support.  The decidability of the event is an
explicit binder, so the statement's `if` instantiates with the caller's ambient
instance. -/
theorem mass_eq_sum_support (X : Distribution A) (P : A → Prop) [DecidablePred P] :
    X.mass P = ∑ a ∈ X.support, if P a then X a else 0 := by
  classical
  unfold mass Finsupp.sum
  exact Finset.sum_congr rfl fun a _ => by by_cases hit : P a <;> simp [hit]

/-- Pointwise evaluation of a pushforward as a sum over the source support. -/
theorem fTransform_apply_eq_sum_support (f : A → B) (X : Distribution A) (b : B)
    [DecidablePred fun a : A => f a = b] :
    fTransform f X b = ∑ a ∈ X.support, if f a = b then X a else 0 := by
  rw [fTransform_apply_eq_mass, mass_eq_sum_support]

/-- **A point never outweighs its fiber** (for a non-negative law — over the
signed carrier a fiber can cancel below one of its points).  This is what
makes the division in the coupling harmless: the divisor vanishes only on
fibers that are null on both sides. -/
theorem apply_le_fTransform_apply (f : A → B) {X : Distribution A} (hX : X.NonNeg)
    (a : A) : X a ≤ fTransform f X (f a) := by
  classical
  rw [fTransform_apply_eq_sum_support]
  by_cases member : a ∈ X.support
  · have bound := Finset.single_le_sum (f := fun x => if f x = f a then X x else 0)
      (fun i _ => by by_cases hit : f i = f a <;> simp [hit, hX i]) member
    simpa using bound
  · rw [Finsupp.notMem_support_iff.1 member]
    exact Finset.sum_nonneg fun i _ => by
      by_cases hit : f i = f a <;> simp [hit, hX i]

/-! ## The fiberwise product coupling -/

section Coupling

variable [DecidableEq D]

/-- **The fiberwise product coupling.**  `left` and `right` are made independent
conditionally on their common projection along `r`; the normalizing divisor is
the mass of the fiber. -/
noncomputable def fiberCoupling (r : A → D) (left right : Distribution A) : Distribution (A × A) :=
  Finsupp.onFinset (left.support ×ˢ right.support)
    (fun pair =>
      if r pair.1 = r pair.2 then left pair.1 * right pair.2 / fTransform r left (r pair.1)
      else 0)
    (fun pair nonzero => by
      have leftNonzero : left pair.1 ≠ 0 := fun zero => nonzero (by simp [zero])
      have rightNonzero : right pair.2 ≠ 0 := fun zero => nonzero (by simp [zero])
      exact Finset.mem_product.2
        ⟨Finsupp.mem_support_iff.2 leftNonzero, Finsupp.mem_support_iff.2 rightNonzero⟩)

@[simp] theorem fiberCoupling_apply (r : A → D) (left right : Distribution A) (pair : A × A) :
    fiberCoupling r left right pair =
      if r pair.1 = r pair.2 then left pair.1 * right pair.2 / fTransform r left (r pair.1)
      else 0 :=
  Finsupp.onFinset_apply

/-- **The coupling is carried by the fiber relation.** -/
theorem eq_of_mem_support_fiberCoupling {r : A → D} {left right : Distribution A} {pair : A × A}
    (member : pair ∈ (fiberCoupling r left right).support) : r pair.1 = r pair.2 := by
  by_contra different
  exact Finsupp.mem_support_iff.1 member (by simp [different])

/-- The fiberwise product of non-negative laws is non-negative — the
property the signed gluing witness below cannot offer. -/
theorem fiberCoupling_nonNeg (r : A → D) {left right : Distribution A}
    (hleft : left.NonNeg) (hright : right.NonNeg) :
    (fiberCoupling r left right).NonNeg := by
  intro pair
  rw [fiberCoupling_apply]
  by_cases hit : r pair.1 = r pair.2
  · rw [if_pos hit]
    exact div_nonneg (mul_nonneg (hleft _) (hright _)) ((hleft.fTransform r) _)
  · rw [if_neg hit]

/-- Event mass of the coupling, as a sum over the product of the two supports —
the form both marginal computations start from. -/
theorem mass_fiberCoupling (r : A → D) (left right : Distribution A) (P : A × A → Prop)
    [DecidablePred P] :
    (fiberCoupling r left right).mass P =
      ∑ pair ∈ left.support ×ˢ right.support,
        if P pair then
          (if r pair.1 = r pair.2 then left pair.1 * right pair.2 / fTransform r left (r pair.1)
           else 0)
        else 0 := by
  classical
  unfold mass fiberCoupling
  rw [Finsupp.onFinset_sum _ (fun _ => by simp)]
  exact Finset.sum_congr rfl fun pair _ => by by_cases hit : P pair <;> simp [hit]

/-- **The first marginal of the coupling is `left`.** -/
theorem fTransform_fst_fiberCoupling (r : A → D) {left : Distribution A}
    (hleft : left.NonNeg) (right : Distribution A)
    (project : fTransform r left = fTransform r right) :
    fTransform (Prod.fst : A × A → A) (fiberCoupling r left right) = left := by
  classical
  ext point
  rw [fTransform_apply_eq_mass, mass_fiberCoupling, Finset.sum_product]
  have collapse : ∀ x ∈ left.support,
      (∑ y ∈ right.support,
        if (x, y).1 = point then
          (if r (x, y).1 = r (x, y).2 then left (x, y).1 * right (x, y).2 /
            fTransform r left (r (x, y).1) else 0)
        else 0) =
      if x = point then
        ∑ y ∈ right.support,
          (if r x = r y then left x * right y / fTransform r left (r x) else 0)
      else 0 := by
    intro x _
    by_cases hit : x = point <;> simp [hit]
  rw [Finset.sum_congr rfl collapse, Finset.sum_ite_eq' left.support point]
  by_cases member : point ∈ left.support
  · rw [if_pos member]
    have nonzero : left point ≠ 0 := Finsupp.mem_support_iff.1 member
    have fiberPos : fTransform r left (r point) ≠ 0 := fun zero =>
      nonzero (le_antisymm (zero ▸ apply_le_fTransform_apply r hleft point)
        (hleft point))
    have factor : ∀ y : A,
        (if r point = r y then left point * right y / fTransform r left (r point) else 0) =
          left point / fTransform r left (r point) * (if r y = r point then right y else 0) := by
      intro y
      by_cases hit : r y = r point
      · rw [if_pos hit.symm, if_pos hit, mul_div_right_comm]
      · rw [if_neg fun same => hit same.symm, if_neg hit, mul_zero]
    rw [Finset.sum_congr rfl (fun y _ => factor y), ← Finset.mul_sum,
      ← mass_eq_sum_support, ← fTransform_apply_eq_mass, ← project,
      div_mul_cancel₀ _ fiberPos]
  · rw [if_neg member, Finsupp.notMem_support_iff.1 member]

/-- **The second marginal of the coupling is `right`.** -/
theorem fTransform_snd_fiberCoupling (r : A → D) (left : Distribution A)
    {right : Distribution A} (hright : right.NonNeg)
    (project : fTransform r left = fTransform r right) :
    fTransform (Prod.snd : A × A → A) (fiberCoupling r left right) = right := by
  classical
  ext point
  rw [fTransform_apply_eq_mass, mass_fiberCoupling, Finset.sum_product]
  have collapse : ∀ x ∈ left.support,
      (∑ y ∈ right.support,
        if (x, y).2 = point then
          (if r (x, y).1 = r (x, y).2 then left (x, y).1 * right (x, y).2 /
            fTransform r left (r (x, y).1) else 0)
        else 0) =
      if point ∈ right.support then
        (if r x = r point then left x * right point / fTransform r left (r x) else 0)
      else 0 := by
    intro x _
    exact Finset.sum_ite_eq' right.support point
      (fun y => if r x = r y then left x * right y / fTransform r left (r x) else 0)
  rw [Finset.sum_congr rfl collapse]
  by_cases member : point ∈ right.support
  · simp only [if_pos member]
    have nonzero : right point ≠ 0 := Finsupp.mem_support_iff.1 member
    have fiberPos : fTransform r left (r point) ≠ 0 := fun zero =>
      nonzero (le_antisymm
        ((project ▸ zero) ▸ apply_le_fTransform_apply r hright point)
        (hright point))
    have factor : ∀ x : A,
        (if r x = r point then left x * right point / fTransform r left (r x) else 0) =
          right point / fTransform r left (r point) * (if r x = r point then left x else 0) := by
      intro x
      by_cases hit : r x = r point
      · rw [if_pos hit, if_pos hit, hit, mul_comm (left x) (right point), mul_div_right_comm]
      · rw [if_neg hit, if_neg hit, mul_zero]
    rw [Finset.sum_congr rfl (fun x _ => factor x), ← Finset.mul_sum,
      ← mass_eq_sum_support, ← fTransform_apply_eq_mass, div_mul_cancel₀ _ fiberPos]
  · rw [Finsupp.notMem_support_iff.1 member]
    simp [member]

end Coupling

/-- **Gluing two non-negative laws, with a non-negative witness**: the
fiberwise product coupling.  Use this form whenever the joint must stay an
honest (sub-)probability object; the fully general signed statement is
`exists_coupling_of_fTransform_eq` below, whose correction-term witness is
genuinely signed.  The decidability of `D` is not part of either statement:
the witnesses are built classically. -/
theorem exists_nonneg_coupling_of_fTransform_eq (r : A → D)
    {left right : Distribution A} (hleft : left.NonNeg) (hright : right.NonNeg)
    (project : fTransform r left = fTransform r right) :
    ∃ joint : Distribution (A × A), joint.NonNeg ∧
      (∀ pair ∈ joint.support, r pair.1 = r pair.2) ∧
      fTransform Prod.fst joint = left ∧ fTransform Prod.snd joint = right := by
  classical
  exact ⟨fiberCoupling r left right, fiberCoupling_nonNeg r hleft hright,
    fun _ member => eq_of_mem_support_fiberCoupling member,
    fTransform_fst_fiberCoupling r hleft right project,
    fTransform_snd_fiberCoupling r left hright project⟩

/-- **Gluing two laws along a common projection** — fully general over the
signed carrier.  Laws with the same pushforward along `r` admit a joint law
carried by the fiber relation of `r` whose marginals are the two given
laws; no non-negativity is assumed (and none is offered on the witness). -/
theorem exists_coupling_of_fTransform_eq (r : A → D) (left right : Distribution A)
    (project : fTransform r left = fTransform r right) :
    ∃ joint : Distribution (A × A), (∀ pair ∈ joint.support, r pair.1 = r pair.2) ∧
      fTransform Prod.fst joint = left ∧ fTransform Prod.snd joint = right := by
  classical
  -- Over the SIGNED carrier the fiberwise product above is unusable (a
  -- cancelling fiber zeroes the divisor while still carrying nonzero
  -- points), but gluing itself needs no non-negativity: transport each side
  -- onto a chosen representative of its fiber and correct once.  With
  -- `rep := Function.invFun r`,
  --
  --   joint := (x ↦ (x, rep (r x)))⋆left + (y ↦ (rep (r y), y))⋆right
  --              − (x ↦ (rep (r x), rep (r x)))⋆left
  --
  -- the two correction terms cancel through `project`, giving marginals
  -- `left` and `right` exactly; every support pair lies on the fiber
  -- relation because `r (rep (r a)) = r a` on inhabited fibers.
  cases isEmpty_or_nonempty A with
  | inl empty =>
      refine ⟨0, by simp, ?_, ?_⟩ <;>
        · ext a
          exact (empty.false a).elim
  | inr nonempty =>
      set rep : D → A := Function.invFun r with hrep
      have rep_section : ∀ a : A, r (rep (r a)) = r a := fun a =>
        Function.invFun_eq ⟨a, rfl⟩
      set joint : Distribution (A × A) :=
        fTransform (fun x => (x, rep (r x))) left
          + fTransform (fun y => (rep (r y), y)) right
          - fTransform (fun x => (rep (r x), rep (r x))) left with hjoint
      have mapDomain_sub : ∀ (g : A × A → A) (P Q : Distribution (A × A)),
          Finsupp.mapDomain g (P - Q) =
            Finsupp.mapDomain g P - Finsupp.mapDomain g Q := fun g P Q =>
        map_sub (Finsupp.mapDomain.addMonoidHom (M := ℝ) g) P Q
      have marginal : ∀ g : A × A → A,
          fTransform g joint =
            fTransform g (fTransform (fun x => (x, rep (r x))) left)
              + fTransform g (fTransform (fun y => (rep (r y), y)) right)
              - fTransform g (fTransform (fun x => (rep (r x), rep (r x))) left) := by
        intro g
        rw [hjoint]
        show Finsupp.mapDomain g _ = _
        rw [mapDomain_sub, Finsupp.mapDomain_add]
        rfl
      have correction :
          fTransform (fun a => rep (r a)) right =
            fTransform (fun a => rep (r a)) left := by
        show fTransform (rep ∘ r) right = fTransform (rep ∘ r) left
        rw [← fTransform_comp, ← fTransform_comp, project]
      refine ⟨joint, ?_, ?_, ?_⟩
      · intro pair member
        rcases Finset.mem_union.1 (Finsupp.support_sub member) with h12 | h3
        · rcases Finset.mem_union.1 (Finsupp.support_add h12) with h1 | h2
          · obtain ⟨a, -, rfl⟩ := mem_support_fTransform _ _ h1
            exact (rep_section a).symm
          · obtain ⟨a, -, rfl⟩ := mem_support_fTransform _ _ h2
            exact rep_section a
        · obtain ⟨a, -, rfl⟩ := mem_support_fTransform _ _ h3
          rfl
      · rw [marginal Prod.fst, fTransform_comp, fTransform_comp, fTransform_comp]
        have base : fTransform (Prod.fst ∘ fun x => (x, rep (r x))) left = left :=
          fTransform_id left
        rw [base]
        have swap : fTransform (Prod.fst ∘ fun y => (rep (r y), y)) right =
            fTransform (Prod.fst ∘ fun x => (rep (r x), rep (r x))) left :=
          correction
        rw [swap, add_sub_cancel_right]
      · rw [marginal Prod.snd, fTransform_comp, fTransform_comp, fTransform_comp]
        have base : fTransform (Prod.snd ∘ fun y => (rep (r y), y)) right = right :=
          fTransform_id right
        rw [base]
        have swap : fTransform (Prod.snd ∘ fun x => (x, rep (r x))) left =
            fTransform (Prod.snd ∘ fun x => (rep (r x), rep (r x))) left := rfl
        rw [swap, add_sub_cancel_left]

end Distribution

end Probability
