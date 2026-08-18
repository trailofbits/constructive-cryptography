/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Algebra.Group.Submonoid.Membership
import AbstractCryptography.Specification.Outbound

/-!
# Interface-indexed attachment (MR16 §3.1, §7 · LiuZhang Ch. 3)

Attachment at interface `i` is a map `e i : SigmaI → Sigma` into the one
converter monoid.  The axiom the instantiation owes is
`PairwiseOrderInvariant`: attachments at distinct interfaces commute in
their action (LiuZhang fn. 1, Jost Prop 2.2.3), stated on the action and
never in the monoid.

`attachedWithin e Z` is the submonoid of converters attached within the
interface set `Z` — MR16 §7's grouping: a protocol is a product of
attachments at its parties' interfaces.  `orderInvariant_attachedWithin`:
disjoint interface sets are order-invariant as groups, so the honest and
dishonest sides of any corruption split form the attachment pair the
blocking relaxations (`Specification.Outbound`) consume.
-/

namespace AbstractCryptography

variable {ι SigmaI Sigma Φ : Type*} [Monoid Sigma] [MulAction Sigma Φ]

namespace ActCommute

variable {a b : Sigma}

theorem one_left : ActCommute Φ (1 : Sigma) b := fun R => by
  rw [one_smul, one_smul]

theorem mul_left {a₁ a₂ : Sigma} (h₁ : ActCommute Φ a₁ b) (h₂ : ActCommute Φ a₂ b) :
    ActCommute Φ (a₁ * a₂) b := fun R => by
  rw [mul_smul, h₂ R, h₁ (a₂ • R), mul_smul]

theorem mul_right {b₁ b₂ : Sigma} (h₁ : ActCommute Φ a b₁) (h₂ : ActCommute Φ a b₂) :
    ActCommute Φ a (b₁ * b₂) :=
  (h₁.symm.mul_left h₂.symm).symm

/-- Order invariance extends from generators to the generated submonoids. -/
theorem closure_closure {s t : Set Sigma}
    (h : ∀ x ∈ s, ∀ y ∈ t, ActCommute Φ x y) {a b : Sigma}
    (ha : a ∈ Submonoid.closure s) (hb : b ∈ Submonoid.closure t) :
    ActCommute Φ a b := by
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
      induction hb using Submonoid.closure_induction with
      | mem y hy => exact h x hx y hy
      | one => exact ActCommute.one_left.symm
      | mul y₁ y₂ _ _ ih₁ ih₂ => exact ActCommute.mul_right ih₁ ih₂
  | one => exact ActCommute.one_left
  | mul x₁ x₂ _ _ ih₁ ih₂ => exact ActCommute.mul_left ih₁ ih₂

end ActCommute

/-- LiuZhang fn. 1 / Jost Prop 2.2.3: attachments at distinct interfaces
commute in their action — the axiom the instantiation must prove. -/
def PairwiseOrderInvariant (Φ : Type*)
    (e : ι → SigmaI → Sigma) [MulAction Sigma Φ] : Prop :=
  ∀ ⦃i j : ι⦄, i ≠ j → ∀ α β, ActCommute Φ (e i α) (e j β)

variable (e : ι → SigmaI → Sigma)

/-- MR16 §7's grouping: the converters attached within the interface set
`Z` — products of attachments at interfaces of `Z`. -/
def attachedWithin (Z : Set ι) : Submonoid Sigma :=
  Submonoid.closure (⋃ i ∈ Z, Set.range (e i))

theorem mem_attachedWithin_of_attach {i : ι} {Z : Set ι} (hi : i ∈ Z) (α : SigmaI) :
    e i α ∈ attachedWithin e Z :=
  Submonoid.subset_closure (Set.mem_biUnion hi ⟨α, rfl⟩)

/-- Disjoint interface sets are order-invariant as groups. -/
theorem actCommute_of_disjoint (hp : PairwiseOrderInvariant Φ e)
    {Z₁ Z₂ : Set ι} (hZ : Disjoint Z₁ Z₂) {a b : Sigma}
    (ha : a ∈ attachedWithin e Z₁) (hb : b ∈ attachedWithin e Z₂) :
    ActCommute Φ a b := by
  refine ActCommute.closure_closure ?_ ha hb
  rintro x hx y hy
  simp only [Set.mem_iUnion] at hx hy
  obtain ⟨i, hi, α, rfl⟩ := hx
  obtain ⟨j, hj, β, rfl⟩ := hy
  exact hp (hZ.ne_of_mem hi hj) α β

/-- The honest and dishonest sides of a corruption split form the attachment
pair the blocking relaxations consume. -/
theorem orderInvariant_attachedWithin (hp : PairwiseOrderInvariant Φ e)
    {Z₁ Z₂ : Set ι} (hZ : Disjoint Z₁ Z₂) :
    OrderInvariant Φ (attachedWithin e Z₁).subtype (attachedWithin e Z₂).subtype :=
  fun a b R => actCommute_of_disjoint e hp hZ a.2 b.2 R

end AbstractCryptography
