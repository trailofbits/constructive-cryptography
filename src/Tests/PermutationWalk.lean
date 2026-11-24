module

public import Probability.Permutation.Walk

/-!
# Tests for adaptive permutation walks, public-table replay, and reply-event bounds

* Likelihood domination (`permutation_constraints_mass_ge_independent`).
* Adaptive causal walk exact probability (`permutation_walk_mass`).
* Exact fresh-label mass and lower bound (`uniform_fresh_labels_mass`, `fresh_labels_factor_ge`).
* Conditional forward and inverse reply-event upper bounds (`permutation_reply_event_mass_le`).
* Public-table good-replay lower bound (`permutation_replay_public_good_lower_bound`).
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.PermutationWalk

open Probability Probability.Counting

/-- The permutation likelihood dominates the independent-value likelihood. -/
example (x y : Bool ↪ Fin 4) :
    (1 / (4 : ℝ)) ^ 2 ≤
      (Distribution.uniform (Equiv.Perm (Fin 4))).mass (fun π => ∀ j, π (x j) = y j) := by
  simpa only [Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat] using
    permutation_constraints_mass_ge_independent x y

/-- Exact mass of injective pairs in `Fin 4` avoiding `{0}` is `3 * 2 / 4^2 = 3 / 8`. -/
example :
    (Distribution.uniform (Bool → Fin 4)).mass
      (fun values => Function.Injective values ∧ ∀ j, values j ∉ ({0} : Finset (Fin 4))) =
        (3 : ℝ) / 8 := by
  have h := uniform_fresh_labels_mass (J := Bool) ({0} : Finset (Fin 4))
  refine Eq.trans ?_ (by norm_num [Fintype.card_fin, Fintype.card_bool, Nat.descFactorial] :
    ((Fintype.card (Fin 4) - ({0} : Finset (Fin 4)).card).descFactorial (Fintype.card Bool) : ℝ) /
      (Fintype.card (Fin 4) : ℝ) ^ Fintype.card Bool = (3 : ℝ) / 8)
  convert h

/-- The fresh-label factor satisfies the collision-plus-forbidden lower bound. -/
example (forbidden : Finset (Fin 8)) :
    1 - (((2 : Nat).choose 2 : ℝ) + 2 * forbidden.card) / 8 ≤
      (((8 - forbidden.card).descFactorial 2 : ℝ) / (8 : ℝ) ^ 2) := by
  simpa only [Fintype.card_fin, Fintype.card_bool, Nat.cast_ofNat] using
    fresh_labels_factor_ge (J := Bool) forbidden

/-- A fresh forward reply on `Fin 4` with one recorded point hits `bad` with factor `4 / 3`. -/
example (bad : Fin 4 → Prop) :
    (Distribution.uniform (Equiv.Perm (Fin 4))).mass
      (fun π => (∀ z ∈ ({0} : Finset (Fin 4)), π z = Equiv.refl (Fin 4) z) ∧ bad (π 1)) ≤
      (4 / (4 - 1 : ℝ)) * (Distribution.uniform (Fin 4)).mass bad *
        (Distribution.uniform (Equiv.Perm (Fin 4))).mass
          (fun π => ∀ z ∈ ({0} : Finset (Fin 4)), π z = Equiv.refl (Fin 4) z) := by
  have h := permutation_reply_event_mass_le (Equiv.refl (Fin 4)) ({0} : Finset (Fin 4))
    bad false 1 (by simp only [Bool.false_eq_true, ↓reduceIte, Finset.mem_singleton,
      Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true])
  simpa only [Bool.false_eq_true, ↓reduceIte, Fintype.card_fin, Finset.card_singleton,
    Nat.cast_ofNat, Nat.cast_one] using h

/-- A fresh inverse reply on `Fin 4` with one recorded point hits `bad` with factor `4 / 3`. -/
example (bad : Fin 4 → Prop) :
    (Distribution.uniform (Equiv.Perm (Fin 4))).mass
      (fun π => (∀ z ∈ ({0} : Finset (Fin 4)), π z = Equiv.refl (Fin 4) z) ∧
        bad ((π.symm) 1)) ≤
      (4 / (4 - 1 : ℝ)) * (Distribution.uniform (Fin 4)).mass bad *
        (Distribution.uniform (Equiv.Perm (Fin 4))).mass
          (fun π => ∀ z ∈ ({0} : Finset (Fin 4)), π z = Equiv.refl (Fin 4) z) := by
  have h := permutation_reply_event_mass_le (Equiv.refl (Fin 4)) ({0} : Finset (Fin 4))
    bad true 1 (by simp only [↓reduceIte, Finset.image_singleton, Equiv.refl_apply,
      Finset.mem_singleton, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, not_false_eq_true])
  simpa only [↓reduceIte, Fintype.card_fin, Finset.card_singleton,
    Nat.cast_ofNat, Nat.cast_one] using h

/-- A two-step adaptive walk `0 ↦ 1 ↦ 2` on `Fin 4` has exact probability `1 / 12`. -/
example :
    (Distribution.uniform (Equiv.Perm (Fin 4))).mass
      (fun π => π 0 = 1 ∧ π (π 0) = 2) = 1 / (12 : ℝ) := by
  let parent : Bool → Option Bool := fun b => if b then some false else none
  let step : Bool → Fin 4 → Fin 4 := fun _ x => x
  let rank : Bool → Nat := fun b => if b then 1 else 0
  let inputs : (Fin 4 → Fin 4) → Bool → Fin 4 := fun f b => if b then f 0 else 0
  let values : Bool ↪ Fin 4 := ⟨fun b => if b then 2 else 1, by
    intro a b h
    cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    · exact absurd (congrArg Fin.val h) (by change (1 : Nat) ≠ 2; omega)
    · exact absurd (congrArg Fin.val h) (by change (2 : Nat) ≠ 1; omega)⟩
  have hwalk := permutation_walk_mass parent step (0 : Fin 4) rank
    (by
      intro j k hjk
      cases j with
      | false => cases hjk
      | true =>
        simp only [parent, ↓reduceIte, Option.some.injEq] at hjk
        subst k
        simp only [rank, Bool.false_eq_true, ↓reduceIte]
        omega)
    inputs
    (by intro f j; cases j <;> rfl)
    values
    (by
      intro a b h
      cases a <;> cases b <;>
        simp only [Counting.walkSite, parent, step, values, Option.elim, Bool.false_eq_true,
          ↓reduceIte] at h ⊢
      · exact absurd (congrArg Fin.val h) (by change (0 : Nat) ≠ 1; omega)
      · exact absurd (congrArg Fin.val h) (by change (1 : Nat) ≠ 0; omega))
  have hcongr :
      (Distribution.uniform (Equiv.Perm (Fin 4))).mass (fun π => π 0 = 1 ∧ π (π 0) = 2) =
        (Distribution.uniform (Equiv.Perm (Fin 4))).mass
          (fun π => ∀ j, π (inputs π j) = values j) := by
    apply Distribution.mass_congr
    intro π
    constructor
    · rintro ⟨h0, h1⟩ j
      cases j
      · exact h0
      · exact h1
    · intro h
      exact ⟨h false, h true⟩
  rw [hcongr, hwalk]
  norm_num [Fintype.card_fin, Fintype.card_bool, Nat.descFactorial]

/-- Public-table good-replay lower bound on `Fin 4` with one replayed site (`0`) and one fixed
public entry (`1 ↦ 2`). -/
example (Event : (Unit → Fin 4) → Prop) :
    (Distribution.uniform (Unit → Fin 4)).mass (fun v => v () ≠ 2 ∧ Event v) *
        (1 / (4 : ℝ)) ≤
      (Distribution.uniform (Equiv.Perm (Fin 4))).mass
        (fun π => π 0 ≠ 2 ∧ Event (fun _ => π 0) ∧ π 1 = 2) := by
  have h := permutation_replay_public_good_lower_bound
    (S := Fin 4) (I := Unit) (J := Unit)
    (fun _ _ => (0 : Fin 4)) (fun π _ => π 0)
    (by
      intro π v
      constructor
      · intro hv _
        exact congrFun hv ()
      · intro hv
        funext u
        exact hv u)
    (fun _ => (1 : Fin 4)) (fun _ => (2 : Fin 4))
    (fun v => v () ≠ 2) Event
    (by
      intro _ _ a b hab
      cases a <;> cases b <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab ⊢
      · exact absurd (congrArg Fin.val hab) (by change (0 : Nat) ≠ 1; omega)
      · exact absurd (congrArg Fin.val hab) (by change (1 : Nat) ≠ 0; omega))
    (by
      intro v hv a b hab
      cases a <;> cases b <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab ⊢
      · exact absurd hab hv
      · exact absurd hab.symm hv)
    (by simp only [Fintype.card_unit, Fintype.card_fin]; omega)
  have hcongr :
      (Distribution.uniform (Equiv.Perm (Fin 4))).mass
          (fun π => π 0 ≠ 2 ∧ Event (fun _ => π 0) ∧ π 1 = 2) =
        (Distribution.uniform (Equiv.Perm (Fin 4))).mass
          (fun π => (fun v => v () ≠ 2) (fun _ => π 0) ∧ Event (fun _ => π 0) ∧
            ∀ _ : Unit, π 1 = 2) := by
    apply Distribution.mass_congr
    intro π
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun _ => h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3 ()⟩⟩
  rw [hcongr]
  simp only [Fintype.card_fin, Fintype.card_unit, Nat.descFactorial_one, Nat.cast_ofNat] at h
  convert h

#print axioms permutation_constraints_mass_ge_independent
#print axioms permutation_walk_mass
#print axioms uniform_fresh_labels_mass
#print axioms fresh_labels_factor_ge_of_budget
#print axioms permutation_replay_public_mass
#print axioms permutation_replay_public_good_lower_bound
#print axioms permutation_reply_event_mass_le

end Tests.PermutationWalk
