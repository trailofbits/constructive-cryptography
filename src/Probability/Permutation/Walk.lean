module

public import Probability.Permutation.Replay

/-!
# Adaptive permutation walks, public-table replay, and reply-event bounds

Extends `Probability.Permutation` and `Probability.Permutation.Replay` with higher-level
without-replacement counting laws for adaptive transcripts and public permutation tables:

* `permutation_reply_constraint`, `permutation_constraints_mass_ge_independent`: orienting
  forward/inverse queries and dominating the independent-value likelihood `(1 / |S|)^{|J|}`.
* `permutation_walk_mass`: adaptive causal walks with distinct sites retain the exact
  falling-factorial probability `1 / (|S|)_{|J|}`.
* `uniform_fresh_labels_mass`, `fresh_labels_factor_ge`, `fresh_labels_factor_ge_of_budget`:
  exact mass and numerical lower bounds for injective labels avoiding a forbidden set.
* `permutation_replay_public_mass`, `permutation_replay_public_good_factor`,
  `permutation_replay_public_good_lower_bound`: adaptive replay jointly with a fixed public
  table, without switching to a random function.
* `permutation_forward_reply_mass_le`, `permutation_inverse_reply_mass_le`,
  `permutation_reply_set_mass_le`, `permutation_reply_event_mass_le`: conditional upper bounds
  for fresh forward or inverse replies hitting a fixed set or event.
* `permutation_avoid_mass_ge` and `permutation_avoid_mass_ge_of_card_le`: fresh replies avoid
  their forbidden sets with summed or common-cardinality loss; repeated requests are allowed.

## References

1. G. Bertoni, J. Daemen, M. Peeters and G. Van Assche. On the Indifferentiability of the
   Sponge Construction. EUROCRYPT 2008, LNCS 4965, pp. 181–197.
-/

@[expose] public section

set_option autoImplicit false

namespace Probability.Counting

open scoped BigOperators

noncomputable section

universe u v

/-! ### Orientation, likelihood comparison, and adaptive walks -/

section Walk

-- `S` is the finite permuted set; `J` indexes the distinct constrained points.
variable {S : Type u} {J : Type v} [Fintype S] [Fintype J] [DecidableEq S]

/-- A forward query `π x = y` and an inverse query `π⁻¹ x = y` impose the same oriented edge. -/
lemma permutation_reply_constraint {S : Type u} (π : Equiv.Perm S) (inverse : Bool) (x y : S) :
    (if inverse then π.symm x else π x) = y ↔
      π (if inverse then y else x) = (if inverse then x else y) := by
  cases inverse
  · rfl
  · change π.symm x = y ↔ π y = x
    rw [π.symm_apply_eq]
    exact eq_comm

/-- On every injective labeling, the permutation likelihood is at least the likelihood
`(1 / |S|)^{|J|}` of independent uniform values. A likelihood-ratio fact, not a switching bound. -/
lemma permutation_constraints_mass_ge_independent (x y : J ↪ S) :
    (1 / (Fintype.card S : ℝ)) ^ Fintype.card J ≤
      (Distribution.uniform (Equiv.Perm S)).mass (fun π => ∀ j, π (x j) = y j) := by
  rw [permutation_constraints_mass, div_pow, one_pow]
  have hm : Fintype.card J ≤ Fintype.card S := Fintype.card_le_of_injective x x.injective
  have hp : 0 < ((Fintype.card S).descFactorial (Fintype.card J) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hm
  have hle : ((Fintype.card S).descFactorial (Fintype.card J) : ℝ) ≤
      (Fintype.card S : ℝ) ^ Fintype.card J := by
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card S) (Fintype.card J)
  exact one_div_le_one_div_of_le hp hle

/-- **Adaptive causal walks**: if each input `inputs π j` is a step `step j` applied to the
root or to the image of its parent, and the walk sites of a target labeling `values` are
distinct, then the walk reaches `values` with the falling-factorial probability [1, Lemma 5]. -/
theorem permutation_walk_mass
    -- `parent j` is the earlier site feeding site `j` (`none` for the root), ranked by `rank`.
    (parent : J → Option J) (step : J → S → S) (root : S) (rank : J → Nat)
    (hrank : ∀ j k, parent j = some k → rank k < rank j)
    -- `inputs f j` is the input queried at site `j` when the oracle is `f`.
    (inputs : (S → S) → J → S)
    (hinputs : ∀ f j, inputs f j = step j
      ((parent j).elim root (fun k => f (inputs f k))))
    -- `values` is the prescribed injective labeling; `hfresh`: its walk sites are distinct.
    (values : J ↪ S)
    (hfresh : Function.Injective (Counting.walkSite parent step root values)) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => ∀ j, π (inputs π j) = values j) =
        1 / ((Fintype.card S).descFactorial (Fintype.card J) : ℝ) := by
  rw [← permutation_constraints_mass
    (⟨Counting.walkSite parent step root values, hfresh⟩ : J ↪ S) values]
  apply Distribution.mass_congr
  intro π
  change (∀ j, π (inputs π j) = values j) ↔
    (∀ j, π (Counting.walkSite parent step root values j) = values j)
  constructor
  · -- Reaching `values` forces the inputs to be the walk sites of `values`.
    intro h
    have he : inputs π = Counting.walkSite parent step root values := by
      rw [Counting.walkSite_of_eval parent step root inputs hinputs π]
      exact congrArg (Counting.walkSite parent step root) (funext h)
    simpa only [← he] using h
  · -- Conversely the walk sites determine the inputs by rank induction.
    intro h
    have he := Counting.eq_walkSite_of_eval_eq parent step root rank hrank inputs hinputs h
    simpa only [he] using h

end Walk

/-! ### Fresh labels -/

open Classical in
/-- Exact fraction of label tuples `J → S` that are injective and avoid a forbidden set:
`((|S| - |forbidden|)_{|J|}) / |S|^{|J|}`. -/
theorem uniform_fresh_labels_mass {S : Type u} {J : Type v} [Fintype S] [Fintype J]
    [Nonempty S] (forbidden : Finset S) :
    (Distribution.uniform (J → S)).mass
      (fun values => Function.Injective values ∧ ∀ j, values j ∉ forbidden) =
        (((Fintype.card S - forbidden.card).descFactorial (Fintype.card J) : ℝ) /
          (Fintype.card S : ℝ) ^ Fintype.card J) := by
  classical
  -- Good tuples are exactly embeddings into the complement of `forbidden`.
  let e : {values : J → S // Function.Injective values ∧ ∀ j, values j ∉ forbidden} ≃
      (J ↪ {x : S // x ∉ forbidden}) := {
    toFun := fun values =>
      ⟨fun j => ⟨values.val j, values.property.2 j⟩,
        fun _ _ he => values.property.1 (congrArg Subtype.val he)⟩
    invFun := fun labels =>
      ⟨fun j => (labels j).val,
        ⟨fun _ _ he => labels.injective (Subtype.ext he), fun j => (labels j).property⟩⟩
    left_inv := fun _ => by apply Subtype.ext; rfl
    right_inv := fun _ => by ext j; rfl }
  have hcard : Fintype.card {x : S // x ∉ forbidden} = Fintype.card S - forbidden.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have hc := Fintype.card_congr e
  rw [Fintype.card_embedding_eq, hcard] at hc
  rw [Distribution.uniform_mass_eq_card_filter, ← Fintype.card_subtype, hc,
    Fintype.card_fun, Nat.cast_pow]

open Classical in
/-- The exact fresh-label factor loses at most the collision count `C(|J|, 2)` and the
forbidden-hit count `|J| · |forbidden|`, each divided by `|S|`. -/
lemma fresh_labels_factor_ge {J : Type u} {S : Type v} [Fintype J] [Fintype S] [Nonempty S]
    (forbidden : Finset S) :
    1 - (((Fintype.card J).choose 2 : ℝ) + Fintype.card J * forbidden.card) /
        Fintype.card S ≤
      (((Fintype.card S - forbidden.card).descFactorial (Fintype.card J) : ℝ) /
        (Fintype.card S : ℝ) ^ Fintype.card J) := by
  classical
  let good (values : J → S) := Function.Injective values ∧ ∀ j, values j ∉ forbidden
  -- A bad tuple either collides or hits the forbidden set.
  have hcover (values : J → S) (hg : ¬ good values) :
      ¬ Set.InjOn values (Finset.univ : Finset J) ∨
        ∃ j ∈ (Finset.univ : Finset J), ∃ c ∈ forbidden, values j = c := by
    by_cases hi : Function.Injective values
    · right
      by_contra! hn
      exact hg ⟨hi, fun j hm => hn j (Finset.mem_univ _) (values j) hm rfl⟩
    · left
      intro he
      exact hi (fun _ _ hh => he (Finset.mem_univ _) (Finset.mem_univ _) hh)
  -- Union bound for forbidden hits, one coordinate and one value at a time.
  have hh : (Distribution.uniform (J → S)).mass
      (fun values => ∃ j ∈ (Finset.univ : Finset J), ∃ c ∈ forbidden, values j = c) ≤
        (Fintype.card J : ℝ) * forbidden.card / Fintype.card S := by
    refine (Distribution.mass_exists_le Distribution.uniform_nonNeg Finset.univ _).trans ?_
    calc
      _ ≤ ∑ _j : J, ∑ _c ∈ forbidden, 1 / (Fintype.card S : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        refine (Distribution.mass_exists_le Distribution.uniform_nonNeg forbidden _).trans ?_
        apply Finset.sum_le_sum
        intro c _
        exact Counting.uniform_mass_coord_determined_le j id Function.injective_id
          (fun _ => c) (fun _ _ _ => rfl)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hb := (Distribution.mass_mono Distribution.uniform_nonNeg hcover).trans
    ((Distribution.mass_or_le Distribution.uniform_nonNeg _ _).trans
      (add_le_add (Counting.uniform_mass_not_injOn_le_choose
        (Y := S) (Finset.univ : Finset J)) hh))
  simp only [Finset.card_univ] at hb
  have hc := Distribution.mass_add_compl (Distribution.uniform (J → S)) good
  rw [Distribution.weight_uniform] at hc
  have hf : (Distribution.uniform (J → S)).mass good =
      (((Fintype.card S - forbidden.card).descFactorial (Fintype.card J) : ℝ) /
        (Fintype.card S : ℝ) ^ Fintype.card J) := uniform_fresh_labels_mass forbidden
  rw [← hf, add_div]
  linarith

open Classical in
/-- Budgeted form of `fresh_labels_factor_ge`: with `|forbidden| ≤ 2 · base + 1` and
`base + |J| ≤ total`, the fresh-label factor is at least `1 - total (total + 1) / |S|`. -/
lemma fresh_labels_factor_ge_of_budget {J : Type u} {S : Type v} [Fintype J] [Fintype S]
    [Nonempty S] (forbidden : Finset S) (base total : Nat)
    (hforbidden : forbidden.card ≤ 2 * base + 1)
    (hbudget : base + Fintype.card J ≤ total) :
    1 - (total : ℝ) * (total + 1) / Fintype.card S ≤
      (((Fintype.card S - forbidden.card).descFactorial (Fintype.card J) : ℝ) /
        (Fintype.card S : ℝ) ^ Fintype.card J) := by
  have hn : (Fintype.card J).choose 2 + Fintype.card J * forbidden.card ≤
      total * (total + 1) := by
    calc
      _ ≤ (Fintype.card J) ^ 2 + Fintype.card J * (2 * base + 1) :=
        Nat.add_le_add (Nat.choose_le_pow _ _) (Nat.mul_le_mul_left _ hforbidden)
      _ ≤ (base + Fintype.card J) * (base + Fintype.card J + 1) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul hbudget (Nat.add_le_add_right hbudget 1)
  have hr : ((Fintype.card J).choose 2 : ℝ) + Fintype.card J * forbidden.card ≤
      (total : ℝ) * (total + 1) := by exact_mod_cast hn
  exact (sub_le_sub_left (div_le_div_of_nonneg_right hr (Nat.cast_nonneg _)) 1).trans
    (fresh_labels_factor_ge forbidden)

/-! ### Adaptive replay against a fixed public permutation table -/

section PublicReplay

-- `S` is the permuted set; `I` indexes replayed sites and `J` fixed public entries.
variable {S : Type u} {I J : Type v} [Fintype S] [DecidableEq S] [Fintype I] [Fintype J]

/-- **A pinned permutation replay with distinct public entries** imposes `|I| + |J|` consistent
constraints, occurring with probability `1 / (|S|)_{|I| + |J|}`. -/
theorem permutation_replay_public_mass
    (site : (I → S) → I → S) (evaluate : Equiv.Perm S → I → S)
    (pinned : ∀ π value, evaluate π = value ↔ ∀ i, π (site value i) = value i)
    (publicSite publicValue : J → S) (value : I → S)
    (hin : Function.Injective (Sum.elim (site value) publicSite))
    (hout : Function.Injective (Sum.elim value publicValue)) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => evaluate π = value ∧ ∀ j, π (publicSite j) = publicValue j) =
        1 / ((Fintype.card S).descFactorial (Fintype.card I + Fintype.card J) : ℝ) := by
  have hc := permutation_constraints_mass
    (⟨Sum.elim (site value) publicSite, hin⟩ : I ⊕ J ↪ S)
    (⟨Sum.elim value publicValue, hout⟩ : I ⊕ J ↪ S)
  rw [Fintype.card_sum] at hc
  refine (Distribution.mass_congr _ (fun π => ?_)).trans hc
  rw [pinned]
  constructor
  · rintro ⟨hi, hj⟩ index
    cases index with
    | inl i => exact hi i
    | inr j => exact hj j
  · intro h
    exact ⟨fun i => h (.inl i), fun j => h (.inr j)⟩

open Classical in
/-- **Exact good-replay likelihood with a fixed public transcript**: summing
`permutation_replay_public_mass` over the good output fibres factors as the independent-label
mass of `Good ∧ Event` times `|S|^{|I|} / (|S|)_{|I| + |J|}`. -/
theorem permutation_replay_public_good_factor [Nonempty S]
    (site : (I → S) → I → S) (evaluate : Equiv.Perm S → I → S)
    (pinned : ∀ π value, evaluate π = value ↔ ∀ i, π (site value i) = value i)
    (publicSite publicValue : J → S) (Good Event : (I → S) → Prop)
    (hin : ∀ value, Good value → Function.Injective (Sum.elim (site value) publicSite))
    (hout : ∀ value, Good value → Function.Injective (Sum.elim value publicValue)) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => Good (evaluate π) ∧ Event (evaluate π) ∧
        ∀ j, π (publicSite j) = publicValue j) =
      (Distribution.uniform (I → S)).mass (fun value => Good value ∧ Event value) *
        ((Fintype.card S : ℝ) ^ Fintype.card I /
          ((Fintype.card S).descFactorial (Fintype.card I + Fintype.card J) : ℝ)) := by
  classical
  -- Fibre the event over the replay's output tuple.
  rw [Distribution.mass_eq_sum_mass_fiber _ _ evaluate Finset.univ
    (fun _ _ => Finset.mem_univ _)]
  conv_rhs => rw [Distribution.mass_eq_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro value _
  by_cases hg : Good value ∧ Event value
  · rw [ite_eq_left hg]
    have he := permutation_replay_public_mass site evaluate pinned publicSite publicValue
      value (hin value hg.1) (hout value hg.1)
    have hm : (Distribution.uniform (Equiv.Perm S)).mass
        (fun π => (Good (evaluate π) ∧ Event (evaluate π) ∧
          ∀ j, π (publicSite j) = publicValue j) ∧ evaluate π = value) =
        (Distribution.uniform (Equiv.Perm S)).mass
          (fun π => evaluate π = value ∧ ∀ j, π (publicSite j) = publicValue j) := by
      apply Distribution.mass_congr
      intro π
      constructor
      · rintro ⟨⟨_, _, hpub⟩, hv⟩
        exact ⟨hv, hpub⟩
      · rintro ⟨hv, hpub⟩
        exact ⟨hv.symm ▸ ⟨hg.1, hg.2, hpub⟩, hv⟩
    rw [hm, he, Distribution.uniform_apply, Fintype.card_fun, Nat.cast_pow]
    have hn : (Fintype.card S : ℝ) ^ Fintype.card I ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
    rw [← mul_div_assoc, one_div_mul_cancel hn]
  · -- A fibre outside `Good ∧ Event` contributes nothing on either side.
    rw [ite_eq_right hg, zero_mul]
    apply Distribution.mass_eq_zero_of_forall_not
    rintro π ⟨⟨hgood, hevent, _⟩, hv⟩
    exact hg (hv ▸ ⟨hgood, hevent⟩)

open Classical in
/-- The exact joint likelihood dominates independent replay labels times the exact public-table
likelihood `1 / (|S|)_{|J|}`. No primitive-switching error is introduced. -/
theorem permutation_replay_public_good_lower_bound [Nonempty S]
    (site : (I → S) → I → S) (evaluate : Equiv.Perm S → I → S)
    (pinned : ∀ π value, evaluate π = value ↔ ∀ i, π (site value i) = value i)
    (publicSite publicValue : J → S) (Good Event : (I → S) → Prop)
    (hin : ∀ value, Good value → Function.Injective (Sum.elim (site value) publicSite))
    (hout : ∀ value, Good value → Function.Injective (Sum.elim value publicValue))
    (hsize : Fintype.card I + Fintype.card J ≤ Fintype.card S) :
    (Distribution.uniform (I → S)).mass (fun value => Good value ∧ Event value) *
        (1 / ((Fintype.card S).descFactorial (Fintype.card J) : ℝ)) ≤
      (Distribution.uniform (Equiv.Perm S)).mass
        (fun π => Good (evaluate π) ∧ Event (evaluate π) ∧
          ∀ j, π (publicSite j) = publicValue j) := by
  rw [permutation_replay_public_good_factor site evaluate pinned publicSite publicValue
    Good Event hin hout]
  apply mul_le_mul_of_nonneg_left _ (Distribution.uniform_nonNeg.mass_nonneg _)
  have hb : 0 < ((Fintype.card S).descFactorial (Fintype.card J) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : Fintype.card J ≤ Fintype.card S)
  have ht : 0 < ((Fintype.card S).descFactorial
      (Fintype.card I + Fintype.card J) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hsize
  apply (div_le_div_iff₀ hb ht).mpr
  rw [one_mul]
  -- `(|S|)_{|I|+|J|} = (|S|)_{|J|} · (|S| - |J|)_{|I|} ≤ |S|^{|I|} · (|S|)_{|J|}`.
  have hm := Nat.descFactorial_mul_descFactorial
    (n := Fintype.card S) (k := Fintype.card J)
    (m := Fintype.card I + Fintype.card J) (by omega)
  rw [Nat.add_sub_cancel] at hm
  have hl : (Fintype.card S).descFactorial (Fintype.card I + Fintype.card J) ≤
      (Fintype.card S) ^ Fintype.card I *
        (Fintype.card S).descFactorial (Fintype.card J) := by
    rw [← hm]
    exact Nat.mul_le_mul_right _ ((Nat.descFactorial_le_pow _ _).trans
      (Nat.pow_le_pow_left (Nat.sub_le _ _) _))
  exact_mod_cast hl

end PublicReplay

/-! ### Conditional reply-event upper bounds -/

section ConditionalBounds

-- `S` is the permuted set, with a recorded partial table `points ↦ reference`.
variable {S : Type u} [Fintype S] [DecidableEq S]

/-- A specified reply to a fresh forward query costs at most one unused output slot. -/
lemma permutation_forward_reply_mass_le (reference : Equiv.Perm S) (points : Finset S)
    (x y : S) (hx : x ∉ points) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => (∀ z ∈ points, π z = reference z) ∧ π x = y) ≤
        (1 / (Fintype.card S - points.card : ℝ)) *
          (Distribution.uniform (Equiv.Perm S)).mass
            (fun π => ∀ z ∈ points, π z = reference z) := by
  by_cases hy : y ∈ points.image reference
  · -- An already used image is impossible at a fresh input.
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hn (π : Equiv.Perm S) :
        ¬ ((∀ z ∈ points, π z = reference z) ∧ π x = reference z) := by
      rintro ⟨hp, he⟩
      exact hx (π.injective (he.trans (hp z hz).symm) ▸ hz)
    rw [Distribution.mass_eq_zero_of_forall_not _ hn]
    exact mul_nonneg (one_div_nonneg.mpr (sub_nonneg.mpr
      (Nat.cast_le.mpr points.card_le_univ))) (Distribution.uniform_nonNeg.mass_nonneg _)
  · exact (permutation_fresh_edge_factor reference points x y hx hy).le

/-- The same bound for a fresh inverse query, oriented as a new forward edge. -/
lemma permutation_inverse_reply_mass_le (reference : Equiv.Perm S) (points : Finset S)
    (x y : S) (hx : x ∉ points.image reference) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => (∀ z ∈ points, π z = reference z) ∧ π.symm x = y) ≤
        (1 / (Fintype.card S - points.card : ℝ)) *
          (Distribution.uniform (Equiv.Perm S)).mass
            (fun π => ∀ z ∈ points, π z = reference z) := by
  by_cases hy : y ∈ points
  · have hn (π : Equiv.Perm S) :
        ¬ ((∀ z ∈ points, π z = reference z) ∧ π.symm x = y) := by
      rintro ⟨hp, he⟩
      have he' : π y = x := by
        rw [← he, π.apply_symm_apply]
      exact hx (Finset.mem_image.mpr ⟨y, hy, (hp y hy).symm.trans he'⟩)
    rw [Distribution.mass_eq_zero_of_forall_not _ hn]
    exact mul_nonneg (one_div_nonneg.mpr (sub_nonneg.mpr
      (Nat.cast_le.mpr points.card_le_univ))) (Distribution.uniform_nonNeg.mass_nonneg _)
  · exact (permutation_inverse_fresh_edge_factor reference points x y hx hy).le

/-- A fresh forward or inverse reply lands in a fixed set `bad` with its without-replacement
probability `|bad| / (|S| - |points|)`, conditional on the recorded table. -/
lemma permutation_reply_set_mass_le (reference : Equiv.Perm S) (points bad : Finset S)
    (inverse : Bool) (x : S)
    (hfresh : if inverse then x ∉ points.image reference else x ∉ points) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => (∀ z ∈ points, π z = reference z) ∧
        (if inverse then π.symm x else π x) ∈ bad) ≤
      (bad.card / (Fintype.card S - points.card : ℝ)) *
        (Distribution.uniform (Equiv.Perm S)).mass
          (fun π => ∀ z ∈ points, π z = reference z) := by
  classical
  let event (y : S) (π : Equiv.Perm S) :=
    (∀ z ∈ points, π z = reference z) ∧ (if inverse then π.symm x else π x) = y
  have he : (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => (∀ z ∈ points, π z = reference z) ∧
        (if inverse then π.symm x else π x) ∈ bad) =
      (Distribution.uniform (Equiv.Perm S)).mass (fun π => ∃ y ∈ bad, event y π) := by
    apply Distribution.mass_congr
    intro π
    constructor
    · rintro ⟨hp, hb⟩
      exact ⟨_, hb, hp, rfl⟩
    · rintro ⟨y, hy, hp, he⟩
      exact ⟨hp, he ▸ hy⟩
  rw [he]
  -- Union bound over the bad replies, each charged one unused slot.
  refine (Distribution.mass_exists_le Distribution.uniform_nonNeg bad event).trans ?_
  have hb (y : S) : (Distribution.uniform (Equiv.Perm S)).mass (event y) ≤
      (1 / (Fintype.card S - points.card : ℝ)) *
        (Distribution.uniform (Equiv.Perm S)).mass
          (fun π => ∀ z ∈ points, π z = reference z) := by
    cases inverse
    · exact permutation_forward_reply_mass_le reference points x y hfresh
    · exact permutation_inverse_reply_mass_le reference points x y hfresh
  refine (Finset.sum_le_sum (fun y _ => hb y)).trans_eq ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Conditional fresh-reply loss is the uniform-state loss `𝒰(S)[bad]` times the exact
remaining-space correction `|S| / (|S| - |points|)`. Inverse queries are included. -/
lemma permutation_reply_event_mass_le [Nonempty S]
    (reference : Equiv.Perm S) (points : Finset S) (bad : S → Prop)
    (inverse : Bool) (x : S)
    (hfresh : if inverse then x ∉ points.image reference else x ∉ points) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => (∀ z ∈ points, π z = reference z) ∧
        bad (if inverse then π.symm x else π x)) ≤
      ((Fintype.card S : ℝ) / (Fintype.card S - points.card : ℝ)) *
        (Distribution.uniform S).mass bad *
        (Distribution.uniform (Equiv.Perm S)).mass
          (fun π => ∀ z ∈ points, π z = reference z) := by
  classical
  have he := permutation_reply_set_mass_le reference points
    (Finset.univ.filter bad) inverse x hfresh
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
  refine he.trans_eq ?_
  rw [Distribution.uniform_mass_eq_card_filter bad]
  have hc : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Fresh replies avoid their forbidden sets with joint mass at least
`Pr[table] · (1 - ∑ i, |bad i| / (|S| - |points|))`. Requests may repeat. -/
theorem permutation_avoid_mass_ge
    -- `reference` witnesses the consistent table recorded at inputs in `points`.
    (reference : Equiv.Perm S) (points : Finset S)
    -- `indices` selects finitely many requests; `inverse i` selects the direction at `input i`.
    {ι : Type*} (indices : Finset ι) (inverse : ι → Bool) (input : ι → S)
    -- `bad i` contains the forbidden replies; each request is fresh relative to the table.
    (bad : ι → Finset S)
    (fresh : ∀ i ∈ indices,
      if inverse i then input i ∉ points.image reference else input i ∉ points) :
    (1 - ∑ i ∈ indices, (bad i).card / (Fintype.card S - points.card : ℝ)) *
        (Distribution.uniform (Equiv.Perm S)).mass
          (fun π => ∀ z ∈ points, π z = reference z) ≤
      (Distribution.uniform (Equiv.Perm S)).mass
        (fun π => (∀ z ∈ points, π z = reference z) ∧ ∀ i ∈ indices,
          (if inverse i then π.symm (input i) else π (input i)) ∉ bad i) := by
  classical
  let agreed (π : Equiv.Perm S) := ∀ z ∈ points, π z = reference z
  let avoids (π : Equiv.Perm S) := ∀ i ∈ indices,
    (if inverse i then π.symm (input i) else π (input i)) ∉ bad i
  let failure (i : ι) (π : Equiv.Perm S) := agreed π ∧
    (if inverse i then π.symm (input i) else π (input i)) ∈ bad i
  let μ := Distribution.uniform (Equiv.Perm S)
  -- Charge each request once, even when several requests read the same permutation edge.
  have union := Distribution.mass_exists_le Distribution.uniform_nonNeg indices failure
  have losses : (∑ i ∈ indices, μ.mass (failure i)) ≤
      (∑ i ∈ indices, (bad i).card / (Fintype.card S - points.card : ℝ)) *
        μ.mass agreed := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i hi =>
      permutation_reply_set_mass_le reference points (bad i) (inverse i) (input i) (fresh i hi)
  have failed : μ.mass (fun π => ¬ avoids π ∧ agreed π) =
      μ.mass (fun π => ∃ i ∈ indices, failure i π) := by
    apply Distribution.mass_congr
    intro π
    simp only [avoids, not_forall, not_not]
    constructor
    · rintro ⟨⟨i, hi, hb⟩, he⟩
      exact ⟨i, hi, he, hb⟩
    · rintro ⟨i, hi, he, hb⟩
      exact ⟨⟨i, hi, hb⟩, he⟩
  -- Agreement partitions into avoidance and failure; subtract the union-bound loss.
  have partition := Distribution.mass_and_add_mass_not_and μ avoids agreed
  rw [failed, Distribution.mass_congr μ (fun _ => and_comm)] at partition
  have bound := union.trans losses
  change (1 - _) * μ.mass agreed ≤ μ.mass (fun π => agreed π ∧ avoids π)
  linarith

/-- If every forbidden set has at most `m` elements, the avoidance loss is at most
`|indices| * m / (|S| - |points|)`. -/
lemma permutation_avoid_mass_ge_of_card_le
    -- `reference` fixes the recorded partial permutation on `points`.
    (reference : Equiv.Perm S) (points : Finset S)
    -- Request `i` uses direction `inverse i`, input `input i`, and forbidden set `bad i`.
    {ι : Type*} (indices : Finset ι) (inverse : ι → Bool) (input : ι → S)
    (bad : ι → Finset S)
    (fresh : ∀ i ∈ indices,
      if inverse i then input i ∉ points.image reference else input i ∉ points)
    -- `m` bounds each forbidden set, including repeated requests.
    (m : ℕ) (size : ∀ i ∈ indices, (bad i).card ≤ m) :
    (1 - (indices.card : ℝ) * m / (Fintype.card S - points.card : ℝ)) *
        (Distribution.uniform (Equiv.Perm S)).mass
          (fun π => ∀ z ∈ points, π z = reference z) ≤
      (Distribution.uniform (Equiv.Perm S)).mass
        (fun π => (∀ z ∈ points, π z = reference z) ∧ ∀ i ∈ indices,
          (if inverse i then π.symm (input i) else π (input i)) ∉ bad i) := by
  have denominator : 0 ≤ (Fintype.card S - points.card : ℝ) :=
    sub_nonneg.mpr (Nat.cast_le.mpr points.card_le_univ)
  have loss : (∑ i ∈ indices, (bad i).card / (Fintype.card S - points.card : ℝ)) ≤
      (indices.card : ℝ) * m / (Fintype.card S - points.card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ indices, (m : ℝ) / (Fintype.card S - points.card : ℝ) :=
        Finset.sum_le_sum fun i hi =>
          div_le_div_of_nonneg_right (Nat.cast_le.mpr (size i hi)) denominator
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]
  -- Increase the general union-bound loss using the supplied common cardinality bound.
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left loss 1)
    (Distribution.uniform_nonNeg.mass_nonneg _)).trans
      (permutation_avoid_mass_ge reference points indices inverse input bad fresh)

end ConditionalBounds

end

end Probability.Counting
