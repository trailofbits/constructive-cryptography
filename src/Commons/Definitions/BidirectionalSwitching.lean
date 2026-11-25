module

public import Commons.Definitions.Ideal
public import ConstructiveCryptography.Instances.Game
public import ConstructiveCryptography.Notation.Basic
public import Probability.Conditioning
public import RandomSystems.Game.UntilBad
public import RandomSystems.Typed.ProbAutomatonGame

/-!
# Bidirectional random permutation / random function switching

Equivalence-as-games (`≡g`) switching bound between the bidirectional ideal permutation
`StrongURP X` and the lazy with-replacement bidirectional random function
`LazyBidirectionalRF X q` [1, Definition 4.16, Theorem 4.17], [2, §4.4.3].
The latter retains a partial bijection: colliding replies are returned without insertion,
so a repeated fresh query samples again.


* **Lazy `StrongURP` presentation (`lazyStrongURP`)**: maintains a partial bijection table,
  replaying hits and sampling uniformly outside the recorded range/domain on fresh forward/inverse
  queries (`lazyStrongURP_eq_strongURP`).
* **Rejection-coin game (`strongURPRejectionGame`)**: on each fresh query, draws uniformly from
  `X`; if the draw collides with the recorded range/domain, resamples from the unused set and sets
  the MBO. Its visible system is `StrongURP X` (`strongURPRejectionGame_visible`).
* **Lazy bidirectional random function (`LazyBidirectionalRF`, `lazyBidirectionalRFGame`)**: on
  each fresh query, draws uniformly from `X` and records the edge when non-colliding, setting the
  MBO on a collision. Its visible system is `LazyBidirectionalRF X q`
  (`lazyBidirectionalRFGame_visible`).
* **Exact game equivalence and switching bound**: both games agree identically on all unset
  transcripts (`strongURPRejectionGame_gameEquivalent_lazyBidirectionalRFGame`), giving exact
  transcript mass `1 / |X|^k` (`lazyBidirectionalRF_unset_mass`) vs `1 / (|X|)_k` for `StrongURP`
  (`strongURP_mass_of_bijective_table`), winning probability at most `C(q, 2) / |X|`, and CC
  statistical distance / substitution bounds (`strongURP_dist_lazyBidirectionalRF_le`,
  `strongURP_attach_dist_lazyBidirectionalRF_le`,
  `strongURP_substitutesWithin_lazyBidirectionalRF`).

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open CategoryTheory SystemAlgebra Probability Probability.Distribution
open scoped BigOperators NNReal SystemAlgebra

namespace BidirectionalSwitching

/-! ### Partial-bijection tables and exact `StrongURP` counting -/

section PartialBijection

variable {X : Type}

open Classical in
/-- Forward lookup in a list of `(input, output)` pairs. -/
noncomputable def lookupForward (table : List (X × X)) (x : X) : Option X :=
  table.lookup x

open Classical in
/-- Inverse lookup in a list of `(input, output)` pairs. -/
noncomputable def lookupInverse (table : List (X × X)) (y : X) : Option X :=
  (table.map Prod.swap).lookup y

/-- A pair list represents a partial bijection when its inputs and outputs are duplicate-free. -/
def IsPartialBijection (table : List (X × X)) : Prop :=
  (table.map Prod.fst).Nodup ∧ (table.map Prod.snd).Nodup

/-- A permutation `π` agrees with every recorded `(x, y)` pair in `table`. -/
def Agrees (table : List (X × X)) (π : Equiv.Perm X) : Prop :=
  ∀ p ∈ table, π p.1 = p.2

open Classical in
lemma lookupForward_eq_none_iff (table : List (X × X)) (x : X) :
    lookupForward table x = none ↔ x ∉ table.map Prod.fst := by
  simp only [lookupForward, List.lookup_eq_none_iff, List.mem_map, not_exists, not_and]
  constructor
  · intro h p hp hpx
    have := h p hp
    simp only [hpx, bne_self_eq_false, Bool.false_eq_true] at this
  · intro h p hp
    simp only [bne_iff_ne, ne_eq]
    exact fun hx => h p hp hx.symm

open Classical in
lemma lookupInverse_eq_none_iff (table : List (X × X)) (y : X) :
    lookupInverse table y = none ↔ y ∉ table.map Prod.snd := by
  simp only [lookupInverse, List.lookup_eq_none_iff, List.mem_map, not_exists, not_and]
  constructor
  · intro h p hp hpy
    have := h (p.2, p.1) ⟨p, hp, rfl⟩
    simp only [hpy, bne_self_eq_false, Bool.false_eq_true] at this
  · intro h q ⟨p, hp, hq⟩
    subst hq
    simp only [bne_iff_ne, ne_eq]
    exact fun hy => h p hp hy.symm

open Classical in
lemma mem_of_lookupForward_eq_some {table : List (X × X)} {x y : X}
    (h : lookupForward table x = some y) : (x, y) ∈ table := by
  obtain ⟨l₁, l₂, he, _⟩ := List.lookup_eq_some_iff.mp h
  rw [he]
  exact List.mem_append_right _ (List.mem_cons_self ..)

open Classical in
lemma mem_of_lookupInverse_eq_some {table : List (X × X)} {x y : X}
    (h : lookupInverse table y = some x) : (x, y) ∈ table := by
  obtain ⟨l₁, l₂, he, _⟩ := List.lookup_eq_some_iff.mp h
  have hswap : (y, x) ∈ table.map Prod.swap := by
    rw [he]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨⟨a, b⟩, hm, heq⟩ := List.mem_map.mp hswap
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
  rw [← heq.1, ← heq.2]
  exact hm

lemma isPartialBijection_nil : IsPartialBijection ([] : List (X × X)) :=
  ⟨List.nodup_nil, List.nodup_nil⟩

lemma isPartialBijection_append {table : List (X × X)} (hb : IsPartialBijection table)
    {x y : X} (hx : x ∉ table.map Prod.fst) (hy : y ∉ table.map Prod.snd) :
    IsPartialBijection (table ++ [(x, y)]) := by
  constructor
  · rw [List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hb.1, List.nodup_singleton x, ?_⟩
    rintro a ha b hb' rfl
    have hbx := List.mem_singleton.mp hb'
    subst hbx
    exact hx ha
  · rw [List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨hb.2, List.nodup_singleton y, ?_⟩
    rintro a ha b hb' rfl
    have hby := List.mem_singleton.mp hb'
    subst hby
    exact hy ha

section FiniteCounting

variable [Fintype X]

open Classical in
/-- All permutations on `X` agreeing with `table`. -/
noncomputable def completions (table : List (X × X)) : Finset (Equiv.Perm X) :=
  Finset.univ.filter (Agrees table)

open Classical in
/-- Outputs not yet appearing in `table`. -/
noncomputable def unusedOutputs (table : List (X × X)) : Finset X :=
  Finset.univ.filter fun y => y ∉ table.map Prod.snd

open Classical in
/-- Inputs not yet appearing in `table`. -/
noncomputable def unusedInputs (table : List (X × X)) : Finset X :=
  Finset.univ.filter fun x => x ∉ table.map Prod.fst

open Classical in
lemma card_unusedOutputs {table : List (X × X)} (hb : IsPartialBijection table) :
    (unusedOutputs table).card = Fintype.card X - table.length := by
  have heq : unusedOutputs table = Finset.univ \ (table.map Prod.snd).toFinset := by
    ext y
    simp only [unusedOutputs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      List.mem_toFinset]
  have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (table.map Prod.snd).toFinset)
  rw [← heq, Finset.card_univ, List.toFinset_card_of_nodup hb.2, List.length_map] at hadd
  omega

open Classical in
lemma card_unusedInputs {table : List (X × X)} (hb : IsPartialBijection table) :
    (unusedInputs table).card = Fintype.card X - table.length := by
  have heq : unusedInputs table = Finset.univ \ (table.map Prod.fst).toFinset := by
    ext x
    simp only [unusedInputs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      List.mem_toFinset]
  have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (table.map Prod.fst).toFinset)
  rw [← heq, Finset.card_univ, List.toFinset_card_of_nodup hb.1, List.length_map] at hadd
  omega

open Classical in
lemma length_lt_card_of_fresh_input {table : List (X × X)} (hb : IsPartialBijection table)
    {x : X} (hx : x ∉ table.map Prod.fst) : table.length < Fintype.card X := by
  have hcard : (insert x (table.map Prod.fst).toFinset).card ≤ Fintype.card X :=
    Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem (by simpa only [List.mem_toFinset] using hx),
    List.toFinset_card_of_nodup hb.1, List.length_map] at hcard
  omega

open Classical in
lemma length_lt_card_of_fresh_output {table : List (X × X)} (hb : IsPartialBijection table)
    {y : X} (hy : y ∉ table.map Prod.snd) : table.length < Fintype.card X := by
  have hcard : (insert y (table.map Prod.snd).toFinset).card ≤ Fintype.card X :=
    Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem (by simpa only [List.mem_toFinset] using hy),
    List.toFinset_card_of_nodup hb.2, List.length_map] at hcard
  omega

open Classical in
lemma unusedOutputs_nonempty_of_fresh {table : List (X × X)} (hb : IsPartialBijection table)
    {x : X} (hx : x ∉ table.map Prod.fst) : (unusedOutputs table).Nonempty := by
  rw [← Finset.card_pos, card_unusedOutputs hb]
  have := length_lt_card_of_fresh_input hb hx
  omega

open Classical in
lemma unusedInputs_nonempty_of_fresh {table : List (X × X)} (hb : IsPartialBijection table)
    {y : X} (hy : y ∉ table.map Prod.snd) : (unusedInputs table).Nonempty := by
  rw [← Finset.card_pos, card_unusedInputs hb]
  have := length_lt_card_of_fresh_output hb hy
  omega

open Classical in
lemma mem_completions_iff (table : List (X × X)) (π : Equiv.Perm X) :
    π ∈ completions table ↔ Agrees table π := by
  simp only [completions, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
/-- Every partial bijection extends to a full permutation of `X`. -/
lemma completions_nonempty_of_isPartialBijection {table : List (X × X)}
    (hb : IsPartialBijection table) : (completions table).Nonempty := by
  induction table with
  | nil => exact ⟨Equiv.refl X, (mem_completions_iff [] _).mpr fun _ hm => by cases hm⟩
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    have hnd1 := List.nodup_cons.mp hb.1
    have hnd2 := List.nodup_cons.mp hb.2
    obtain ⟨π, hπ⟩ := ih ⟨hnd1.2, hnd2.2⟩
    have hagr := (mem_completions_iff rest π).mp hπ
    refine ⟨Equiv.swap (π x) y * π, (mem_completions_iff _ _).mpr ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hqr
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    · have hne1 : π q.1 ≠ π x := fun he => hnd1.1 (List.mem_map.mpr ⟨q, hqr, π.injective he⟩)
      have hne2 : π q.1 ≠ y := fun he =>
        hnd2.1 (List.mem_map.mpr ⟨q, hqr, (hagr q hqr).symm.trans he⟩)
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2, hagr q hqr]

open Classical in
lemma mem_completions_append_iff (table : List (X × X)) (x y : X) (π : Equiv.Perm X) :
    π ∈ completions (table ++ [(x, y)]) ↔ π ∈ completions table ∧ π x = y := by
  simp only [mem_completions_iff, Agrees, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Or.inl hp), h (x, y) (Or.inr rfl)⟩
  · rintro ⟨h, hxy⟩ p (hp | rfl)
    · exact h p hp
    · exact hxy

open Classical in
/-- Output-swap bijection preserves `completions table` when both swapped outputs are unused. -/
lemma swap_output_mem_completions_iff (table : List (X × X)) {y z : X}
    (hy : y ∉ table.map Prod.snd) (hz : z ∉ table.map Prod.snd) (π : Equiv.Perm X) :
    Equiv.swap y z * π ∈ completions table ↔ π ∈ completions table := by
  simp only [mem_completions_iff, Agrees, Equiv.Perm.mul_apply]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  have hy' : p.2 ≠ y := fun he => hy (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hz' : p.2 ≠ z := fun he => hz (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne hy' hz']

open Classical in
/-- Input-swap bijection preserves `completions table` when both swapped inputs are unused. -/
lemma swap_input_mem_completions_iff (table : List (X × X)) {x w : X}
    (hx : x ∉ table.map Prod.fst) (hw : w ∉ table.map Prod.fst) (π : Equiv.Perm X) :
    π * Equiv.swap x w ∈ completions table ↔ π ∈ completions table := by
  simp only [mem_completions_iff, Agrees, Equiv.Perm.mul_apply]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  have hx' : p.1 ≠ x := fun he => hx (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hw' : p.1 ≠ w := fun he => hw (he ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
  rw [Equiv.swap_apply_of_ne_of_ne hx' hw']

open Classical in
lemma card_completions_cons {x y : X} {rest : List (X × X)}
    (hb : IsPartialBijection ((x, y) :: rest)) :
    (completions rest).card =
      (Fintype.card X - rest.length) * (completions ((x, y) :: rest)).card := by
  have hnd1 := List.nodup_cons.mp hb.1
  have hnd2 := List.nodup_cons.mp hb.2
  have hbrest : IsPartialBijection rest := ⟨hnd1.2, hnd2.2⟩
  have hpart : (completions rest).card =
      ∑ z ∈ unusedOutputs rest, ((completions rest).filter fun π => π x = z).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext π
      simp only [Finset.mem_biUnion, Finset.mem_filter, unusedOutputs, Finset.mem_univ, true_and]
      constructor
      · intro hπ
        refine ⟨π x, ?_, hπ, rfl⟩
        intro hm
        obtain ⟨q, hq, hqy⟩ := List.mem_map.mp hm
        have hqx : x = q.1 :=
          π.injective (hqy.symm.trans ((mem_completions_iff rest π).mp hπ q hq).symm)
        exact hnd1.1 (List.mem_map.mpr ⟨q, hq, hqx.symm⟩)
      · rintro ⟨_, _, hπ, _⟩
        exact hπ
    · intro a _ b _ hab
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro π ha hb'
      exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb').2)
  have hfiber (z : X) (hz : z ∈ unusedOutputs rest) :
      ((completions rest).filter fun π => π x = z).card =
        (completions ((x, y) :: rest)).card := by
    have hz' : z ∉ rest.map Prod.snd := (Finset.mem_filter.mp hz).2
    refine Finset.card_bij (fun π _ => Equiv.swap z y * π) ?_ ?_ ?_
    · intro π hπ
      rw [Finset.mem_filter] at hπ
      rw [mem_completions_iff]
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hpr
      · simp only [Equiv.Perm.mul_apply, hπ.2, Equiv.swap_apply_left]
      · exact (mem_completions_iff rest _).mp
          ((swap_output_mem_completions_iff rest hz' hnd2.1 π).mpr hπ.1) p hpr
    · intro π₁ _ π₂ _ heq
      exact mul_left_cancel heq
    · intro π hπ
      refine ⟨Equiv.swap z y * π, ?_, by simp only [← mul_assoc, Equiv.swap_mul_self, one_mul]⟩
      rw [Finset.mem_filter]
      have hπ' := (mem_completions_iff _ π).mp hπ
      have hrest : π ∈ completions rest :=
        (mem_completions_iff rest π).mpr fun p hp => hπ' p (List.mem_cons_of_mem _ hp)
      have hxy : π x = y := hπ' (x, y) (List.mem_cons_self ..)
      exact ⟨(swap_output_mem_completions_iff rest hz' hnd2.1 π).mpr hrest,
        by simp only [Equiv.Perm.mul_apply, hxy, Equiv.swap_apply_right]⟩
  rw [hpart, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul,
    card_unusedOutputs hbrest]

open Classical in
/-- Exact count of permutations extending a partial bijection of length `k`:
`|(completions table)| · (|X|)_k = |X|!`. -/
lemma card_completions_mul_descFactorial {table : List (X × X)}
    (hb : IsPartialBijection table) :
    (completions table).card * (Fintype.card X).descFactorial table.length =
      (Fintype.card X).factorial := by
  induction table with
  | nil =>
    simp only [List.length_nil, Nat.descFactorial_zero, mul_one]
    have hfull : completions ([] : List (X × X)) = Finset.univ := by
      ext π
      simp only [mem_completions_iff, Agrees, List.not_mem_nil, false_implies, implies_true,
        Finset.mem_univ]
    rw [hfull, Finset.card_univ, Fintype.card_perm]
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    have hbrest : IsPartialBijection rest :=
      ⟨(List.nodup_cons.mp hb.1).2, (List.nodup_cons.mp hb.2).2⟩
    have hstep := card_completions_cons hb
    rw [List.length_cons, Nat.descFactorial_succ]
    calc
      (completions ((x, y) :: rest)).card *
          ((Fintype.card X - rest.length) * (Fintype.card X).descFactorial rest.length)
        = ((Fintype.card X - rest.length) * (completions ((x, y) :: rest)).card) *
            (Fintype.card X).descFactorial rest.length := by ring
      _ = (completions rest).card * (Fintype.card X).descFactorial rest.length := by rw [← hstep]
      _ = (Fintype.card X).factorial := ih hbrest

open Classical in
/-- Uniform permutation probability of agreeing with a partial bijection `table` is
`1 / (|X|)_{table.length}`. -/
lemma uniform_perm_mass_agrees_eq {table : List (X × X)} (hb : IsPartialBijection table) :
    (Distribution.uniform (Equiv.Perm X)).mass (Agrees table) =
      1 / ((Fintype.card X).descFactorial table.length : ℝ) := by
  rw [Distribution.uniform_mass_eq_card_filter, Fintype.card_perm]
  change ((completions table).card : ℝ) / ((Fintype.card X).factorial : ℝ) = _
  have hmul : ((completions table).card : ℝ) *
      ((Fintype.card X).descFactorial table.length : ℝ) = ((Fintype.card X).factorial : ℝ) := by
    exact_mod_cast card_completions_mul_descFactorial hb
  have hlen : table.length ≤ Fintype.card X := by
    have h := Finset.card_le_univ (table.map Prod.fst).toFinset
    rwa [List.toFinset_card_of_nodup hb.1, List.length_map] at h
  have hdesc_pos : (0 : ℝ) < ((Fintype.card X).descFactorial table.length : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hlen
  have hfact_pos : (0 : ℝ) < ((Fintype.card X).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (Fintype.card X)
  rw [div_eq_div_iff (ne_of_gt hfact_pos) (ne_of_gt hdesc_pos), one_mul]
  exact hmul

/-- Reply of a permutation `π` on a `Bidirectional` query. -/
def permEval (q : ℕ) (π : Equiv.Perm X) (u : Σ i, (Bidirectional X q).X i) :
    Σ i, (Bidirectional X q).Y i :=
  match u with
  | ⟨.forward, x⟩ => ⟨.forward, π x⟩
  | ⟨.inverse, y⟩ => ⟨.inverse, π.symm y⟩

end FiniteCounting

end PartialBijection

/-! ### Lazy presentation of `StrongURP` -/

section LazyStrongURP

variable {X : Type} [Fintype X] [Nonempty X]

open Classical in
/-- Uniform distribution over outputs not yet in `table`. -/
noncomputable def unusedForwardLaw (table : List (X × X)) : ProbDist X :=
  ProbDist.uniformOn (fun y => y ∉ table.map Prod.snd) 𝒰[X]

open Classical in
/-- Uniform distribution over inputs not yet in `table`. -/
noncomputable def unusedInverseLaw (table : List (X × X)) : ProbDist X :=
  ProbDist.uniformOn (fun x => x ∉ table.map Prod.fst) 𝒰[X]

open Classical in
/-- Uniform completion law over permutations agreeing with `table`. -/
noncomputable def completionLaw (table : List (X × X)) : ProbDist (Equiv.Perm X) :=
  ProbDist.uniformOn (· ∈ completions table) 𝒰[Equiv.Perm X]

open Classical in
/-- Lazy bidirectional permutation transition: replay hits; on fresh forward/inverse queries sample
uniformly outside the recorded range/domain and record the new pair. -/
noncomputable def lazyStrongURPStep (q : ℕ) :
    ProbStep (List (X × X)) (Bidirectional X q).I (Bidirectional X q).X (Bidirectional X q).Y
  | table, .forward, x =>
    match lookupForward table x with
    | some y => ProbDist.single (table, y)
    | none => (unusedForwardLaw table).map fun y => (table ++ [(x, y)], y)
  | table, .inverse, y =>
    match lookupInverse table y with
    | some x => ProbDist.single (table, x)
    | none => (unusedInverseLaw table).map fun x => (table ++ [(x, y)], x)

open Classical in
/-- Lazy bidirectional permutation on `Bidirectional X q`. -/
noncomputable def lazyStrongURP (X : Type) [Fintype X] [Nonempty X] (q : ℕ) :
    TypedSystem (Bidirectional X q) :=
  TypedSystem.ofProbAutomaton (Bidirectional X q) (lazyStrongURPStep q) (ProbDist.single [])

omit [Nonempty X] in
open Classical in
lemma mem_support_completionLaw_iff (table : List (X × X)) (h : (completions table).Nonempty)
    (π : Equiv.Perm X) :
    π ∈ (completionLaw table).1.support ↔ π ∈ completions table :=
  ProbDist.mem_support_uniformOn_iff _ h _ π

open Classical in
lemma completionLaw_forward_eq_unusedForwardLaw (table : List (X × X))
    (h : (completions table).Nonempty) (x : X) (fresh : lookupForward table x = none) :
    (completionLaw table).map (fun π => π x) = unusedForwardLaw table := by
  apply ProbDist.eq_uniformOn_of_constant
  · intro y hy
    obtain ⟨π, hπ, rfl⟩ := mem_support_fTransform _ _ hy
    have hπ' := (mem_completions_iff table π).mp ((mem_support_completionLaw_iff table h π).mp hπ)
    intro hm
    obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hm
    have hxeq : x = p.1 := π.injective (hpy.symm.trans (hπ' p hp).symm)
    exact (lookupForward_eq_none_iff table x).mp fresh (List.mem_map.mpr ⟨p, hp, hxeq.symm⟩)
  · intro y hy z hz
    let e : Equiv.Perm X ≃ Equiv.Perm X := Equiv.mulLeft (Equiv.swap y z)
    have he (π : Equiv.Perm X) : e π ∈ completions table ↔ π ∈ completions table :=
      swap_output_mem_completions_iff table hy hz π
    have hinv : fTransform e (completionLaw table).1 = (completionLaw table).1 :=
      congrArg Subtype.val (ProbDist.map_uniformOn_of_equiv _ h _ e he)
    simp only [ProbDist.map_val, fTransform_apply_eq_mass]
    calc
      (completionLaw table).1.mass (fun π => π x = y)
        = (fTransform e (completionLaw table).1).mass (fun π => π x = y) := by rw [hinv]
      _ = (completionLaw table).1.mass (fun π => π x = z) := by
        rw [mass_fTransform]
        exact mass_congr _ fun π => by
          change (Equiv.swap y z * π) x = y ↔ π x = z
          rw [Equiv.Perm.mul_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

open Classical in
lemma completionLaw_inverse_eq_unusedInverseLaw (table : List (X × X))
    (h : (completions table).Nonempty) (y : X) (fresh : lookupInverse table y = none) :
    (completionLaw table).map (fun π => π.symm y) = unusedInverseLaw table := by
  apply ProbDist.eq_uniformOn_of_constant
  · intro x hx
    obtain ⟨π, hπ, rfl⟩ := mem_support_fTransform _ _ hx
    have hπ' := (mem_completions_iff table π).mp ((mem_support_completionLaw_iff table h π).mp hπ)
    intro hm
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hm
    have hyeq : y = p.2 := by
      have := congrArg π hpx
      rw [π.apply_symm_apply] at this
      exact this.symm.trans (hπ' p hp)
    exact (lookupInverse_eq_none_iff table y).mp fresh (List.mem_map.mpr ⟨p, hp, hyeq.symm⟩)
  · intro x hx w hw
    let e : Equiv.Perm X ≃ Equiv.Perm X := Equiv.mulRight (Equiv.swap x w)
    have he (π : Equiv.Perm X) : e π ∈ completions table ↔ π ∈ completions table :=
      swap_input_mem_completions_iff table hx hw π
    have hinv : fTransform e (completionLaw table).1 = (completionLaw table).1 :=
      congrArg Subtype.val (ProbDist.map_uniformOn_of_equiv _ h _ e he)
    simp only [ProbDist.map_val, fTransform_apply_eq_mass]
    calc
      (completionLaw table).1.mass (fun π => π.symm y = x)
        = (fTransform e (completionLaw table).1).mass (fun π => π.symm y = x) := by rw [hinv]
      _ = (completionLaw table).1.mass (fun π => π.symm y = w) := by
        rw [mass_fTransform]
        exact mass_congr _ fun π => by
          change (π * Equiv.swap x w).symm y = x ↔ π.symm y = w
          have hsym : (π * Equiv.swap x w).symm y = Equiv.swap x w (π.symm y) := by
            simp only [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
          rw [hsym, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

open Classical in
lemma completionLaw_eq_bind_forward (table : List (X × X))
    (h : (completions table).Nonempty) (x : X) (fresh : lookupForward table x = none) :
    completionLaw table = (unusedForwardLaw table).bind
      (fun y => completionLaw (table ++ [(x, y)])) := by
  rw [← completionLaw_forward_eq_unusedForwardLaw table h x fresh]
  apply Subtype.ext
  rw [ProbDist.bind_val, ProbDist.map_val]
  conv_lhs => unfold completionLaw ProbDist.uniformOn
  rw [normalizeOr_eq_bindK_restrict _ _ _ (weight_restrict_uniform_ne_zero _ h) (fun π => π x)]
  apply bindK_congr
  intro y _
  simp only [completionLaw, ProbDist.uniformOn, restrict_restrict]
  congr 2
  exact restrict_congr _ fun π => (mem_completions_append_iff table x y π).symm

open Classical in
lemma completionLaw_eq_bind_inverse (table : List (X × X))
    (h : (completions table).Nonempty) (y : X) (fresh : lookupInverse table y = none) :
    completionLaw table = (unusedInverseLaw table).bind
      (fun x => completionLaw (table ++ [(x, y)])) := by
  rw [← completionLaw_inverse_eq_unusedInverseLaw table h y fresh]
  apply Subtype.ext
  rw [ProbDist.bind_val, ProbDist.map_val]
  conv_lhs => unfold completionLaw ProbDist.uniformOn
  rw [normalizeOr_eq_bindK_restrict _ _ _ (weight_restrict_uniform_ne_zero _ h)
    (fun π => π.symm y)]
  apply bindK_congr
  intro x _
  simp only [completionLaw, ProbDist.uniformOn, restrict_restrict]
  congr 2
  refine restrict_congr _ fun π => ?_
  rw [mem_completions_append_iff]
  exact and_congr_right fun _ =>
    ⟨fun hsym => by rw [← hsym, π.apply_symm_apply],
      fun hxy => by rw [← hxy, π.symm_apply_apply]⟩

open Classical in
lemma completions_append_nonempty_forward (table : List (X × X))
    (h : (completions table).Nonempty) (x : X) (fresh : lookupForward table x = none)
    (y : X) (hy : y ∈ (unusedForwardLaw table).1.support) :
    (completions (table ++ [(x, y)])).Nonempty := by
  rw [← completionLaw_forward_eq_unusedForwardLaw table h x fresh] at hy
  obtain ⟨π, hπ, hxy⟩ := mem_support_fTransform _ _ hy
  exact ⟨π, (mem_completions_append_iff table x y π).mpr
    ⟨(mem_support_completionLaw_iff table h π).mp hπ, hxy⟩⟩

open Classical in
lemma completions_append_nonempty_inverse (table : List (X × X))
    (h : (completions table).Nonempty) (y : X) (fresh : lookupInverse table y = none)
    (x : X) (hx : x ∈ (unusedInverseLaw table).1.support) :
    (completions (table ++ [(x, y)])).Nonempty := by
  rw [← completionLaw_inverse_eq_unusedInverseLaw table h y fresh] at hx
  obtain ⟨π, hπ, hxy⟩ := mem_support_fTransform _ _ hx
  refine ⟨π, (mem_completions_append_iff table x y π).mpr
    ⟨(mem_support_completionLaw_iff table h π).mp hπ, ?_⟩⟩
  rw [← hxy, π.apply_symm_apply]

open Classical in
/-- The lazy bidirectional permutation equals `StrongURP X` on every admitted history. -/
theorem lazyStrongURP_eq_strongURP (q : ℕ) :
    lazyStrongURP X q = StrongURP X (q := q) := by
  let permStep : ProbStep (Equiv.Perm X) (Bidirectional X q).I (Bidirectional X q).X
      (Bidirectional X q).Y :=
    fun π i => match i with
      | .forward => fun x => (ProbDist.single (π x)).map fun y => (π, y)
      | .inverse => fun y => (ProbDist.single (π.symm y)).map fun x => (π, x)
  have hsim := TypedSystem.ofProbAutomaton_eq_of_simulation (A := Bidirectional X q)
    (lazyStrongURPStep q) permStep completionLaw
    (fun _ table => (completions table).Nonempty)
    (by
      intro _ table ⟨i, x⟩ h _ p hp
      cases i with
      | forward =>
        simp only [ProbStep.outcome, lazyStrongURPStep] at hp
        cases hl : lookupForward table x with
        | none =>
          simp only [hl, ProbDist.map_val, fTransform_fTransform, Function.comp_def] at hp
          obtain ⟨y, hy, rfl⟩ := mem_support_fTransform _ _ hp
          exact completions_append_nonempty_forward table h x hl y hy
        | some y =>
          simp only [hl, ProbDist.single, fTransform_single, Finsupp.support_single _ one_ne_zero,
            Finset.mem_singleton] at hp
          rw [hp]
          exact h
      | inverse =>
        simp only [ProbStep.outcome, lazyStrongURPStep] at hp
        cases hl : lookupInverse table x with
        | none =>
          simp only [hl, ProbDist.map_val, fTransform_fTransform, Function.comp_def] at hp
          obtain ⟨w, hw, rfl⟩ := mem_support_fTransform _ _ hp
          exact completions_append_nonempty_inverse table h x hl w hw
        | some w =>
          simp only [hl, ProbDist.single, fTransform_single, Finsupp.support_single _ one_ne_zero,
            Finset.mem_singleton] at hp
          rw [hp]
          exact h)
    (by
      intro _ table ⟨i, x⟩ h _
      cases i with
      | forward =>
        simp only [ProbStep.SimulatesAt, ProbStep.outcome, permStep, lazyStrongURPStep,
          ProbDist.map_val, ProbDist.single, fTransform_single]
        rw [bindK_single_comp]
        cases hl : lookupForward table x with
        | none =>
          simp only [ProbDist.map_val, fTransform_fTransform, Function.comp_def, bindK_fTransform,
            ProbStep.tagged]
          have hdis := congrArg Subtype.val (completionLaw_eq_bind_forward table h x hl)
          rw [hdis, ProbDist.bind_val, fTransform_bindK]
          apply bindK_congr
          intro y hy
          apply fTransform_congr_support
          intro π hπ
          have hnew := completions_append_nonempty_forward table h x hl y hy
          have hpin := ((mem_completions_append_iff table x y π).mp
            ((mem_support_completionLaw_iff _ hnew π).mp hπ)).2
          rw [hpin]
        | some y =>
          simp only [fTransform_single, bindK_single, one_smul, ProbStep.tagged]
          apply fTransform_congr_support
          intro π hπ
          have hm := mem_of_lookupForward_eq_some hl
          rw [(mem_completions_iff table π).mp ((mem_support_completionLaw_iff table h π).mp hπ)
            (x, y) hm]
      | inverse =>
        simp only [ProbStep.SimulatesAt, ProbStep.outcome, permStep, lazyStrongURPStep,
          ProbDist.map_val, ProbDist.single, fTransform_single]
        rw [bindK_single_comp]
        cases hl : lookupInverse table x with
        | none =>
          simp only [ProbDist.map_val, fTransform_fTransform, Function.comp_def, bindK_fTransform,
            ProbStep.tagged]
          have hdis := congrArg Subtype.val (completionLaw_eq_bind_inverse table h x hl)
          rw [hdis, ProbDist.bind_val, fTransform_bindK]
          apply bindK_congr
          intro w hw
          apply fTransform_congr_support
          intro π hπ
          have hnew := completions_append_nonempty_inverse table h x hl w hw
          have hpin := ((mem_completions_append_iff table w x π).mp
            ((mem_support_completionLaw_iff _ hnew π).mp hπ)).2
          have hsym : π.symm x = w := by rw [← hpin, π.symm_apply_apply]
          rw [hsym]
        | some w =>
          simp only [fTransform_single, bindK_single, one_smul, ProbStep.tagged]
          apply fTransform_congr_support
          intro π hπ
          have hm := mem_of_lookupInverse_eq_some hl
          have hpin := (mem_completions_iff table π).mp
            ((mem_support_completionLaw_iff table h π).mp hπ) (w, x) hm
          dsimp only at hpin
          have hsym : π.symm x = w := by rw [← hpin, π.symm_apply_apply]
          rw [hsym])
    (ProbDist.single [])
    (by
      intro table ht
      have ht' : table = [] := by
        simpa only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
          Finset.mem_singleton] using ht
      subst ht'
      exact completions_nonempty_of_isPartialBijection isPartialBijection_nil)
  have hinit : (ProbDist.single []).bind completionLaw = 𝒰[Equiv.Perm X] := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.single, bindK_single, one_smul]
    exact congrArg Subtype.val (ProbDist.uniformOn_of_forall _
      (fun π => (mem_completions_iff [] π).mpr fun _ hm => by cases hm) _)
  rw [hinit] at hsim
  have hpermEq :
      TypedSystem.ofProbAutomaton (Bidirectional X q) permStep 𝒰[Equiv.Perm X] =
        StrongURP X (q := q) := by
    let reply : Equiv.Perm X → (i : (Bidirectional X q).I) → (Bidirectional X q).X i →
        (Bidirectional X q).Y i :=
      fun π i => match i with
        | .forward => fun x => π x
        | .inverse => fun y => π.symm y
    have hstepEq : permStep = fun π i x => (ProbDist.single (reply π i x)).map fun y => (π, y) := by
      funext π i x
      cases i <;> rfl
    rw [hstepEq, TypedSystem.ofProbAutomaton_eq_keyed (A := Bidirectional X q)
      𝒰[Equiv.Perm X] (fun π i x => ProbDist.single (reply π i x)),
      TypedSystem.keyed_single (A := Bidirectional X q) 𝒰[Equiv.Perm X] reply]
    rfl
  exact hsim.trans hpermEq

end LazyStrongURP

/-! ### Rejection sampling identity -/

section RejectionSampling

variable {X : Type} [Fintype X] [Nonempty X]

open Classical in
/-- Drawing `r ∼ 𝒰[X]` and resampling from `uniformOn P` whenever `¬ P r` yields `uniformOn P`. -/
lemma rejection_resample_eq_uniformOn (P : X → Prop) (hEx : ∃ a : X, P a) :
    (𝒰[X].bind fun r => if P r then ProbDist.single r else ProbDist.uniformOn P 𝒰[X]) =
      ProbDist.uniformOn P 𝒰[X] := by
  have hP : (Finset.univ.filter P).Nonempty := by
    obtain ⟨a, ha⟩ := hEx
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  apply Subtype.ext
  ext x
  rw [ProbDist.bind_val, bindK_apply]
  have hU_pos : (0 : ℝ) < ((Finset.univ.filter P).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hP
  have hX_pos : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := X)
  have hunif (y : X) : (ProbDist.uniformOn P 𝒰[X]).1 y =
      if P y then 1 / ((Finset.univ.filter P).card : ℝ) else 0 := by
    unfold ProbDist.uniformOn
    have hne : ((Distribution.uniform X).restrict P).weight ≠ 0 :=
      weight_restrict_uniform_ne_zero P hEx
    rw [normalizeOr_val_of_weight_ne_zero _ _ _ hne, Finsupp.smul_apply, smul_eq_mul,
      weight_restrict, Distribution.uniform_mass_eq_card_filter, restrict_apply]
    split_ifs with hPy
    · simp only [Distribution.uniform_apply]
      field_simp [ne_of_gt hX_pos, ne_of_gt hU_pos]
    · simp only [mul_zero]
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp only [zero_mul])]
  have hsplit : ∑ r : X, (𝒰[X] : ProbDist X).1 r *
        (if P r then ProbDist.single r else ProbDist.uniformOn P 𝒰[X]).1 x =
      (1 / (Fintype.card X : ℝ)) *
        ∑ r : X, (if P r then (ProbDist.single r).1 x else (ProbDist.uniformOn P 𝒰[X]).1 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [ProbDist.uniform, Distribution.uniform_apply]
    split_ifs <;> rfl
  rw [hsplit]
  have hpart :
      (∑ r : X, (if P r then (ProbDist.single r).1 x else (ProbDist.uniformOn P 𝒰[X]).1 x)) =
        (∑ r ∈ Finset.univ.filter P, (ProbDist.single r).1 x) +
          (∑ r ∈ Finset.univ.filter (fun r => ¬ P r), (ProbDist.uniformOn P 𝒰[X]).1 x) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P]
    congr 1
    · exact Finset.sum_congr rfl fun r hr => ite_eq_left (Finset.mem_filter.mp hr).2
    · exact Finset.sum_congr rfl fun r hr => ite_eq_right (Finset.mem_filter.mp hr).2
  rw [hpart, Finset.sum_const, nsmul_eq_mul, hunif x]
  have hcompl : ((Finset.univ.filter fun r => ¬ P r).card : ℝ) =
      (Fintype.card X : ℝ) - ((Finset.univ.filter P).card : ℝ) := by
    have hadd := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset X) P (fun _ => (1 : ℝ))
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at hadd
    linarith
  by_cases hPx : P x
  · rw [ite_eq_left hPx]
    have hsing : (∑ r ∈ Finset.univ.filter P, (ProbDist.single r).1 x) = 1 := by
      rw [Finset.sum_eq_single x]
      · simp only [ProbDist.single, Finsupp.single_eq_same]
      · intro r _ hrx
        simp only [ProbDist.single, Finsupp.single_eq_of_ne hrx.symm]
      · intro hx
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hPx⟩) hx
    rw [hsing, hcompl]
    field_simp [ne_of_gt hX_pos, ne_of_gt hU_pos]
    ring
  · rw [ite_eq_right hPx]
    have hsing : (∑ r ∈ Finset.univ.filter P, (ProbDist.single r).1 x) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have hne : r ≠ x := fun hrx => hPx (hrx ▸ (Finset.mem_filter.mp hr).2)
      simp only [ProbDist.single, Finsupp.single_eq_of_ne hne.symm]
    rw [hsing, mul_zero, add_zero, mul_zero]

end RejectionSampling

/-! ### Lazy bidirectional random function and rejection-coin game -/

section Games

variable {X : Type} [Fintype X] [Nonempty X]

open Classical in
/-- Transition step of `LazyBidirectionalRF`: replay hits; on fresh forward/inverse queries draw
uniformly from `X` and record the pair when it does not collide with the existing table.
A collision is returned without insertion; repeating that fresh query samples again. -/
noncomputable def lazyBidirectionalRFStep (q : ℕ) :
    ProbStep (List (X × X)) (Bidirectional X q).I (Bidirectional X q).X (Bidirectional X q).Y
  | table, .forward, x =>
    match lookupForward table x with
    | some y => ProbDist.single (table, y)
    | none => 𝒰[X].map fun y =>
        if y ∉ table.map Prod.snd then (table ++ [(x, y)], y) else (table, y)
  | table, .inverse, y =>
    match lookupInverse table y with
    | some x => ProbDist.single (table, x)
    | none => 𝒰[X].map fun x =>
        if x ∉ table.map Prod.fst then (table ++ [(x, y)], x) else (table, x)

open Classical in
/-- Collision-monitoring game step for `LazyBidirectionalRF`: sets the monotone flag when a fresh
draw collides with the recorded range/domain. -/
noncomputable def lazyBidirectionalRFGameStep (q : ℕ) :
    ProbStep (List (X × X) × Bool) (Bidirectional X q).I (Bidirectional X q).X
      (withMBO (Bidirectional X q).Y)
  | (table, bad), .forward, x =>
    match lookupForward table x with
    | some y => ProbDist.single ((table, bad), (y, bad))
    | none => 𝒰[X].map fun y =>
        if y ∉ table.map Prod.snd then ((table ++ [(x, y)], bad), (y, bad))
        else ((table, true), (y, true))
  | (table, bad), .inverse, y =>
    match lookupInverse table y with
    | some x => ProbDist.single ((table, bad), (x, bad))
    | none => 𝒰[X].map fun x =>
        if x ∉ table.map Prod.fst then ((table ++ [(x, y)], bad), (x, bad))
        else ((table, true), (x, true))

open Classical in
/-- Rejection-coin game step for `StrongURP`: draws `r ∼ 𝒰[X]`; if `r` collides with the recorded
range/domain, resamples from the unused set and sets the monotone flag. -/
noncomputable def strongURPRejectionGameStep (q : ℕ) :
    ProbStep (List (X × X) × Bool) (Bidirectional X q).I (Bidirectional X q).X
      (withMBO (Bidirectional X q).Y)
  | (table, bad), .forward, x =>
    match lookupForward table x with
    | some y => ProbDist.single ((table, bad), (y, bad))
    | none => 𝒰[X].bind fun y =>
        if y ∉ table.map Prod.snd then ProbDist.single ((table ++ [(x, y)], bad), (y, bad))
        else (unusedForwardLaw table).map fun y' => ((table ++ [(x, y')], true), (y', true))
  | (table, bad), .inverse, y =>
    match lookupInverse table y with
    | some x => ProbDist.single ((table, bad), (x, bad))
    | none => 𝒰[X].bind fun x =>
        if x ∉ table.map Prod.fst then ProbDist.single ((table ++ [(x, y)], bad), (x, bad))
        else (unusedInverseLaw table).map fun x' => ((table ++ [(x', y)], true), (x', true))

open Classical in
lemma lazyBidirectionalRFGameStep_flag (q : ℕ) (table : List (X × X)) (b : Bool)
    (i : (Bidirectional X q).I) (x : (Bidirectional X q).X i)
    (p : (List (X × X) × Bool) × ((Bidirectional X q).Y i × Bool))
    (hp : p ∈ (lazyBidirectionalRFGameStep q (table, b) i x).1.support) :
    p.2.2 = p.1.2 ∧ (b = true → p.1.2 = true) := by
  cases i with
  | forward =>
    simp only [lazyBidirectionalRFGameStep] at hp
    cases hl : lookupForward table x with
    | some y =>
      simp only [hl, ProbDist.single, Finsupp.support_single _ one_ne_zero,
        Finset.mem_singleton] at hp
      rw [hp]
      exact ⟨rfl, id⟩
    | none =>
      simp only [hl, ProbDist.map_val] at hp
      obtain ⟨y, _, rfl⟩ := mem_support_fTransform _ _ hp
      split_ifs <;> exact ⟨rfl, fun hb => by first | exact hb | rfl⟩
  | inverse =>
    simp only [lazyBidirectionalRFGameStep] at hp
    cases hl : lookupInverse table x with
    | some w =>
      simp only [hl, ProbDist.single, Finsupp.support_single _ one_ne_zero,
        Finset.mem_singleton] at hp
      rw [hp]
      exact ⟨rfl, id⟩
    | none =>
      simp only [hl, ProbDist.map_val] at hp
      obtain ⟨w, _, rfl⟩ := mem_support_fTransform _ _ hp
      split_ifs <;> exact ⟨rfl, fun hb => by first | exact hb | rfl⟩

open Classical in
lemma strongURPRejectionGameStep_flag (q : ℕ) (table : List (X × X)) (b : Bool)
    (i : (Bidirectional X q).I) (x : (Bidirectional X q).X i)
    (p : (List (X × X) × Bool) × ((Bidirectional X q).Y i × Bool))
    (hp : p ∈ (strongURPRejectionGameStep q (table, b) i x).1.support) :
    p.2.2 = p.1.2 ∧ (b = true → p.1.2 = true) := by
  cases i with
  | forward =>
    simp only [strongURPRejectionGameStep] at hp
    cases hl : lookupForward table x with
    | some y =>
      rw [hl] at hp
      simp only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
        Finset.mem_singleton] at hp
      rw [hp]
      exact ⟨rfl, id⟩
    | none =>
      rw [hl] at hp
      rw [ProbDist.bind_val] at hp
      have hne := Finsupp.mem_support_iff.mp hp
      rw [bindK_apply] at hne
      obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hp' := Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hy)
      by_cases hfresh : y ∉ table.map Prod.snd
      · rw [ite_eq_left hfresh] at hp'
        simp only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
          Finset.mem_singleton] at hp'
        rw [hp']
        exact ⟨rfl, id⟩
      · rw [ite_eq_right hfresh] at hp'
        simp only [ProbDist.map_val] at hp'
        obtain ⟨y', _, rfl⟩ := mem_support_fTransform _ _ hp'
        exact ⟨rfl, fun _ => rfl⟩
  | inverse =>
    simp only [strongURPRejectionGameStep] at hp
    cases hl : lookupInverse table x with
    | some w =>
      rw [hl] at hp
      simp only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
        Finset.mem_singleton] at hp
      rw [hp]
      exact ⟨rfl, id⟩
    | none =>
      rw [hl] at hp
      rw [ProbDist.bind_val] at hp
      have hne := Finsupp.mem_support_iff.mp hp
      rw [bindK_apply] at hne
      obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hp' := Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hw)
      by_cases hfresh : w ∉ table.map Prod.fst
      · rw [ite_eq_left hfresh] at hp'
        simp only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
          Finset.mem_singleton] at hp'
        rw [hp']
        exact ⟨rfl, id⟩
      · rw [ite_eq_right hfresh] at hp'
        simp only [ProbDist.map_val] at hp'
        obtain ⟨w', _, rfl⟩ := mem_support_fTransform _ _ hp'
        exact ⟨rfl, fun _ => rfl⟩

open Classical in
/-- Step a partial bijection table along a single visible `Bidirectional` query/reply pair; returns
`none` if the pair conflicts with the table or collides on a fresh query. -/
noncomputable def stepBijection (q : ℕ) (table : List (X × X))
    (z : (Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i) :
    Option (List (X × X)) :=
  match z with
  | (⟨.forward, x⟩, ⟨.forward, y⟩) =>
    match lookupForward table x with
    | some y' => if y' = y then some table else none
    | none => if y ∉ table.map Prod.snd then some (table ++ [(x, y)]) else none
  | (⟨.inverse, y⟩, ⟨.inverse, x⟩) =>
    match lookupInverse table y with
    | some x' => if x' = x then some table else none
    | none => if x ∉ table.map Prod.fst then some (table ++ [(x, y)]) else none
  | _ => none

open Classical in
/-- Fold `stepBijection` along a visible `Bidirectional` transcript, returning `some table` iff the
transcript is collision-free and consistent with the partial bijection `table`. -/
noncomputable def transcriptBijection (q : ℕ)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)) :
    Option (List (X × X)) :=
  h.foldl (fun acc z => acc.bind fun table => stepBijection q table z) (some [])

omit [Nonempty X] in
open Classical in
lemma transcriptBijection_append_singleton (q : ℕ)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (z : (Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i) :
    transcriptBijection q (h ++ [z]) =
      (transcriptBijection q h).bind fun table => stepBijection q table z := by
  simp only [transcriptBijection, List.foldl_append, List.foldl_cons, List.foldl_nil]

omit [Nonempty X] in
open Classical in
lemma stepBijection_isPartialBijection {q : ℕ} {table table' : List (X × X)}
    (hb : IsPartialBijection table)
    (z : (Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)
    (hs : stepBijection q table z = some table') :
    IsPartialBijection table' ∧
      (table'.length = table.length ∨ table'.length = table.length + 1) := by
  rcases z with ⟨⟨p1, a⟩, ⟨p2, b⟩⟩
  cases p1 <;> cases p2
  · simp only [stepBijection] at hs
    cases hl : lookupForward table a with
    | some y' =>
      rw [hl] at hs
      dsimp only at hs
      by_cases heq : y' = b
      · rw [ite_eq_left heq] at hs
        cases hs
        exact ⟨hb, Or.inl rfl⟩
      · rw [ite_eq_right heq] at hs
        cases hs
    | none =>
      rw [hl] at hs
      dsimp only at hs
      by_cases hfresh : b ∉ table.map Prod.snd
      · rw [ite_eq_left hfresh] at hs
        cases hs
        exact ⟨isPartialBijection_append hb ((lookupForward_eq_none_iff table a).mp hl) hfresh,
          Or.inr (by simp only [List.length_append, List.length_singleton])⟩
      · rw [ite_eq_right hfresh] at hs
        cases hs
  · cases hs
  · cases hs
  · simp only [stepBijection] at hs
    cases hl : lookupInverse table a with
    | some x' =>
      rw [hl] at hs
      dsimp only at hs
      by_cases heq : x' = b
      · rw [ite_eq_left heq] at hs
        cases hs
        exact ⟨hb, Or.inl rfl⟩
      · rw [ite_eq_right heq] at hs
        cases hs
    | none =>
      rw [hl] at hs
      dsimp only at hs
      by_cases hfresh : b ∉ table.map Prod.fst
      · rw [ite_eq_left hfresh] at hs
        cases hs
        exact ⟨isPartialBijection_append hb hfresh ((lookupInverse_eq_none_iff table a).mp hl),
          Or.inr (by simp only [List.length_append, List.length_singleton])⟩
      · rw [ite_eq_right hfresh] at hs
        cases hs

omit [Nonempty X] in
open Classical in
lemma transcriptBijection_isPartialBijection {q : ℕ}
    {h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)}
    {table : List (X × X)} (ht : transcriptBijection q h = some table) :
    IsPartialBijection table ∧ table.length ≤ h.length := by
  induction h using List.reverseRecOn generalizing table with
  | nil =>
    simp only [transcriptBijection, List.foldl_nil, Option.some.injEq] at ht
    subst ht
    exact ⟨isPartialBijection_nil, le_rfl⟩
  | append_singleton h z ih =>
    rw [transcriptBijection_append_singleton] at ht
    cases hprev : transcriptBijection q h with
    | none => simp only [hprev, Option.bind_none, reduceCtorEq] at ht
    | some prev =>
      simp only [hprev, Option.bind_some] at ht
      obtain ⟨hbp, hlp⟩ := ih hprev
      obtain ⟨hbt, hlt⟩ := stepBijection_isPartialBijection hbp z ht
      refine ⟨hbt, ?_⟩
      simp only [List.length_append, List.length_singleton]
      rcases hlt with heq | hsucc <;> omega

open Classical in
/-- Exact single-state unset transition formula shared by BOTH `lazyBidirectionalRFGameStep` and
`strongURPRejectionGameStep`. -/
lemma unset_transition_single (q : ℕ) (table : List (X × X))
    (z : (Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i) :
    let d : Distribution (List (X × X) × Bool) :=
      match stepBijection q table z with
      | some table' =>
        if table'.length = table.length then
          (ProbDist.single (table', false)).1
        else
          (1 / (Fintype.card X : ℝ)) • (ProbDist.single (table', false)).1
      | none => 0
    (lazyBidirectionalRFGameStep q).transition (ProbDist.single (table, false)).1 z.1
        (tagMBO false z.2) = d ∧
      (strongURPRejectionGameStep q).transition (ProbDist.single (table, false)).1 z.1
        (tagMBO false z.2) = d := by
  intro d
  have hsingle_eq (step : ProbStep (List (X × X) × Bool) (Bidirectional X q).I
      (Bidirectional X q).X (withMBO (Bidirectional X q).Y)) :
      step.transition (ProbDist.single (table, false)).1 z.1 (tagMBO false z.2) =
        fTransform Prod.fst
          ((step.outcome (table, false) z.1).restrict fun sy => sy.2 = tagMBO false z.2) := by
    simp only [ProbStep.transition, ProbDist.single, bindK_single, one_smul]
  rw [hsingle_eq, hsingle_eq]
  have hcheck (step : ProbStep (List (X × X) × Bool) (Bidirectional X q).I
      (Bidirectional X q).X (withMBO (Bidirectional X q).Y))
      (hspec : ∀ (s' : List (X × X) × Bool),
        (step (table, false) z.1.1 z.1.2).1.mass (fun p =>
          p.1 = s' ∧ (⟨z.1.1, p.2⟩ : Σ i, withMBO (Bidirectional X q).Y i) =
            tagMBO false z.2) = d s') :
      fTransform Prod.fst
        ((step.outcome (table, false) z.1).restrict fun sy => sy.2 = tagMBO false z.2) = d := by
    ext s'
    rw [fTransform_apply_eq_mass, mass_restrict, ProbStep.outcome, mass_fTransform]
    exact hspec s'
  constructor
  · apply hcheck
    intro s'
    rcases z with ⟨⟨p1, a⟩, ⟨p2, b⟩⟩
    cases p1 <;> cases p2
    · -- forward, forward
      simp only [lazyBidirectionalRFGameStep, d, stepBijection]
      cases hl : lookupForward table a with
      | some y' =>
        simp only [ProbDist.single, mass_single, tagMBO, Sigma.mk.injEq, heq_eq_eq, true_and,
          Prod.mk.injEq, and_true]
        by_cases heq : y' = b
        · subst heq
          simp only [↓reduceIte, Finsupp.single_apply]
          by_cases hs : (table, false) = s' <;> simp [hs]
        · simp only [heq, ↓reduceIte, Finsupp.zero_apply, and_false]
      | none =>
        simp only [ProbDist.map_val, mass_fTransform, ProbDist.uniform, tagMBO, Sigma.mk.injEq,
          heq_eq_eq, true_and]
        by_cases hfresh : b ∉ table.map Prod.snd
        · rw [ite_eq_left hfresh]
          dsimp only
          simp only [List.length_append, List.length_singleton, Nat.add_eq_left, one_ne_zero,
            ↓reduceIte, Finsupp.smul_apply, ProbDist.single, smul_eq_mul, Finsupp.single_apply]
          have hpred : (fun y : X =>
              (if y ∉ table.map Prod.snd then (table ++ [(a, y)], false) else (table, true)) = s' ∧
              (if y ∉ table.map Prod.snd then (y, false) else (y, true)) = (b, false)) =
              (fun y : X => (table ++ [(a, b)], false) = s' ∧ y = b) := by
            funext y
            apply propext
            by_cases hy : y ∉ table.map Prod.snd
            · rw [ite_eq_left hy, ite_eq_left hy]
              simp only [Prod.mk.injEq, and_true]
              exact ⟨fun ⟨hs, hyb⟩ => ⟨hyb ▸ hs, hyb⟩, fun ⟨hs, hyb⟩ => ⟨hyb.symm ▸ hs, hyb⟩⟩
            · rw [ite_eq_right hy, ite_eq_right hy]
              simp only [Prod.mk.injEq, Bool.true_eq_false, and_false, false_iff, not_and]
              intro _ hyb
              exact hy (hyb ▸ hfresh)
          have hcast :
              (Distribution.uniform X).mass (fun y : X =>
                (if y ∉ table.map Prod.snd then ((table ++ [(a, y)], false), (y, false))
                  else ((table, true), (y, true))).1 = s' ∧
                (if y ∉ table.map Prod.snd then ((table ++ [(a, y)], false), (y, false))
                  else ((table, true), (y, true))).2 = (b, false)) =
              (Distribution.uniform X).mass (fun y : X =>
                (table ++ [(a, b)], false) = s' ∧ y = b) := by
            rw [← hpred]
            apply mass_congr
            intro y
            by_cases hy : y ∉ table.map Prod.snd
            · rw [ite_eq_left hy, ite_eq_left hy, ite_eq_left hy]
            · rw [ite_eq_right hy, ite_eq_right hy, ite_eq_right hy]
          rw [hcast]
          by_cases hs : (table ++ [(a, b)], false) = s'
          · rw [ite_eq_left hs, mul_one]
            simp only [hs, true_and, Distribution.mass_singleton, Distribution.uniform_apply]
          · rw [ite_eq_right hs, mul_zero]
            exact mass_eq_zero_of_forall_not _ (fun _ h => hs h.1)
        · rw [ite_eq_right hfresh]
          dsimp only
          simp only [Finsupp.zero_apply]
          apply mass_eq_zero_of_forall_not
          intro y hy
          by_cases hfy : y ∉ table.map Prod.snd
          · rw [ite_eq_left hfy] at hy
            exact hfresh ((Prod.mk.inj hy.2).1 ▸ hfy)
          · rw [ite_eq_right hfy] at hy
            exact Bool.false_ne_true (Prod.mk.inj hy.2).2.symm
    · -- forward, inverse
      simp only [d, stepBijection, tagMBO, Sigma.mk.injEq, reduceCtorEq, false_and, and_false,
        Finsupp.zero_apply]
      exact mass_eq_zero_of_forall_not _ (fun _ => id)
    · -- inverse, forward
      simp only [d, stepBijection, tagMBO, Sigma.mk.injEq, reduceCtorEq, false_and, and_false,
        Finsupp.zero_apply]
      exact mass_eq_zero_of_forall_not _ (fun _ => id)
    · -- inverse, inverse
      simp only [lazyBidirectionalRFGameStep, d, stepBijection]
      cases hl : lookupInverse table a with
      | some x' =>
        simp only [ProbDist.single, mass_single, tagMBO, Sigma.mk.injEq, heq_eq_eq, true_and,
          Prod.mk.injEq, and_true]
        by_cases heq : x' = b
        · subst heq
          simp only [↓reduceIte, Finsupp.single_apply]
          by_cases hs : (table, false) = s' <;> simp [hs]
        · simp only [heq, ↓reduceIte, Finsupp.zero_apply, and_false]
      | none =>
        simp only [ProbDist.map_val, mass_fTransform, ProbDist.uniform, tagMBO, Sigma.mk.injEq,
          heq_eq_eq, true_and]
        by_cases hfresh : b ∉ table.map Prod.fst
        · rw [ite_eq_left hfresh]
          dsimp only
          simp only [List.length_append, List.length_singleton, Nat.add_eq_left, one_ne_zero,
            ↓reduceIte, Finsupp.smul_apply, ProbDist.single, smul_eq_mul, Finsupp.single_apply]
          have hpred : (fun x : X =>
              (if x ∉ table.map Prod.fst then (table ++ [(x, a)], false) else (table, true)) = s' ∧
              (if x ∉ table.map Prod.fst then (x, false) else (x, true)) = (b, false)) =
              (fun x : X => (table ++ [(b, a)], false) = s' ∧ x = b) := by
            funext x
            apply propext
            by_cases hx : x ∉ table.map Prod.fst
            · rw [ite_eq_left hx, ite_eq_left hx]
              simp only [Prod.mk.injEq, and_true]
              exact ⟨fun ⟨hs, hxb⟩ => ⟨hxb ▸ hs, hxb⟩, fun ⟨hs, hxb⟩ => ⟨hxb.symm ▸ hs, hxb⟩⟩
            · rw [ite_eq_right hx, ite_eq_right hx]
              simp only [Prod.mk.injEq, Bool.true_eq_false, and_false, false_iff, not_and]
              intro _ hxb
              exact hx (hxb ▸ hfresh)
          have hcast :
              (Distribution.uniform X).mass (fun x : X =>
                (if x ∉ table.map Prod.fst then ((table ++ [(x, a)], false), (x, false))
                  else ((table, true), (x, true))).1 = s' ∧
                (if x ∉ table.map Prod.fst then ((table ++ [(x, a)], false), (x, false))
                  else ((table, true), (x, true))).2 = (b, false)) =
              (Distribution.uniform X).mass (fun x : X =>
                (table ++ [(b, a)], false) = s' ∧ x = b) := by
            rw [← hpred]
            apply mass_congr
            intro x
            by_cases hx : x ∉ table.map Prod.fst
            · rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx]
            · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx]
          rw [hcast]
          by_cases hs : (table ++ [(b, a)], false) = s'
          · rw [ite_eq_left hs, mul_one]
            simp only [hs, true_and, Distribution.mass_singleton, Distribution.uniform_apply]
          · rw [ite_eq_right hs, mul_zero]
            exact mass_eq_zero_of_forall_not _ (fun _ h => hs h.1)
        · rw [ite_eq_right hfresh]
          dsimp only
          simp only [Finsupp.zero_apply]
          apply mass_eq_zero_of_forall_not
          intro x hx
          by_cases hfx : x ∉ table.map Prod.fst
          · rw [ite_eq_left hfx] at hx
            exact hfresh ((Prod.mk.inj hx.2).1 ▸ hfx)
          · rw [ite_eq_right hfx] at hx
            exact Bool.false_ne_true (Prod.mk.inj hx.2).2.symm
  · apply hcheck
    intro s'
    rcases z with ⟨⟨p1, a⟩, ⟨p2, b⟩⟩
    cases p1 <;> cases p2
    · -- forward, forward
      simp only [strongURPRejectionGameStep, d, stepBijection]
      cases hl : lookupForward table a with
      | some y' =>
        simp only [ProbDist.single, mass_single, tagMBO, Sigma.mk.injEq, heq_eq_eq, true_and,
          Prod.mk.injEq, and_true]
        by_cases heq : y' = b
        · subst heq
          simp only [↓reduceIte, Finsupp.single_apply]
          by_cases hs : (table, false) = s' <;> simp [hs]
        · simp only [heq, ↓reduceIte, Finsupp.zero_apply, and_false]
      | none =>
        rw [ProbDist.bind_val, mass_bindK]
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp only [zero_mul])]
        simp only [ProbDist.uniform, Distribution.uniform_apply, tagMBO, Sigma.mk.injEq,
          heq_eq_eq, true_and]
        have hterm (y : X) :
            (if y ∉ table.map Prod.snd then
              ProbDist.single ((table ++ [(a, y)], false), (y, false))
            else (unusedForwardLaw table).map fun y' =>
              ((table ++ [(a, y')], true), (y', true))).1.mass
              (fun p => p.1 = s' ∧ p.2 = (b, false)) =
            if y ∉ table.map Prod.snd ∧ (table ++ [(a, y)], false) = s' ∧ y = b then 1 else 0 := by
          by_cases hy : y ∉ table.map Prod.snd
          · rw [ite_eq_left hy]
            simp only [ProbDist.single, mass_single, Prod.mk.injEq, and_true, hy]
            by_cases h1 : (table ++ [(a, y)], false) = s' ∧ y = b <;> simp [h1]
          · have hfalse : ¬ (y ∉ table.map Prod.snd ∧ (table ++ [(a, y)], false) = s' ∧ y = b) :=
              fun hc => hy hc.1
            rw [ite_eq_right hy, ite_eq_right hfalse]
            simp only [ProbDist.map_val, mass_fTransform, Prod.mk.injEq, Bool.true_eq_false,
              and_false]
            exact mass_eq_zero_of_forall_not _ (fun _ => id)
        simp only [hterm]
        by_cases hfresh : b ∉ table.map Prod.snd
        · rw [ite_eq_left hfresh]
          dsimp only
          simp only [List.length_append, List.length_singleton, Nat.add_eq_left, one_ne_zero,
            ↓reduceIte, Finsupp.smul_apply, ProbDist.single, smul_eq_mul, Finsupp.single_apply]
          rw [Finset.sum_eq_single b]
          · by_cases hs : (table ++ [(a, b)], false) = s' <;> simp [hfresh, hs]
          · intro y _ hyb
            simp [hyb]
          · intro hb
            exact absurd (Finset.mem_univ b) hb
        · simp only [hfresh, ↓reduceIte, Finsupp.zero_apply]
          apply Finset.sum_eq_zero
          intro y _
          have hno : ¬ (y ∉ table.map Prod.snd ∧ (table ++ [(a, y)], false) = s' ∧ y = b) := by
            rintro ⟨hy, _, rfl⟩
            exact hfresh hy
          rw [ite_eq_right hno, mul_zero]
    · -- forward, inverse
      simp only [d, stepBijection, tagMBO, Sigma.mk.injEq, reduceCtorEq, false_and, and_false,
        Finsupp.zero_apply]
      exact mass_eq_zero_of_forall_not _ (fun _ => id)
    · -- inverse, forward
      simp only [d, stepBijection, tagMBO, Sigma.mk.injEq, reduceCtorEq, false_and, and_false,
        Finsupp.zero_apply]
      exact mass_eq_zero_of_forall_not _ (fun _ => id)
    · -- inverse, inverse
      simp only [strongURPRejectionGameStep, d, stepBijection]
      cases hl : lookupInverse table a with
      | some x' =>
        simp only [ProbDist.single, mass_single, tagMBO, Sigma.mk.injEq, heq_eq_eq, true_and,
          Prod.mk.injEq, and_true]
        by_cases heq : x' = b
        · subst heq
          simp only [↓reduceIte, Finsupp.single_apply]
          by_cases hs : (table, false) = s' <;> simp [hs]
        · simp only [heq, ↓reduceIte, Finsupp.zero_apply, and_false]
      | none =>
        rw [ProbDist.bind_val, mass_bindK]
        rw [Finsupp.sum_fintype _ _ (fun _ => by simp only [zero_mul])]
        simp only [ProbDist.uniform, Distribution.uniform_apply, tagMBO, Sigma.mk.injEq,
          heq_eq_eq, true_and]
        have hterm (x : X) :
            (if x ∉ table.map Prod.fst then
              ProbDist.single ((table ++ [(x, a)], false), (x, false))
            else (unusedInverseLaw table).map fun x' =>
              ((table ++ [(x', a)], true), (x', true))).1.mass
              (fun p => p.1 = s' ∧ p.2 = (b, false)) =
            if x ∉ table.map Prod.fst ∧ (table ++ [(x, a)], false) = s' ∧ x = b then 1 else 0 := by
          by_cases hx : x ∉ table.map Prod.fst
          · rw [ite_eq_left hx]
            simp only [ProbDist.single, mass_single, Prod.mk.injEq, and_true, hx]
            by_cases h1 : (table ++ [(x, a)], false) = s' ∧ x = b <;> simp [h1]
          · have hfalse : ¬ (x ∉ table.map Prod.fst ∧ (table ++ [(x, a)], false) = s' ∧ x = b) :=
              fun hc => hx hc.1
            rw [ite_eq_right hx, ite_eq_right hfalse]
            simp only [ProbDist.map_val, mass_fTransform, Prod.mk.injEq, Bool.true_eq_false,
              and_false]
            exact mass_eq_zero_of_forall_not _ (fun _ => id)
        simp only [hterm]
        by_cases hfresh : b ∉ table.map Prod.fst
        · rw [ite_eq_left hfresh]
          dsimp only
          simp only [List.length_append, List.length_singleton, Nat.add_eq_left, one_ne_zero,
            ↓reduceIte, Finsupp.smul_apply, ProbDist.single, smul_eq_mul, Finsupp.single_apply]
          rw [Finset.sum_eq_single b]
          · by_cases hs : (table ++ [(b, a)], false) = s' <;> simp [hfresh, hs]
          · intro x _ hxb
            simp [hxb]
          · intro hb
            exact absurd (Finset.mem_univ b) hb
        · simp only [hfresh, ↓reduceIte, Finsupp.zero_apply]
          apply Finset.sum_eq_zero
          intro x _
          have hno : ¬ (x ∉ table.map Prod.fst ∧ (table ++ [(x, a)], false) = s' ∧ x = b) := by
            rintro ⟨hx, _, rfl⟩
            exact hfresh hx
          rw [ite_eq_right hno, mul_zero]

open Classical in
lemma transition_smul {S' I : Type} {A' B' : I → Type} (step : ProbStep S' I A' B')
    (c : ℝ) (β : Distribution S') (x : Σ i, A' i) (y : Σ i, B' i) :
    step.transition (c • β) x y = c • step.transition β x y := by
  ext s'
  simp only [ProbStep.transition, bindK_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index' (fun _ => by simp only [zero_mul])]
  simp only [Finsupp.sum, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

open Classical in
/-- Exact unset-MBO belief formula for BOTH `lazyBidirectionalRFGameStep` and
`strongURPRejectionGameStep` on any transcript `h`. -/
lemma unset_belief_eq (q : ℕ)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)) :
    let target : Distribution (List (X × X) × Bool) :=
      if h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst) then
        match transcriptBijection q h with
        | some table =>
          (1 / (Fintype.card X : ℝ) ^ table.length) • (ProbDist.single (table, false)).1
        | none => 0
      else 0
    (lazyBidirectionalRFGameStep q).belief (Bidirectional X q).withMBO.inputDomain
        (ProbDist.single ([], false)).1 (unsetMBOs h) = target ∧
      (strongURPRejectionGameStep q).belief (Bidirectional X q).withMBO.inputDomain
        (ProbDist.single ([], false)).1 (unsetMBOs h) = target := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [unsetMBOs, List.map_nil, ProbStep.belief_nil, true_or, ↓reduceIte,
      transcriptBijection, List.foldl_nil, List.length_nil, pow_zero, div_one, one_smul, and_self]
  | append_singleton h z ih =>
    have hunset : unsetMBOs (h ++ [z]) = unsetMBOs h ++ [(z.1, tagMBO false z.2)] := by
      simp only [unsetMBOs, List.map_append, List.map_singleton]
    have hfst : (unsetMBOs h).map Prod.fst = h.map Prod.fst := by
      simp only [unsetMBOs, List.map_map, Function.comp_def]
    have hdom : (Bidirectional X q).withMBO.inputDomain (unsetMBOs h) z.1 ↔
        (Bidirectional X q).domain (h.map Prod.fst ++ [z.1]) := by
      change (Bidirectional X q).domain ((unsetMBOs h).map Prod.fst ++ [z.1]) ↔ _
      rw [hfst]
    rw [hunset, ProbStep.belief_snoc, ProbStep.belief_snoc]
    simp only [hdom]
    have hmap : (h ++ [z]).map Prod.fst = h.map Prod.fst ++ [z.1] := by
      simp only [List.map_append, List.map_singleton]
    have hne : h ++ [z] ≠ [] := List.append_ne_nil_of_right_ne_nil h (List.cons_ne_nil _ _)
    by_cases hadm : (Bidirectional X q).domain (h.map Prod.fst ++ [z.1])
    · have hadmH : h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst) := by
        by_cases hn : h = []
        · exact Or.inl hn
        · exact Or.inr ((Bidirectional X q).nonempty_prefix.2 (List.prefix_append _ _)
            (fun he => hn (List.map_eq_nil_iff.mp he)) hadm)
      rw [ite_eq_left hadm, ite_eq_left hadm, ite_eq_left (Or.inr (hmap ▸ hadm))]
      rw [ih.1, ih.2, ite_eq_left hadmH, transcriptBijection_append_singleton]
      cases hprev : transcriptBijection q h with
      | none =>
        simp only [Option.bind_none, ProbStep.transition_zero, and_self]
      | some table =>
        simp only [Option.bind_some, transition_smul]
        have hstep := unset_transition_single q table z
        rw [hstep.1, hstep.2]
        have hbt := (transcriptBijection_isPartialBijection hprev).1
        cases hnext : stepBijection q table z with
        | none =>
          dsimp only
          simp only [smul_zero, and_self]
        | some table' =>
          dsimp only
          have ⟨_, hlen_cases⟩ := stepBijection_isPartialBijection hbt z hnext
          rcases hlen_cases with heq | hsucc
          · rw [ite_eq_left heq, heq]
            exact ⟨rfl, rfl⟩
          · have hne' : table'.length ≠ table.length := by omega
            rw [ite_eq_right hne', smul_smul, hsucc, pow_succ]
            have hpow : (1 / (Fintype.card X : ℝ) ^ table.length) *
                (1 / (Fintype.card X : ℝ)) =
                1 / ((Fintype.card X : ℝ) ^ table.length * (Fintype.card X : ℝ)) := by ring
            rw [hpow]
            exact ⟨rfl, rfl⟩
    · have hnot : ¬ (h ++ [z] = [] ∨ (Bidirectional X q).domain ((h ++ [z]).map Prod.fst)) := by
        rw [hmap]
        exact not_or.mpr ⟨hne, hadm⟩
      rw [ite_eq_right hadm, ite_eq_right hadm, ite_eq_right hnot]
      exact ⟨rfl, rfl⟩

end Games

end BidirectionalSwitching

/-! ### Public bidirectional switching API -/

section PublicAPI

open BidirectionalSwitching

variable (X : Type) [Fintype X] [Nonempty X] (q : ℕ)

open Classical in
/-- Lazy with-replacement bidirectional random function on `Bidirectional X q`: replays hits and
draws uniformly from `X` on fresh forward/inverse queries, recording non-colliding pairs. -/
noncomputable def LazyBidirectionalRF : TypedSystem (Bidirectional X q) :=
  TypedSystem.ofProbAutomaton (Bidirectional X q) (lazyBidirectionalRFStep q) (ProbDist.single [])

open Classical in
/-- Collision-monitoring game on `LazyBidirectionalRF X q`: sets the MBO when a fresh draw
collides with the recorded domain or range. -/
noncomputable def lazyBidirectionalRFGame : TypedGame (Bidirectional X q) :=
  TypedGame.ofProbAutomaton (A := Bidirectional X q) (lazyBidirectionalRFGameStep q)
    (ProbDist.single []) (lazyBidirectionalRFGameStep_flag q)

open Classical in
/-- Rejection-coin game on `StrongURP X`: draws uniformly from `X` on fresh queries, resamples
from the unused set on a collision, and sets the MBO. -/
noncomputable def strongURPRejectionGame : TypedGame (Bidirectional X q) :=
  TypedGame.ofProbAutomaton (A := Bidirectional X q) (strongURPRejectionGameStep q)
    (ProbDist.single []) (strongURPRejectionGameStep_flag q)

open Classical in
/-- Hiding the MBO of `lazyBidirectionalRFGame X q` recovers `LazyBidirectionalRF X q`. -/
theorem lazyBidirectionalRFGame_visible :
    (lazyBidirectionalRFGame X q).visible = LazyBidirectionalRF X q := by
  rw [lazyBidirectionalRFGame, TypedGame.visible_ofProbAutomaton, LazyBidirectionalRF]
  have hsim := TypedSystem.ofProbAutomaton_eq_of_simulation (A := Bidirectional X q)
    (ProbStep.forgetMBO (lazyBidirectionalRFGameStep q)) (lazyBidirectionalRFStep q)
    (fun sb => ProbDist.single sb.1) (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial)
    (by
      intro _ ⟨table, bad⟩ ⟨i, a⟩ _ _
      simp only [ProbStep.SimulatesAt, ProbStep.outcome, ProbStep.forgetMBO, ProbDist.map_val,
        ProbDist.single, fTransform_single, bindK_single, one_smul, fTransform_fTransform,
        Function.comp_def, bindK_fTransform, ProbStep.tagged]
      rw [bindK_single_comp]
      cases i with
      | forward =>
        simp only [lazyBidirectionalRFGameStep, lazyBidirectionalRFStep]
        cases hl : lookupForward table a with
        | some y =>
          dsimp only
          simp only [ProbDist.single, fTransform_single]
          rfl
        | none =>
          dsimp only
          simp only [ProbDist.map_val, fTransform_fTransform, Function.comp_def]
          congr 1
          funext y
          by_cases hy : y ∉ table.map Prod.snd
          · rw [ite_eq_left hy, ite_eq_left hy]
            rfl
          · rw [ite_eq_right hy, ite_eq_right hy]
            rfl
      | inverse =>
        simp only [lazyBidirectionalRFGameStep, lazyBidirectionalRFStep]
        cases hl : lookupInverse table a with
        | some x =>
          dsimp only
          simp only [ProbDist.single, fTransform_single]
          rfl
        | none =>
          dsimp only
          simp only [ProbDist.map_val, fTransform_fTransform, Function.comp_def]
          congr 1
          funext x
          by_cases hx : x ∉ table.map Prod.fst
          · rw [ite_eq_left hx, ite_eq_left hx]
            rfl
          · rw [ite_eq_right hx, ite_eq_right hx]
            rfl)
    ((ProbDist.single []).map fun s => (s, false))
    (fun _ _ => trivial)
  have hinit : ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).bind
      (fun sb => ProbDist.single sb.1) = ProbDist.single [] := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.map_val, ProbDist.single, fTransform_single,
      bindK_single, one_smul]
  rw [hinit] at hsim
  exact hsim

open Classical in
/-- Hiding the MBO of `strongURPRejectionGame X q` recovers `StrongURP X`. -/
theorem strongURPRejectionGame_visible :
    (strongURPRejectionGame X q).visible = StrongURP X (q := q) := by
  rw [strongURPRejectionGame, TypedGame.visible_ofProbAutomaton, ← lazyStrongURP_eq_strongURP q,
    lazyStrongURP]
  have hsim := TypedSystem.ofProbAutomaton_eq_of_simulation (A := Bidirectional X q)
    (ProbStep.forgetMBO (strongURPRejectionGameStep q)) (lazyStrongURPStep q)
    (fun sb => ProbDist.single sb.1)
    (fun _ sb => IsPartialBijection sb.1)
    (by
      intro _ ⟨table, bad⟩ ⟨i, a⟩ hb _ p hp
      simp only [ProbStep.outcome, ProbStep.forgetMBO, ProbDist.map_val, fTransform_fTransform,
        Function.comp_def] at hp
      obtain ⟨q', hq', rfl⟩ := mem_support_fTransform _ _ hp
      cases i with
      | forward =>
        simp only [strongURPRejectionGameStep] at hq'
        cases hl : lookupForward table a with
        | some y =>
          rw [hl] at hq'
          simp only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
            Finset.mem_singleton] at hq'
          rw [hq']
          exact hb
        | none =>
          rw [hl] at hq'
          rw [ProbDist.bind_val] at hq'
          have hne := Finsupp.mem_support_iff.mp hq'
          rw [bindK_apply] at hne
          obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
          have hq'' := Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hy)
          by_cases hfresh : y ∉ table.map Prod.snd
          · rw [ite_eq_left hfresh] at hq''
            simp only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
              Finset.mem_singleton] at hq''
            rw [hq'']
            exact isPartialBijection_append hb ((lookupForward_eq_none_iff table a).mp hl) hfresh
          · rw [ite_eq_right hfresh] at hq''
            simp only [ProbDist.map_val] at hq''
            obtain ⟨y', hy', rfl⟩ := mem_support_fTransform _ _ hq''
            have hEx : ∃ y : X, y ∉ table.map Prod.snd := by
              obtain ⟨y₀, hy₀⟩ := unusedOutputs_nonempty_of_fresh hb
                ((lookupForward_eq_none_iff table a).mp hl)
              exact ⟨y₀, (Finset.mem_filter.mp hy₀).2⟩
            have hy'fresh : y' ∉ table.map Prod.snd := by
              unfold unusedForwardLaw at hy'
              exact (ProbDist.mem_support_uniformOn_iff (fun y => y ∉ table.map Prod.snd)
                hEx 𝒰[X] y').mp hy'
            exact isPartialBijection_append hb ((lookupForward_eq_none_iff table a).mp hl) hy'fresh
      | inverse =>
        simp only [strongURPRejectionGameStep] at hq'
        cases hl : lookupInverse table a with
        | some x =>
          rw [hl] at hq'
          simp only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
            Finset.mem_singleton] at hq'
          rw [hq']
          exact hb
        | none =>
          rw [hl] at hq'
          rw [ProbDist.bind_val] at hq'
          have hne := Finsupp.mem_support_iff.mp hq'
          rw [bindK_apply] at hne
          obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
          have hq'' := Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hx)
          by_cases hfresh : x ∉ table.map Prod.fst
          · rw [ite_eq_left hfresh] at hq''
            simp only [ProbDist.single, Finsupp.support_single _ one_ne_zero,
              Finset.mem_singleton] at hq''
            rw [hq'']
            exact isPartialBijection_append hb hfresh ((lookupInverse_eq_none_iff table a).mp hl)
          · rw [ite_eq_right hfresh] at hq''
            simp only [ProbDist.map_val] at hq''
            obtain ⟨x', hx', rfl⟩ := mem_support_fTransform _ _ hq''
            have hEx : ∃ x : X, x ∉ table.map Prod.fst := by
              obtain ⟨x₀, hx₀⟩ := unusedInputs_nonempty_of_fresh hb
                ((lookupInverse_eq_none_iff table a).mp hl)
              exact ⟨x₀, (Finset.mem_filter.mp hx₀).2⟩
            have hx'fresh : x' ∉ table.map Prod.fst := by
              unfold unusedInverseLaw at hx'
              exact (ProbDist.mem_support_uniformOn_iff (fun x => x ∉ table.map Prod.fst)
                hEx 𝒰[X] x').mp hx'
            exact isPartialBijection_append hb hx'fresh ((lookupInverse_eq_none_iff table a).mp hl))
    (by
      intro _ ⟨table, bad⟩ ⟨i, a⟩ hb _
      simp only [ProbStep.SimulatesAt, ProbStep.outcome, ProbStep.forgetMBO, ProbDist.map_val,
        ProbDist.single, fTransform_single, bindK_single, one_smul, fTransform_fTransform,
        Function.comp_def, bindK_fTransform, ProbStep.tagged]
      rw [bindK_single_comp]
      cases i with
      | forward =>
        simp only [strongURPRejectionGameStep, lazyStrongURPStep]
        cases hl : lookupForward table a with
        | some y =>
          dsimp only
          simp only [ProbDist.single, fTransform_single]
          rfl
        | none =>
          dsimp only
          have hEx : ∃ y : X, y ∉ table.map Prod.snd := by
            obtain ⟨y₀, hy₀⟩ := unusedOutputs_nonempty_of_fresh hb
              ((lookupForward_eq_none_iff table a).mp hl)
            exact ⟨y₀, (Finset.mem_filter.mp hy₀).2⟩
          have hrej : (𝒰[X].bind fun r =>
                if r ∉ table.map Prod.snd then ProbDist.single r
                else unusedForwardLaw table).1 = (unusedForwardLaw table).1 := by
            unfold unusedForwardLaw
            convert congrArg Subtype.val
              (rejection_resample_eq_uniformOn (fun y => y ∉ table.map Prod.snd) hEx)
          have hlhs :
              fTransform (fun p : (List (X × X) × Bool) × X × Bool =>
                (p.1.1, (⟨Bidirectional.Port.forward, p.2.1⟩ :
                  Σ i, (Bidirectional X q).Y i)))
                (𝒰[X].bind fun y =>
                  if y ∉ table.map Prod.snd then
                    ProbDist.single ((table ++ [(a, y)], bad), (y, bad))
                  else (unusedForwardLaw table).map fun y' =>
                    ((table ++ [(a, y')], true), (y', true))).1 =
              fTransform (fun y : X =>
                (table ++ [(a, y)], (⟨Bidirectional.Port.forward, y⟩ :
                  Σ i, (Bidirectional X q).Y i)))
                (𝒰[X].bind fun y =>
                  if y ∉ table.map Prod.snd then ProbDist.single y
                  else unusedForwardLaw table).1 := by
            simp only [ProbDist.bind_val, fTransform_bindK]
            apply bindK_congr
            intro y _
            by_cases hy : y ∉ table.map Prod.snd
            · rw [ite_eq_left hy, ite_eq_left hy]
              simp only [ProbDist.single, fTransform_single]
            · rw [ite_eq_right hy, ite_eq_right hy]
              simp only [ProbDist.map_val, fTransform_fTransform, Function.comp_def]
          rw [ProbDist.map_val, fTransform_fTransform]
          change fTransform (fun y : X =>
                (table ++ [(a, y)], (⟨Bidirectional.Port.forward, y⟩ :
                  Σ i, (Bidirectional X q).Y i))) (unusedForwardLaw table).1 =
              fTransform (fun p : (List (X × X) × Bool) × X × Bool =>
                (p.1.1, (⟨Bidirectional.Port.forward, p.2.1⟩ :
                  Σ i, (Bidirectional X q).Y i))) _
          rw [hlhs, hrej]
      | inverse =>
        simp only [strongURPRejectionGameStep, lazyStrongURPStep]
        cases hl : lookupInverse table a with
        | some x =>
          dsimp only
          simp only [ProbDist.single, fTransform_single]
          rfl
        | none =>
          dsimp only
          have hEx : ∃ x : X, x ∉ table.map Prod.fst := by
            obtain ⟨x₀, hx₀⟩ := unusedInputs_nonempty_of_fresh hb
              ((lookupInverse_eq_none_iff table a).mp hl)
            exact ⟨x₀, (Finset.mem_filter.mp hx₀).2⟩
          have hrej : (𝒰[X].bind fun r =>
                if r ∉ table.map Prod.fst then ProbDist.single r
                else unusedInverseLaw table).1 = (unusedInverseLaw table).1 := by
            unfold unusedInverseLaw
            convert congrArg Subtype.val
              (rejection_resample_eq_uniformOn (fun x => x ∉ table.map Prod.fst) hEx)
          have hlhs :
              fTransform (fun p : (List (X × X) × Bool) × X × Bool =>
                (p.1.1, (⟨Bidirectional.Port.inverse, p.2.1⟩ :
                  Σ i, (Bidirectional X q).Y i)))
                (𝒰[X].bind fun x =>
                  if x ∉ table.map Prod.fst then
                    ProbDist.single ((table ++ [(x, a)], bad), (x, bad))
                  else (unusedInverseLaw table).map fun x' =>
                    ((table ++ [(x', a)], true), (x', true))).1 =
              fTransform (fun x : X =>
                (table ++ [(x, a)], (⟨Bidirectional.Port.inverse, x⟩ :
                  Σ i, (Bidirectional X q).Y i)))
                (𝒰[X].bind fun x =>
                  if x ∉ table.map Prod.fst then ProbDist.single x
                  else unusedInverseLaw table).1 := by
            simp only [ProbDist.bind_val, fTransform_bindK]
            apply bindK_congr
            intro x _
            by_cases hx : x ∉ table.map Prod.fst
            · rw [ite_eq_left hx, ite_eq_left hx]
              simp only [ProbDist.single, fTransform_single]
            · rw [ite_eq_right hx, ite_eq_right hx]
              simp only [ProbDist.map_val, fTransform_fTransform, Function.comp_def]
          rw [ProbDist.map_val, fTransform_fTransform]
          change fTransform (fun x : X =>
                (table ++ [(x, a)], (⟨Bidirectional.Port.inverse, x⟩ :
                  Σ i, (Bidirectional X q).Y i))) (unusedInverseLaw table).1 =
              fTransform (fun p : (List (X × X) × Bool) × X × Bool =>
                (p.1.1, (⟨Bidirectional.Port.inverse, p.2.1⟩ :
                  Σ i, (Bidirectional X q).Y i))) _
          rw [hlhs, hrej])
    ((ProbDist.single []).map fun s => (s, false))
    (by
      intro sb hsb
      simp only [ProbDist.map_val, ProbDist.single, fTransform_single,
        Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hsb
      rw [hsb]
      exact isPartialBijection_nil)
  have hinit : ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).bind
      (fun sb => ProbDist.single sb.1) = ProbDist.single [] := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.map_val, ProbDist.single, fTransform_single,
      bindK_single, one_smul]
  rw [hinit] at hsim
  exact hsim

open Classical in
/-- `strongURPRejectionGame X q` and `lazyBidirectionalRFGame X q` are literally equivalent as
games (`≡g`) [1, Definition 4.16]. -/
theorem strongURPRejectionGame_gameEquivalent_lazyBidirectionalRFGame :
    (strongURPRejectionGame X q).1.1.GameEquivalent (lazyBidirectionalRFGame X q).1.1 := by
  intro h
  have hb := unset_belief_eq (X := X) q h
  have hinit : ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).1 =
      (ProbDist.single ([], false)).1 := by
    simp only [ProbDist.map_val, ProbDist.single, fTransform_single]
  change ((strongURPRejectionGameStep q).belief (Bidirectional X q).withMBO.inputDomain
      ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).1 (unsetMBOs h)).weight =
    ((lazyBidirectionalRFGameStep q).belief (Bidirectional X q).withMBO.inputDomain
      ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).1 (unsetMBOs h)).weight
  rw [hinit, hb.1, hb.2]

open Classical in
/-- Exact unset-MBO transcript probability of `lazyBidirectionalRFGame X q` on any admitted
collision-free transcript with partial bijection `table`: `1 / |X|^{table.length}`. -/
theorem lazyBidirectionalRF_unset_mass
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (hadm : h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst))
    {table : List (X × X)} (ht : transcriptBijection q h = some table) :
    (lazyBidirectionalRFGame X q).1.1 (unsetMBOs h) =
      1 / (Fintype.card X : ℝ) ^ table.length := by
  have hb := (unset_belief_eq (X := X) q h).1
  have hinit : ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).1 =
      (ProbDist.single ([], false)).1 := by
    simp only [ProbDist.map_val, ProbDist.single, fTransform_single]
  change ((lazyBidirectionalRFGameStep q).belief (Bidirectional X q).withMBO.inputDomain
      ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).1 (unsetMBOs h)).weight = _
  rw [hinit, hb, ite_eq_left hadm, ht, Distribution.weight_smul,
    (ProbDist.single (table, false)).2.2, mul_one]

omit [Nonempty X] in
open Classical in
/-- Exact transcript probability of `StrongURP X` on any admitted transcript whose replies are
characterized by a partial bijection `table`: `1 / (|X|)_{table.length}`. -/
theorem strongURP_mass_of_bijective_table
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (hadm : h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst))
    {table : List (X × X)} (hb : IsPartialBijection table)
    (hiff : ∀ π : Equiv.Perm X, (∀ z ∈ h, permEval q π z.1 = z.2) ↔ Agrees table π) :
    (StrongURP X (q := q)).1 h = 1 / ((Fintype.card X).descFactorial table.length : ℝ) := by
  rw [StrongURP, TypedSystem.sample_ofFunction_mass, behaviorMass, mass_fTransform,
    ← uniform_perm_mass_agrees_eq hb]
  apply mass_congr
  intro π
  rw [DDS.replies_ofFunction_iff, List.map_eq_nil_iff, List.map_map, List.map_eq_map_iff]
  simp only [hadm, true_and]
  rw [← hiff π]
  refine forall₂_congr fun z _ => ?_
  rcases z with ⟨⟨p, a⟩, y⟩
  cases p <;> exact eq_comm

/-! ### Winning and switching bounds -/

open Classical in
/-- One-step set-bit bound for `lazyBidirectionalRFGame X q`: at step `|h|`, the next query sets
the MBO with conditional probability at most `|h| / |X|`. -/
lemma lazyBidirectionalRFGame_set_mass_le
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (u : Σ i, (Bidirectional X q).X i)
    (hadm : (Bidirectional X q).domain (h.map Prod.fst ++ [u])) :
    (∑ y, (lazyBidirectionalRFGame X q).1.1 (unsetMBOs h ++ [(u, tagMBO true y)])) ≤
      ((h.length : ℝ) / Fintype.card X) *
        (lazyBidirectionalRFGame X q).1.1 (unsetMBOs h) := by
  have hinit : ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).1 =
      (ProbDist.single ([], false)).1 := by
    simp only [ProbDist.map_val, ProbDist.single, fTransform_single]
  have hadmH : h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst) := by
    by_cases hn : h = []
    · exact Or.inl hn
    · exact Or.inr ((Bidirectional X q).nonempty_prefix.2 (List.prefix_append _ _)
        (fun he => hn (List.map_eq_nil_iff.mp he)) hadm)
  have hbel := (unset_belief_eq (X := X) q h).1
  have hstep_sum (y : Σ i, (Bidirectional X q).Y i) :
      (lazyBidirectionalRFGame X q).1.1 (unsetMBOs h ++ [(u, tagMBO true y)]) =
        ((lazyBidirectionalRFGameStep q).transition
          ((lazyBidirectionalRFGameStep q).belief (Bidirectional X q).withMBO.inputDomain
            (ProbDist.single ([], false)).1 (unsetMBOs h)) u (tagMBO true y)).weight := by
    change ((lazyBidirectionalRFGameStep q).belief (Bidirectional X q).withMBO.inputDomain
        ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).1
        (unsetMBOs h ++ [(u, tagMBO true y)])).weight = _
    rw [hinit, ProbStep.belief_snoc]
    have hfst : (unsetMBOs h).map Prod.fst = h.map Prod.fst := by
      simp only [unsetMBOs, List.map_map, Function.comp_def]
    simp only [Interface.inputDomain, Domain.ofInputs_apply, hfst]
    exact congrArg Distribution.weight (ite_eq_left hadm)
  simp only [hstep_sum]
  change _ ≤ ((h.length : ℝ) / Fintype.card X) *
    ((lazyBidirectionalRFGameStep q).belief (Bidirectional X q).withMBO.inputDomain
      ((ProbDist.single ([] : List (X × X))).map fun s => (s, false)).1 (unsetMBOs h)).weight
  rw [hinit, hbel, ite_eq_left hadmH]
  cases ht : transcriptBijection q h with
  | none =>
    simp only [ProbStep.transition_zero]
    change ∑ _ : Σ i, (Bidirectional X q).Y i, (0 : ℝ) ≤ ((h.length : ℝ) / Fintype.card X) * 0
    simp only [Finset.sum_const_zero, mul_zero, le_rfl]
  | some table =>
    have ⟨hbt, hlen⟩ := transcriptBijection_isPartialBijection ht
    simp only [transition_smul, Distribution.weight_smul, (ProbDist.single (table, false)).2.2,
      mul_one, ← Finset.mul_sum]
    have hpow_nonneg : 0 ≤ (1 / (Fintype.card X : ℝ) ^ table.length) := by positivity
    rw [mul_comm (((h.length : ℝ) / Fintype.card X))]
    refine mul_le_mul_of_nonneg_left ?_ hpow_nonneg
    have hsum_eq :
        (∑ y : Σ i, (Bidirectional X q).Y i,
          ((lazyBidirectionalRFGameStep q).transition (ProbDist.single (table, false)).1 u
            (tagMBO true y)).weight) =
          (lazyBidirectionalRFGameStep q (table, false) u.1 u.2).1.mass
            (fun p => p.2.2 = true) := by
      have hterm (y : Σ i, (Bidirectional X q).Y i) :
          ((lazyBidirectionalRFGameStep q).transition (ProbDist.single (table, false)).1 u
            (tagMBO true y)).weight =
            (lazyBidirectionalRFGameStep q (table, false) u.1 u.2).1.mass
              (fun p => p.2.2 = true ∧ (⟨u.1, p.2.1⟩ : Σ i, (Bidirectional X q).Y i) = y) := by
        rw [ProbStep.weight_transition, ProbDist.single, Finsupp.sum_single_index (by simp),
          one_mul, ProbStep.outcome, mass_fTransform]
        apply mass_congr
        intro p
        change (⟨u.1, p.2⟩ : Σ i, withMBO (Bidirectional X q).Y i) = tagMBO true y ↔ _
        rw [eq_tagMBO_iff]
        exact and_comm
      simp only [hterm]
      symm
      exact mass_eq_sum_mass_fiber
        (lazyBidirectionalRFGameStep q (table, false) u.1 u.2).1
        (fun p => p.2.2 = true)
        (fun p => (⟨u.1, p.2.1⟩ : Σ i, (Bidirectional X q).Y i)) Finset.univ
        (fun _ _ => Finset.mem_univ _)
    rw [hsum_eq]
    rcases u with ⟨port, a⟩
    cases port with
    | forward =>
      simp only [lazyBidirectionalRFGameStep]
      cases hl : lookupForward table a with
      | some y =>
        simp only [ProbDist.single, mass_single, Bool.false_eq_true, ↓reduceIte]
        positivity
      | none =>
        simp only [ProbDist.map_val, mass_fTransform, ProbDist.uniform]
        have hpred :
            (Distribution.uniform X).mass (fun y : X =>
              (if y ∉ table.map Prod.snd then ((table ++ [(a, y)], false), (y, false))
                else ((table, true), (y, true))).2.2 = true) =
            (Distribution.uniform X).mass (fun y : X => y ∈ table.map Prod.snd) := by
          apply mass_congr
          intro y
          by_cases hy : y ∉ table.map Prod.snd
          · rw [ite_eq_left hy]
            simp only [Bool.false_eq_true, false_iff]
            exact hy
          · rw [ite_eq_right hy]
            simp only [true_iff]
            exact not_not.mp hy
        rw [hpred, Distribution.uniform_mass_eq_card_filter]
        have hcard : ((Finset.univ.filter fun y => y ∈ table.map Prod.snd).card : ℝ) ≤
            (h.length : ℝ) := by
          have heq : Finset.univ.filter (fun y => y ∈ table.map Prod.snd) =
              (table.map Prod.snd).toFinset := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
          rw [heq, List.toFinset_card_of_nodup hbt.2, List.length_map]
          exact_mod_cast hlen
        exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
    | inverse =>
      simp only [lazyBidirectionalRFGameStep]
      cases hl : lookupInverse table a with
      | some x =>
        simp only [ProbDist.single, mass_single, Bool.false_eq_true, ↓reduceIte]
        positivity
      | none =>
        simp only [ProbDist.map_val, mass_fTransform, ProbDist.uniform]
        have hpred :
            (Distribution.uniform X).mass (fun x : X =>
              (if x ∉ table.map Prod.fst then ((table ++ [(x, a)], false), (x, false))
                else ((table, true), (x, true))).2.2 = true) =
            (Distribution.uniform X).mass (fun x : X => x ∈ table.map Prod.fst) := by
          apply mass_congr
          intro x
          by_cases hx : x ∉ table.map Prod.fst
          · rw [ite_eq_left hx]
            simp only [Bool.false_eq_true, false_iff]
            exact hx
          · rw [ite_eq_right hx]
            simp only [true_iff]
            exact not_not.mp hx
        rw [hpred, Distribution.uniform_mass_eq_card_filter]
        have hcard : ((Finset.univ.filter fun x => x ∈ table.map Prod.fst).card : ℝ) ≤
            (h.length : ℝ) := by
          have heq : Finset.univ.filter (fun x => x ∈ table.map Prod.fst) =
              (table.map Prod.fst).toFinset := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
          rw [heq, List.toFinset_card_of_nodup hbt.1, List.length_map]
          exact_mod_cast hlen
        exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)

lemma transcriptCost_length_div {A B : Type} (c : ℝ) (h : List (A × B)) :
    transcriptCost (fun p _ => (p.length : ℝ) / c) h = (h.length.choose 2 : ℝ) / c := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [transcriptCost, List.length_nil, Nat.choose_zero_succ, Nat.cast_zero, zero_div]
  | append_singleton h z ih =>
    rw [transcriptCost_snoc, ih, List.length_append, List.length_singleton,
      Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
    ring

open Classical in
/-- Every compatible stopping distinguisher wins `lazyBidirectionalRFGame X q` with probability at
most `C(q, 2) / |X|`. -/
lemma lazyBidirectionalRFGame_winProbability_le
    (P : (Bidirectional X q).inputDomain.Distinguisher) :
    P.winProbability (lazyBidirectionalRFGame X q).1.1 ≤
      (q.choose 2 : ℝ) / Fintype.card X := by
  apply P.winProbability_le_of_transcriptCost_le (lazyBidirectionalRFGame X q).1.2
    (lazyBidirectionalRFGame X q).2
    (β := fun h _ => (h.length : ℝ) / Fintype.card X)
    (fun h _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (lazyBidirectionalRFGame_set_mass_le X q)
  intro h hh
  have hlen : h.length ≤ q := by
    rcases List.eq_nil_or_concat h with rfl | ⟨h', z, rfl⟩
    · simp only [List.length_nil, Nat.zero_le]
    · rw [List.concat_eq_append] at hh
      have hadm : (Bidirectional X q).domain ((h' ++ [z]).map Prod.fst) := by
        by_contra hd
        apply hh
        exact RandomSystem.mass_eq_zero_of_not_admitted (lazyBidirectionalRFGame X q).1.1.visible
          (by
            change ¬ (Bidirectional X q).domain (h'.map Prod.fst ++ [z.1])
            simpa only [List.map_append, List.map_singleton] using hd) z.2
      have hle := (Bidirectional X q).length_le _ hadm
      rw [List.length_map, List.length_append, List.length_singleton] at hle
      simpa only [List.length_concat] using hle
  rw [transcriptCost_length_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose 2 hlen)
    (Nat.cast_nonneg _)

open Classical in
/-- Every admitted winner on `Bidirectional X q` wins `lazyBidirectionalRFGame X q` with
probability at most `C(q, 2) / |X|`. -/
theorem lazyBidirectionalRFGame_win_le
    {winner : TypedGame (Bidirectional X q) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners (Bidirectional X q)) :
    winner (lazyBidirectionalRFGame X q) ≤ (q.choose 2 : ℝ) / Fintype.card X :=
  Interface.win_le (lazyBidirectionalRFGame_winProbability_le X q) hw

open Classical in
/-- Every admitted winner on `Bidirectional X q` wins `strongURPRejectionGame X q` with
probability at most `C(q, 2) / |X|`. -/
theorem strongURPRejectionGame_win_le
    {winner : TypedGame (Bidirectional X q) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners (Bidirectional X q)) :
    winner (strongURPRejectionGame X q) ≤ (q.choose 2 : ℝ) / Fintype.card X := by
  refine Interface.win_le (fun P => ?_) hw
  rw [P.winProbability_eq_of_gameEquivalent (strongURPRejectionGame X q).1.2
    (lazyBidirectionalRFGame X q).1.2 (strongURPRejectionGame X q).2
    (lazyBidirectionalRFGame X q).2
    (strongURPRejectionGame_gameEquivalent_lazyBidirectionalRFGame X q)]
  exact lazyBidirectionalRFGame_winProbability_le X q P

open Classical in
/-- **Bidirectional RP/RF switching lemma**: `StrongURP X` and `LazyBidirectionalRF X q` are within
statistical distance `C(q, 2) / |X|` for every query budget `q` [1, Theorem 4.17], [2, §4.4.3]. -/
theorem strongURP_dist_lazyBidirectionalRF_le :
    Δ (StrongURP X (q := q)) (LazyBidirectionalRF X q) ≤
      ENNReal.ofReal ((q.choose 2 : ℝ) / Fintype.card X) := by
  rw [ConstructiveCryptography.CryptographicAlgebra.distance_comm,
    ← strongURPRejectionGame_visible X q, ← lazyBidirectionalRFGame_visible X q,
    Interface.cc_distance_eq]
  have hnonneg : (0 : ℝ) ≤ (q.choose 2 : ℝ) / Fintype.card X :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  let ε : ℝ≥0 := ⟨(q.choose 2 : ℝ) / Fintype.card X, hnonneg⟩
  have hdist : (lazyBidirectionalRFGame X q).1.1.visible.transcriptDistance
      (strongURPRejectionGame X q).1.1.visible ≤ ε := by
    apply RandomSystem.GameEquivalent.transcriptDistance_visible_le
      (lazyBidirectionalRFGame X q).1.2
      (fun h => (strongURPRejectionGame_gameEquivalent_lazyBidirectionalRFGame X q h).symm)
      (fun h _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (lazyBidirectionalRFGame_set_mass_le X q)
    intro h hh
    have hlen : h.length ≤ q := by
      rcases List.eq_nil_or_concat h with rfl | ⟨h', z, rfl⟩
      · simp only [List.length_nil, Nat.zero_le]
      · rw [List.concat_eq_append] at hh
        have hadm : (Bidirectional X q).domain ((h' ++ [z]).map Prod.fst) := by
          by_contra hd
          apply hh
          exact RandomSystem.mass_eq_zero_of_not_admitted
            (lazyBidirectionalRFGame X q).1.1.visible
            (by
              change ¬ (Bidirectional X q).domain (h'.map Prod.fst ++ [z.1])
              simpa only [List.map_append, List.map_singleton] using hd) z.2
        have hle := (Bidirectional X q).length_le _ hadm
        rw [List.length_map, List.length_append, List.length_singleton] at hle
        simpa only [List.length_concat] using hle
    rw [transcriptCost_length_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose 2 hlen)
      (Nat.cast_nonneg _)
  have hcoe : (ε : ENNReal) = ENNReal.ofReal ((q.choose 2 : ℝ) / Fintype.card X) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hnonneg]
    rfl
  rw [← hcoe]
  exact_mod_cast hdist

open Classical in
/-- Attaching any converter `α` preserves the bidirectional RP/RF switching bound. -/
theorem strongURP_attach_dist_lazyBidirectionalRF_le
    {A : Interface} (α : A ⟶ Bidirectional X q) :
    Δ (α • StrongURP X (q := q)) (α • LazyBidirectionalRF X q) ≤
      ENNReal.ofReal ((q.choose 2 : ℝ) / Fintype.card X) :=
  (ConstructiveCryptography.CryptographicAlgebra.distance_attach_le α _ _).trans
    (strongURP_dist_lazyBidirectionalRF_le X q)

open Classical in
/-- `StrongURP X` substitutes for `LazyBidirectionalRF X q` within `C(q, 2) / |X|` against any
admissible distinguisher class. -/
theorem strongURP_substitutesWithin_lazyBidirectionalRF
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher] :
    StrongURP X (q := q) ≃[fun _ => ENNReal.ofReal ((q.choose 2 : ℝ) / Fintype.card X)]
      LazyBidirectionalRF X q := by
  intro d hd
  open ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage in
  exact (DominatedByDistance.advantage_le_distance d hd _ _).trans
    (strongURP_dist_lazyBidirectionalRF_le X q)

end PublicAPI

end Commons
