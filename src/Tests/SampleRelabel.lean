module

public import RandomSystems.Typed.SampleRelabel
public import RandomSystems.Typed.QueryRouting

/-!
# Relabeling retained draws on visible transcripts

Tests `TypedSystem.sample_mass_eq_of_map`, `TypedSystem.sample_mass_eq_of_display_relabel`, and
`TypedGame.sample_visible_mass_eq_of_relabel` using two independent fair bits `(b₀, b₁)`.
When a hidden bit `m` is dropped from replies, one internal history (`m = false`) matches via
the identity map and the other (`m = true`) matches via swapping `(b₀, b₁)`. No single
law-preserving relabeling can match the visible probabilities pointwise.
-/

@[expose] public section

namespace Tests.SampleRelabel

open Probability Probability.Distribution SystemAlgebra

/-- Two independent fair bits `(b₀, b₁)` drawn uniformly from `Bool × Bool`. -/
noncomputable def twoBits : Distribution (Bool × Bool) :=
  Distribution.prod 𝒰[Bool].1 𝒰[Bool].1

instance : Distribution.IsProbability twoBits :=
  ⟨(Distribution.prod_isProbDist _ _ 𝒰[Bool].2 𝒰[Bool].2).1,
   (Distribution.prod_isProbDist _ _ 𝒰[Bool].2 𝒰[Bool].2).2⟩

/-- Swapping two independent fair bits preserves their joint law. -/
lemma fTransform_swap_twoBits : Distribution.fTransform Prod.swap twoBits = twoBits :=
  Distribution.fTransform_swap_prod 𝒰[Bool].1 𝒰[Bool].1

/-- One-query visible interface with a Boolean reply. -/
abbrev bitIface : Interface := Interface.source Bool 1

/-- Internal reply law `0`: draw hidden bit `m ← 𝒰[Bool]` and return `(b₀, m)`. -/
noncomputable def replyLaw₀ (k : Bool × Bool) : ProbDist (Bool × Bool) :=
  𝒰[Bool].map fun m => (k.1, m)

/-- Internal reply law `1`: draw hidden bit `m ← 𝒰[Bool]` and return `(if m then b₁ else b₀, m)`. -/
noncomputable def replyLaw₁ (k : Bool × Bool) : ProbDist (Bool × Bool) :=
  𝒰[Bool].map fun m => (if m then k.2 else k.1, m)

/-- Any memoryless system on `bitIface.withMBO` is a typed game (at most one reply per run). -/
noncomputable def oneBitGame (ν : ProbDist (Bool × Bool)) : TypedGame bitIface :=
  ⟨TypedSystem.ofMemoryless bitIface.withMBO fun _ _ => ν, by
    intro h hm
    have hlen : h.length ≤ 1 := by
      rcases TypedSystem.possible_domain (TypedSystem.ofMemoryless bitIface.withMBO fun _ _ => ν)
          hm with hnil | hdom
      · simp only [List.map_eq_nil_iff.mp hnil, List.length_nil, zero_le]
      · simpa only [List.length_map] using bitIface.withMBO.length_le _ hdom
    match h with
    | [] => exact List.Pairwise.nil
    | [_] => exact List.pairwise_singleton _ _
    | _ :: _ :: _ => exact absurd hlen (by norm_num)⟩

/-- System `0` as a typed game hiding its second bit `m` as the MBO. -/
noncomputable def game₀ (k : Bool × Bool) : TypedGame bitIface :=
  oneBitGame (replyLaw₀ k)

/-- System `1` as a typed game hiding its second bit `m` as the MBO. -/
noncomputable def game₁ (k : Bool × Bool) : TypedGame bitIface :=
  oneBitGame (replyLaw₁ k)

/-- The single-query visible transcript returning `true`. -/
abbrev visTrue : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, Bool)) :=
  [(⟨(), ()⟩, ⟨(), true⟩)]

/-- Evaluate `oneBitGame ν` on a length-1 MBO-tagged transcript. -/
lemma oneBitGame_single (ν : ProbDist (Bool × Bool)) (y m : Bool) :
    (oneBitGame ν).1.1 [(⟨(), ()⟩, ⟨(), (y, m)⟩)] = ν.1 (y, m) := by
  have hd : bitIface.withMBO.inputDomain [] ⟨(), ()⟩ := by
    change ([⟨(), ()⟩] : List (Σ _ : Unit, Unit)) ≠ [] ∧
      ([⟨(), ()⟩] : List (Σ _ : Unit, Unit)).length ≤ 1
    exact ⟨List.cons_ne_nil _ _, le_rfl⟩
  have hsnoc := RandomSystem.memoryless_snoc bitIface.withMBO.inputDomain
    (RandomSystem.portLaw (fun (_ : Unit) (_ : Unit) => ν)) [] ⟨(), ()⟩ ⟨(), (y, m)⟩
  simp only [List.nil_append] at hsnoc
  change (TypedSystem.ofMemoryless bitIface.withMBO fun _ _ => ν).1 [(⟨(), ()⟩, ⟨(), (y, m)⟩)] = _
  rw [TypedSystem.ofMemoryless_val, hsnoc, ite_eq_left hd, RandomSystem.mass_nil, one_mul,
    RandomSystem.portLaw_apply_mk]

/-- Point mass of `replyLaw₀ k` at `(y, m)`. -/
lemma replyLaw₀_apply (k : Bool × Bool) (y m : Bool) :
    (replyLaw₀ k).1 (y, m) = if y = k.1 then (1 / 2 : ℝ) else 0 := by
  rw [replyLaw₀, ProbDist.map_val, Distribution.fTransform_apply_eq_mass,
    Distribution.mass_eq_sum]
  have hunif : ∀ b : Bool, 𝒰[Bool].1 b = (1 / 2 : ℝ) := fun b => by
    change Distribution.uniform Bool b = (1 / 2 : ℝ)
    simp only [Distribution.uniform_apply, Fintype.card_bool, Nat.cast_ofNat]
  simp only [Fintype.sum_bool, Prod.mk.injEq, hunif]
  rcases k with ⟨b₀, b₁⟩
  cases b₀ <;> cases y <;> cases m <;> norm_num

/-- Point mass of `replyLaw₁ k` at `(y, m)`. -/
lemma replyLaw₁_apply (k : Bool × Bool) (y m : Bool) :
    (replyLaw₁ k).1 (y, m) = if y = (if m then k.2 else k.1) then (1 / 2 : ℝ) else 0 := by
  rw [replyLaw₁, ProbDist.map_val, Distribution.fTransform_apply_eq_mass,
    Distribution.mass_eq_sum]
  have hunif : ∀ b : Bool, 𝒰[Bool].1 b = (1 / 2 : ℝ) := fun b => by
    change Distribution.uniform Bool b = (1 / 2 : ℝ)
    simp only [Distribution.uniform_apply, Fintype.card_bool, Nat.cast_ofNat]
  simp only [Fintype.sum_bool, Prod.mk.injEq, hunif]
  rcases k with ⟨b₀, b₁⟩
  cases b₀ <;> cases b₁ <;> cases y <;> cases m <;> norm_num

/-- Two independent fair bits: the visible probabilities at `visTrue` agree because internal
history `m = false` matches via `id` and internal history `m = true` matches via `Prod.swap`. -/
example :
    (TypedSystem.sample twoBits fun k => (game₀ k).visible).1 visTrue =
      (TypedSystem.sample twoBits fun k => (game₁ k).visible).1 visTrue := by
  apply TypedGame.sample_visible_mass_eq_of_relabel
  intro u hu
  -- Every internal history displaying as `visTrue` has length 1 with query `()` and visible `true`.
  match u with
  | [] => cases hu
  | [((⟨(), ()⟩, ⟨(), (y, m)⟩))] =>
    have hy : y = true := by
      have h0 := congrArg (fun l => l.head?.map fun p => p.2.2) hu
      exact Option.some.inj (by simpa only [forgetMBOs, forgetMBO, List.map_cons,
        List.head?_cons, Option.map_some] using h0)
    subst hy
    cases m
    · -- Hidden bit `false`: match with the identity map `id`.
      refine ⟨id, Distribution.fTransform_id twoBits, fun k _ => ?_⟩
      change (oneBitGame (replyLaw₀ k)).1.1 [(⟨(), ()⟩, ⟨(), (true, false)⟩)] =
        (oneBitGame (replyLaw₁ k)).1.1 [(⟨(), ()⟩, ⟨(), (true, false)⟩)]
      rw [oneBitGame_single, oneBitGame_single, replyLaw₀_apply, replyLaw₁_apply]
      simp only [Bool.false_eq_true, ↓reduceIte]
    · -- Hidden bit `true`: match by swapping the two fair bits `(b₀, b₁)`.
      refine ⟨Prod.swap, fTransform_swap_twoBits, fun k _ => ?_⟩
      change (oneBitGame (replyLaw₀ k)).1.1 [(⟨(), ()⟩, ⟨(), (true, true)⟩)] =
        (oneBitGame (replyLaw₁ k.swap)).1.1 [(⟨(), ()⟩, ⟨(), (true, true)⟩)]
      rw [oneBitGame_single, oneBitGame_single, replyLaw₀_apply, replyLaw₁_apply]
      simp only [Prod.snd_swap, ↓reduceIte]
  | _ :: _ :: _ =>
    have hlen := congrArg List.length hu
    simp only [forgetMBOs, List.length_map, List.length_cons, List.length_nil] at hlen
    omega

/-- The same example via `TypedConverter.mapReplies` hiding the second bit and
`TypedSystem.sample_mass_eq_of_display_relabel`. -/
example :
    let hide := TypedConverter.mapReplies (Interface.source (Bool × Bool) 1) (fun _ y => y.1)
    let R₀ : Bool × Bool → TypedSystem bitIface := fun k =>
      hide • TypedSystem.ofMemoryless (Interface.source (Bool × Bool) 1) fun _ _ => replyLaw₀ k
    let R₁ : Bool × Bool → TypedSystem bitIface := fun k =>
      hide • TypedSystem.ofMemoryless (Interface.source (Bool × Bool) 1) fun _ _ => replyLaw₁ k
    (TypedSystem.sample twoBits R₀).1 visTrue = (TypedSystem.sample twoBits R₁).1 visTrue := by
  classical
  intro hide R₀ R₁
  have hmem : ∀ (ν : ProbDist (Bool × Bool)),
      (hide • TypedSystem.ofMemoryless (Interface.source (Bool × Bool) 1) fun _ _ => ν).1
        visTrue = ∑ ym : Bool × Bool, if ym.1 = true then ν.1 ym else 0 := by
    intro ν
    have hmap := TypedConverter.mapReplies_smul_ofMemoryless (Interface.source (Bool × Bool) 1)
      (fun _ (y : Bool × Bool) => y.1) (fun _ _ => ν)
    have hd : bitIface.inputDomain [] ⟨(), ()⟩ := by
      change ([⟨(), ()⟩] : List (Σ _ : Unit, Unit)) ≠ [] ∧
        ([⟨(), ()⟩] : List (Σ _ : Unit, Unit)).length ≤ 1
      exact ⟨List.cons_ne_nil _ _, le_rfl⟩
    have hsnoc := RandomSystem.memoryless_snoc bitIface.inputDomain
      (RandomSystem.portLaw (fun (_ : Unit) (_ : Unit) => ν.map Prod.fst))
      [] ⟨(), ()⟩ ⟨(), true⟩
    simp only [List.nil_append] at hsnoc
    have heq : (hide • TypedSystem.ofMemoryless (Interface.source (Bool × Bool) 1)
        fun _ _ => ν).1 visTrue = (ν.map Prod.fst).1 true := by
      rw [hmap, TypedSystem.ofMemoryless_val]
      change RandomSystem.memoryless bitIface.inputDomain
        (RandomSystem.portLaw (fun (_ : Unit) (_ : Unit) => ν.map Prod.fst))
        [(⟨(), ()⟩, ⟨(), true⟩)] = _
      rw [hsnoc, ite_eq_left hd, RandomSystem.mass_nil, one_mul, RandomSystem.portLaw_apply_mk]
    rw [heq, ProbDist.map_val, Distribution.fTransform_apply_eq_mass, Distribution.mass_eq_sum]
    refine Finset.sum_congr rfl fun ym _ => ?_
    by_cases hy : ym.1 = true <;> simp only [hy, ↓reduceIte]
  refine TypedSystem.sample_mass_eq_of_display_relabel twoBits R₀ R₁ visTrue
    (Finset.univ : Finset (Bool × Bool)) (fun ym => [(⟨(), ()⟩, ⟨(), ym.1⟩)])
    (fun k ym => (replyLaw₀ k).1 ym) (fun k ym => (replyLaw₁ k).1 ym)
    (fun k _ => (hmem (replyLaw₀ k)).trans <| Finset.sum_congr rfl fun ym _ => by
      simp only [List.cons.injEq, Prod.mk.injEq, Sigma.mk.injEq, heq_eq_eq, and_true, true_and])
    (fun k _ => (hmem (replyLaw₁ k)).trans <| Finset.sum_congr rfl fun ym _ => by
      simp only [List.cons.injEq, Prod.mk.injEq, Sigma.mk.injEq, heq_eq_eq, and_true, true_and])
    fun ym _ hdisp => ?_
  have hy : ym.1 = true := by
    have h0 := congrArg (fun l => l.head?.map fun p => p.2.2) hdisp
    exact Option.some.inj (by simpa only [List.head?_cons, Option.map_some] using h0)
  rcases ym with ⟨y, m⟩
  dsimp only at hy
  subst hy
  cases m
  · refine ⟨id, Distribution.fTransform_id twoBits, fun k _ => ?_⟩
    simp only [replyLaw₀_apply, replyLaw₁_apply, id_eq, Bool.false_eq_true, ↓reduceIte]
  · refine ⟨Prod.swap, fTransform_swap_twoBits, fun k _ => ?_⟩
    simp only [replyLaw₀_apply, replyLaw₁_apply, Prod.snd_swap, ↓reduceIte]

/-- No single `twoBits`-preserving relabeling matches the visible probabilities pointwise:
`game₀` gives visible probability `1` on two keys (`(true, true)` and `(true, false)`),
while `game₁` gives `1` only on `(true, true)`. -/
example :
    ¬ ∃ s : Bool × Bool → Bool × Bool,
      Distribution.fTransform s twoBits = twoBits ∧
        ∀ k ∈ twoBits.support,
          ((game₀ k).visible).1 visTrue = ((game₁ (s k)).visible).1 visTrue := by
  classical
  rintro ⟨s, hs, hmatch⟩
  have hval : ∀ k : Bool × Bool, twoBits k = (1 / 4 : ℝ) := by
    intro k
    rw [twoBits, Distribution.prod_apply]
    have hunif : ∀ b : Bool, 𝒰[Bool].1 b = (1 / 2 : ℝ) := fun b => by
      change Distribution.uniform Bool b = (1 / 2 : ℝ)
      simp only [Distribution.uniform_apply, Fintype.card_bool, Nat.cast_ofNat]
    rw [hunif, hunif]
    norm_num
  have hsupp : ∀ k : Bool × Bool, k ∈ twoBits.support := fun k => by
    rw [Finsupp.mem_support_iff, hval]
    norm_num
  have hvis₀ : ∀ k : Bool × Bool, ((game₀ k).visible).1 visTrue = if k.1 then 1 else 0 := by
    intro k
    change sumMBO (game₀ k).1.1 visTrue = _
    simp only [sumMBO, tagMBO]
    change (oneBitGame (replyLaw₀ k)).1.1 [(⟨(), ()⟩, ⟨(), (true, false)⟩)] +
      (oneBitGame (replyLaw₀ k)).1.1 [(⟨(), ()⟩, ⟨(), (true, true)⟩)] = _
    rw [oneBitGame_single, oneBitGame_single, replyLaw₀_apply, replyLaw₀_apply]
    cases k.1 <;> norm_num
  have hvis₁ : ∀ k : Bool × Bool,
      ((game₁ k).visible).1 visTrue =
        (if k.1 then (1 / 2 : ℝ) else 0) + (if k.2 then 1 / 2 else 0) := by
    intro k
    change sumMBO (game₁ k).1.1 visTrue = _
    simp only [sumMBO, tagMBO]
    change (oneBitGame (replyLaw₁ k)).1.1 [(⟨(), ()⟩, ⟨(), (true, false)⟩)] +
      (oneBitGame (replyLaw₁ k)).1.1 [(⟨(), ()⟩, ⟨(), (true, true)⟩)] = _
    rw [oneBitGame_single, oneBitGame_single, replyLaw₁_apply, replyLaw₁_apply]
    cases k.1 <;> cases k.2 <;> norm_num
  have hs_eq : ∀ k : Bool × Bool, k.1 = true → s k = (true, true) := by
    intro k hk
    have h1 := hmatch k (hsupp k)
    rw [hvis₀, hvis₁, hk] at h1
    rcases hs_k : s k with ⟨a, b⟩
    rw [hs_k] at h1
    cases a <;> cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 <;> norm_num at h1
    rfl
  -- Both `(true, true)` and `(true, false)` map to `(true, true)`, giving mass ≥ 1/2 > 1/4.
  have hmass := congrArg (fun D : Distribution (Bool × Bool) => D (true, true)) hs
  rw [Distribution.fTransform_apply_eq_mass, Distribution.mass_eq_sum] at hmass
  have hle : twoBits (true, true) + twoBits (true, false) ≤
      ∑ k : Bool × Bool, if s k = (true, true) then twoBits k else 0 := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, hs_eq (true, true) rfl, hs_eq (true, false) rfl, ↓reduceIte]
    have hnn : ∀ k : Bool × Bool, 0 ≤ if s k = (true, true) then twoBits k else 0 := by
      intro k
      split_ifs
      · exact (Distribution.IsProbability.isProbDist twoBits).1 k
      · exact le_rfl
    linarith [hnn (false, true), hnn (false, false)]
  have hsum_eq :
      (∑ k : Bool × Bool, if s k = (true, true) then twoBits k else 0) = twoBits (true, true) := by
    convert hmass
  have hbound : twoBits (true, true) + twoBits (true, false) ≤ twoBits (true, true) :=
    hle.trans (le_of_eq hsum_eq)
  rw [hval (true, true), hval (true, false)] at hbound
  norm_num at hbound

/-- Fair distribution on `{0, 1} ⊆ Fin 3`, leaving `2` outside its support. -/
noncomputable def fairTwoOfThree : Distribution (Fin 3) :=
  Finsupp.single (0 : Fin 3) (1 / 2) + Finsupp.single (1 : Fin 3) (1 / 2)

instance : Distribution.IsProbability fairTwoOfThree :=
  ⟨fun x => by
    simp only [fairTwoOfThree, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> norm_num, by
    simp only [fairTwoOfThree, Distribution.weight_add, Distribution.weight_single]
    norm_num⟩

/-- `sample_mass_eq_of_map` does not require `s` to be bijective: collapsing the unsupported point
`2 ↦ 0` while swapping supported points `0 ↔ 1` preserves `fairTwoOfThree`. -/
example :
    (TypedSystem.sample fairTwoOfThree fun k =>
        TypedSystem.ofFunction (A := bitIface) fun _ _ => k == 0).1 visTrue =
      (TypedSystem.sample fairTwoOfThree fun k =>
        TypedSystem.ofFunction (A := bitIface) fun _ _ => k == 1).1 visTrue := by
  let s : Fin 3 → Fin 3 := fun | 0 => 1 | 1 => 0 | 2 => 0
  refine TypedSystem.sample_mass_eq_of_map fairTwoOfThree
    (fun k => TypedSystem.ofFunction (A := bitIface) fun _ _ => k == 0)
    (fun k => TypedSystem.ofFunction (A := bitIface) fun _ _ => k == 1) visTrue s ?_ ?_
  · -- `s` is neither injective (`s 1 = s 2 = 0`) nor surjective (`2 ∉ range s`), yet preserves `P`.
    simp only [fairTwoOfThree, Distribution.fTransform_add, Distribution.fTransform_single, s]
    exact add_comm _ _
  · intro k hk
    have hk01 : k = 0 ∨ k = 1 := by
      have hne : fairTwoOfThree k ≠ 0 := Finsupp.mem_support_iff.mp hk
      match k with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr rfl
      | 2 =>
        exfalso
        apply hne
        simp only [fairTwoOfThree, Finsupp.add_apply, Finsupp.single_apply, Fin.reduceEq,
          ↓reduceIte, add_zero]
    rcases hk01 with rfl | rfl <;> rfl

#print axioms Probability.Distribution.sum_mul_eq_of_fTransform_eq
#print axioms Probability.Distribution.sum_mul_sum_eq_of_fTransform_eq
#print axioms SystemAlgebra.TypedSystem.sample_mass_eq_of_map
#print axioms SystemAlgebra.TypedSystem.sample_mass_eq_of_sum_relabel
#print axioms SystemAlgebra.TypedSystem.sample_mass_eq_of_display_relabel
#print axioms SystemAlgebra.TypedGame.sample_visible_mass_eq_of_relabel

end Tests.SampleRelabel
