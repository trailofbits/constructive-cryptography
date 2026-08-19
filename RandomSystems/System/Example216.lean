/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.SingleQuery
import RandomSystems.System.MultiDistance

/-!
# Lanzenberger Example 2.16, and Definition 2.28's two printed displays

(Read visually at printed pp. 14–16 and 18 of D. Lanzenberger, *A Theory of
Random Systems, Games, and Hardness Amplification*, DISS ETH No. 29554;
PDF leaves 24–26 and 28.)

Example 2.16 takes the four single-query `({0,1},{0,1})`-DDS of Figure 2.1,

```
zero(x) := 0,   one(x) := 1,   id(x) := x,   flip(x) := 1 − x,
```

the uniform mixture `V := {(zero,¼),(one,¼),(id,¼),(flip,¼)}`, and the
one-parameter family

```
V_α := {(zero,α),(one,α),(id,½−α),(flip,½−α)},   α ∈ [0,½],
```

and observes that all of them "have the same behavior": each answers a
*single* query with a uniform random bit.  `V = V_{1/4}`, `V′ = V_{1/2}`.

The point is that the PDS carrier — a distribution over deterministic systems
— is strictly finer than behaviour.  `V₀` samples the answers to `0` and to
`1` as two independent bits; `V_{1/2}` samples one bit and returns it to
whichever query is asked; the two are indistinguishable only because a system
can be executed once (printed p. 15, below Definition 2.15), and they are as
far apart *as laws* as two probability laws can be: `δ(V₀, V_{1/2}) = 1`.

That is the worked artifact the tree lacked: `classDistance` and `statDist`
are genuinely different numbers, and the thesis's own remark below Definition
2.28 ("taking the infimum seems to be necessary to quantify the distance of
random systems in a meaningful way") is here a theorem rather than a remark.

## What is proved

* `equivalent_V` — `V α ≡ V β` for all `α, β ∈ [0,½]` (Definition 2.17);
* `statDist_V_zero_V_half` — `δ(V₀, V_{1/2}) = 1`, and `V_zero_ne_V_half` —
  the two are distinct *as PDS*: equivalence is strictly coarser than equality;
* `classDistance_classPair` — `Δ(V₀, V₀) = 0`, so the class distance sees none
  of that gap;
* `definition_2_28_printed_displays_disagree` — **the erratum, kernel-checked**;
* `corrected_display_agrees_at_V` — the corrected reading
  (`PDS.multiSystemDistance`) does agree at the same class pair.

## The erratum

Definition 2.28 prints, verbatim,

```
Δ(S,T) := inf_{S∈𝐒, T∈𝐓} δ(S,T) = 1 − inf_{(S,T)∈𝐒×𝐓} sup_ℰ Pr^ℰ(S = T),
```

asserting that its two displays are the same number.  By the coupling lemma
`sup_ℰ Pr^ℰ(S = T) = |S| − δ(S,T)` at each representative pair
(`Probability.supAgreement_pair_eq_weight_sub_statDist`), the second display
equals `sup_{reps} δ` while the first is `inf_{reps} δ`.  They agree exactly
when `δ` is constant across representatives — which is what Example 2.16
denies.  At `𝐒 = 𝐓 = [V₀]` the first display is `0` (take one representative
twice) and the second is `1` (take `V₀` against `V_{1/2}`).

## Provenance

Architecture transplanted from the read-only quarry
`RandomSystems/Example216.lean` (`singleQuery` `:129`, `V` `:310`,
`isProbDist_V` `:356`, `equivalent_V` `:439`, `delta_V0_Vhalf` `:490`,
`definition_2_28_printed_displays_disagree` `:591`,
`corrected_display_agrees_at_V` `:602`), with one **deliberate change of
route**.  The quarry pins the whole class by a closed-form behaviour function
(`classBehavior`) and gets `equivalent_V` as a `rfl`-after-`observableBehavior`
argument; on this carrier the tree already owns the reassembly lemma
`PDS.equivalent_of_weight_eq_of_successorTransform_equivalent`
(`Attainment.lean`, thesis §2.4.2 step 6), so the equivalence is proved by
computing the successor transformations instead.  They come out *literally
independent of `α`* — `single emptySystem ½` at every answered first query and
`0` at the refusal — which is Example 2.16's content stated at the first-answer
level.  No behaviour function is introduced, and the computation reuses
`PDS.weight_successorTransform` (Notation 2.34's weight identity) and
`PDS.eq_single_emptySystem_of_support_rejects_every_query`.
-/

namespace RandomSystems

noncomputable section

open Probability (Distribution statDist)
open Probability

open scoped ENNReal

namespace Example216

open System

/-! ## Local plumbing

The event mass of a point law.  Kept local for the reason `Attainment.lean`
already gives for its own local `Distribution` copies: the probability layer is
not free to rebuild. -/

open Classical in
theorem mass_single {A : Type*} (a : A) (c : ℝ) (P : A → Prop) :
    Distribution.mass (Finsupp.single a c) P = if P a then c else 0 := by
  unfold Distribution.mass
  rw [Finsupp.sum_single_index (by by_cases h : P a <;> simp [h])]

/-! ## Figure 2.1: the four single-query systems -/

/-- Figure 2.1's `zero(x) := 0`. -/
def zeroFn : Bool → Bool := fun _ => false

/-- Figure 2.1's `one(x) := 1`. -/
def oneFn : Bool → Bool := fun _ => true

/-- Figure 2.1's `id(x) := x`. -/
def idFn : Bool → Bool := fun x => x

/-- Figure 2.1's `flip(x) := 1 − x`. -/
def flipFn : Bool → Bool := fun x => !x

/-- Figure 2.1's systems as single-query DDS. -/
def atom (f : Bool → Bool) : System.DDS Bool Bool := System.DDS.singleQuery f

theorem atom_ne {f g : Bool → Bool} (h : f ≠ g) : atom f ≠ atom g :=
  fun he => h (System.singleQuery_injective he)

/-- The reversed form, spelled out rather than reached by `Ne.symm`, so that
`rw` sees the orientation `Finsupp.single_eq_of_ne` needs. -/
theorem atom_ne' {f g : Bool → Bool} (h : f ≠ g) : atom g ≠ atom f :=
  fun he => h (System.singleQuery_injective he).symm

theorem zeroFn_ne_oneFn : zeroFn ≠ oneFn := fun h => by
  simpa [zeroFn, oneFn] using congrFun h false
theorem zeroFn_ne_idFn : zeroFn ≠ idFn := fun h => by
  simpa [zeroFn, idFn] using congrFun h true
theorem zeroFn_ne_flipFn : zeroFn ≠ flipFn := fun h => by
  simpa [zeroFn, flipFn] using congrFun h false
theorem oneFn_ne_idFn : oneFn ≠ idFn := fun h => by
  simpa [oneFn, idFn] using congrFun h false
theorem oneFn_ne_flipFn : oneFn ≠ flipFn := fun h => by
  simpa [oneFn, flipFn] using congrFun h true
theorem idFn_ne_flipFn : idFn ≠ flipFn := fun h => by
  simpa [idFn, flipFn] using congrFun h false

/-! ## Example 2.10: the figure itself

The four atoms above are also thesis **Example 2.10** (printed p. 14, PDF leaf
24), the row this section closes.  Figure 2.1 was read visually there, and it
draws each system as a depth-one tree: an unlabelled root, two edges out of it
labelled `0` and `1` — the query — and two leaves carrying the answer.  The
leaf labels are

```
zero: 0 ↦ 0, 1 ↦ 0      one: 0 ↦ 1, 1 ↦ 1
id:   0 ↦ 0, 1 ↦ 1      flip: 0 ↦ 1, 1 ↦ 0
```

and the caption's text reads "the four single-query `({0,1},{0,1})`-DDS zero,
one, id, and flip, i.e., **all total functions** from `{0,1}` to `{0,1}`".

Three things are therefore checkable, and are checked below against the
definitions above: the tree has *one* level of branching
(`figure_2_1_single_query`), the leaves carry those answers
(`figure_2_1_answers`), and the four exhaust the single-query systems
(`figure_2_1_exhaustive`, `figure_2_1_exhaustive_dds`) — with the six
distinctness lemmas above they are exactly four.  The bit convention is the
tree's own: the figure's `0` is `false` and its `1` is `true`. -/

/-- **Figure 2.1, the depth of the tree.**  Each system answers a single query
and nothing after it: the domain is exactly `X¹`, the figure's one level of
branching.  A *total* evaluator would be a tree of unbounded depth and would
let an environment read two leaves of one sample, which is exactly what
Example 2.16 turns on. -/
theorem figure_2_1_single_query (f : Bool → Bool) :
    System.dom (atom f) = System.singleQueryDomain Bool :=
  System.dom_singleQuery f

/-- **Figure 2.1, the leaf labels.**  The answer each of the four systems gives
to the query `x`, in the `s⊥` presentation: `zero` answers `0`, `one` answers
`1`, `id` answers `x`, `flip` answers `1 − x`. -/
theorem figure_2_1_answers (x : Bool) :
    System.answer (atom zeroFn) [] x = some false ∧
      System.answer (atom oneFn) [] x = some true ∧
        System.answer (atom idFn) [] x = some x ∧
          System.answer (atom flipFn) [] x = some (!x) :=
  ⟨by simp [atom, zeroFn], by simp [atom, oneFn], by simp [atom, idFn],
    by simp [atom, flipFn]⟩

/-- **Example 2.10's "all total functions"**, at the answer functions: every
`f : {0,1} → {0,1}` is one of Figure 2.1's four. -/
theorem figure_2_1_exhaustive (f : Bool → Bool) :
    f = zeroFn ∨ f = oneFn ∨ f = idFn ∨ f = flipFn := by
  rcases hfalse : f false with _ | _ <;> rcases htrue : f true with _ | _
  · exact Or.inl (funext fun x => by cases x <;> simp [zeroFn, hfalse, htrue])
  · exact Or.inr (Or.inr (Or.inl
      (funext fun x => by cases x <;> simp [idFn, hfalse, htrue])))
  · exact Or.inr (Or.inr (Or.inr
      (funext fun x => by cases x <;> simp [flipFn, hfalse, htrue])))
  · exact Or.inr (Or.inl (funext fun x => by cases x <;> simp [oneFn, hfalse, htrue]))

/-- **Example 2.10's "all total functions"**, at the systems: every
single-query `({0,1},{0,1})`-DDS *is* one of Figure 2.1's four, so the figure
depicts the whole genus and not four samples of it.  Read through U1's
representation (`System.singleQueryEquiv`), where "single-query" is the
domain being exactly `X¹` — the figure's own depth. -/
theorem figure_2_1_exhaustive_dds {s : System.DDS Bool Bool}
    (hs : System.dom s = System.singleQueryDomain Bool) :
    s = atom zeroFn ∨ s = atom oneFn ∨ s = atom idFn ∨ s = atom flipFn := by
  obtain ⟨f, rfl⟩ : ∃ f : Bool → Bool, System.DDS.singleQuery f = s :=
    ⟨System.singleQueryEquiv.symm ⟨s, hs⟩,
      congrArg Subtype.val (System.singleQueryEquiv.apply_symm_apply ⟨s, hs⟩)⟩
  rcases figure_2_1_exhaustive f with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-! ## The family `V_α` -/

/-- Example 2.16's family
`V_α := {(zero,α),(one,α),(id,½−α),(flip,½−α)}`.  The thesis's `V` is `V ¼`
and its `V′` is `V ½`.

The parameter is unrestricted here; the hypothesis `0 ≤ α ≤ ½` — the thesis's
own range, which is exactly what makes `V α` a probability law — is carried by
the theorems that need it, as the tree does everywhere else. -/
def V (α : ℝ) : PDS Bool Bool :=
  Finsupp.single (atom zeroFn) α + Finsupp.single (atom oneFn) α
    + Finsupp.single (atom idFn) (1 / 2 - α)
    + Finsupp.single (atom flipFn) (1 / 2 - α)

theorem V_apply_zeroFn (α : ℝ) : V α (atom zeroFn) = α := by
  rw [V]
  simp only [Finsupp.add_apply]
  rw [Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (atom_ne zeroFn_ne_oneFn),
    Finsupp.single_eq_of_ne (atom_ne zeroFn_ne_idFn),
    Finsupp.single_eq_of_ne (atom_ne zeroFn_ne_flipFn)]
  ring

theorem V_apply_oneFn (α : ℝ) : V α (atom oneFn) = α := by
  rw [V]
  simp only [Finsupp.add_apply]
  rw [Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (atom_ne' zeroFn_ne_oneFn),
    Finsupp.single_eq_of_ne (atom_ne oneFn_ne_idFn),
    Finsupp.single_eq_of_ne (atom_ne oneFn_ne_flipFn)]
  ring

theorem V_apply_idFn (α : ℝ) : V α (atom idFn) = 1 / 2 - α := by
  rw [V]
  simp only [Finsupp.add_apply]
  rw [Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (atom_ne' zeroFn_ne_idFn),
    Finsupp.single_eq_of_ne (atom_ne' oneFn_ne_idFn),
    Finsupp.single_eq_of_ne (atom_ne idFn_ne_flipFn)]
  ring

theorem V_apply_flipFn (α : ℝ) : V α (atom flipFn) = 1 / 2 - α := by
  rw [V]
  simp only [Finsupp.add_apply]
  rw [Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (atom_ne' zeroFn_ne_flipFn),
    Finsupp.single_eq_of_ne (atom_ne' oneFn_ne_flipFn),
    Finsupp.single_eq_of_ne (atom_ne' idFn_ne_flipFn)]
  ring

theorem weight_V (α : ℝ) : (V α).weight = 1 := by
  rw [V, Distribution.weight_add, Distribution.weight_add,
    Distribution.weight_add, Distribution.weight_single,
    Distribution.weight_single, Distribution.weight_single,
    Distribution.weight_single]
  ring

theorem nonNeg_V {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) : (V α).NonNeg := by
  intro s
  rw [V]
  simp only [Finsupp.add_apply]
  have hc : (0 : ℝ) ≤ 1 / 2 - α := by linarith
  exact add_nonneg (add_nonneg (add_nonneg
    (Distribution.single_nonNeg h0 _ s) (Distribution.single_nonNeg h0 _ s))
    (Distribution.single_nonNeg hc _ s)) (Distribution.single_nonNeg hc _ s)

theorem isProbDist_V {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) :
    (V α).isProbDist :=
  ⟨nonNeg_V h0 h1, weight_V α⟩

/-- Every atom in the support of `V α` is one of Figure 2.1's four systems. -/
theorem exists_fn_of_mem_support_V {α : ℝ} {s : System.DDS Bool Bool}
    (hs : s ∈ (V α).support) : ∃ f : Bool → Bool, s = atom f := by
  classical
  rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
  · rcases Finset.mem_union.mp (Finsupp.support_add h) with h' | h'
    · rcases Finset.mem_union.mp (Finsupp.support_add h') with h'' | h''
      · exact ⟨zeroFn, Finset.mem_singleton.mp (Finsupp.support_single_subset h'')⟩
      · exact ⟨oneFn, Finset.mem_singleton.mp (Finsupp.support_single_subset h'')⟩
    · exact ⟨idFn, Finset.mem_singleton.mp (Finsupp.support_single_subset h')⟩
  · exact ⟨flipFn, Finset.mem_singleton.mp (Finsupp.support_single_subset h)⟩

open Classical in
/-- The support of `V α` sits inside Figure 2.1's four systems. -/
theorem support_V_subset (α : ℝ) :
    (V α).support ⊆ ({atom zeroFn, atom oneFn, atom idFn, atom flipFn} :
      Finset (System.DDS Bool Bool)) := by
  intro s hs
  rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
  · rcases Finset.mem_union.mp (Finsupp.support_add h) with h' | h'
    · rcases Finset.mem_union.mp (Finsupp.support_add h') with h'' | h''
      · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h'')]; simp
      · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h'')]; simp
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h')]; simp
  · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h)]; simp

/-- Every representative in the support of `V α` has the single-query domain,
which is Definition 2.14's common-domain clause for this family. -/
theorem dom_eq_of_mem_support_V {α : ℝ} {s : System.DDS Bool Bool}
    (hs : s ∈ (V α).support) :
    System.dom s = System.singleQueryDomain Bool := by
  obtain ⟨f, rfl⟩ := exists_fn_of_mem_support_V hs
  exact System.dom_singleQuery f

/-! ## The successor transformations do not depend on `α`

This is Example 2.16's content at the first-answer level: whatever the query
`x`, the mass answering it with `b` is `½` for every member of the family, and
after that one answer every member is spent. -/

open Classical in
/-- After the first query every survivor is the empty system, so the successor
transformation accepts no query at all. -/
theorem notMem_dom_of_mem_support_successorTransform_V {α : ℝ} {x : Bool}
    {y : Option Bool} {s' : System.DDS Bool Bool}
    (hs' : s' ∈ (PDS.successorTransform (V α) x y).support) (q : Bool) :
    [q] ∉ System.dom s' := by
  unfold PDS.successorTransform at hs'
  obtain ⟨s, hs, rfl⟩ := Distribution.mem_support_fTransform _ _ hs'
  have hsV : s ∈ (V α).support := by
    rw [Finsupp.mem_support_iff] at hs ⊢
    intro h0
    rw [Finsupp.filter_apply] at hs
    split at hs
    · exact hs h0
    · exact hs rfl
  obtain ⟨f, rfl⟩ := exists_fn_of_mem_support_V hsV
  rw [atom, System.successor_singleQuery]
  exact System.notMem_dom_emptySystem [q]

/-- The successor transformation of `V α` is a point law at the empty system:
its only content is its weight. -/
theorem successorTransform_V_eq_single (α : ℝ) (x : Bool) (y : Option Bool) :
    PDS.successorTransform (V α) x y
      = Finsupp.single System.emptySystem
          (PDS.successorTransform (V α) x y).weight :=
  PDS.eq_single_emptySystem_of_support_rejects_every_query
    fun _ hs' q => notMem_dom_of_mem_support_successorTransform_V hs' q

open Classical in
/-- Notation 2.34's weight identity, computed on the family: whichever bit is
asked and whichever bit is answered, exactly mass `½` of `V α` produced it —
**independently of `α`**. -/
theorem weight_successorTransform_V_some (α : ℝ) (x b : Bool) :
    (PDS.successorTransform (V α) x (some b)).weight = 1 / 2 := by
  rw [PDS.weight_successorTransform, V, Distribution.mass_add,
    Distribution.mass_add, Distribution.mass_add, mass_single, mass_single,
    mass_single, mass_single]
  simp only [atom, System.output_fullyDefined_singleQuery, Option.some.injEq]
  cases x <;> cases b <;>
    norm_num [zeroFn, oneFn, idFn, flipFn]

open Classical in
/-- Every member of the family answers its first query, so the `⊥`-answer
branch is empty. -/
theorem weight_successorTransform_V_none (α : ℝ) (x : Bool) :
    (PDS.successorTransform (V α) x none).weight = 0 := by
  rw [PDS.weight_successorTransform, V, Distribution.mass_add,
    Distribution.mass_add, Distribution.mass_add, mass_single, mass_single,
    mass_single, mass_single]
  simp only [atom, System.output_fullyDefined_singleQuery, reduceCtorEq,
    if_false, add_zero]

/-- **Example 2.16, the equivalence**: every two members of the family present
the same random system, so `{V_α | α ∈ [0,½]} ⊆ [V]` — the equivalence class of
a PDS is a nontrivial line.

The proof is the reassembly lemma of thesis §2.4.2 step 6: equal weight,
nothing outside the common domain, and per-first-answer successor
transformations that agree — and here they do not merely agree, they are
*equal*, and independent of the parameter. -/
theorem equivalent_V {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 / 2) :
    PDS.equivalent (V α) (V β) := by
  have hsucc : ∀ (x : Bool) (y : Option Bool),
      PDS.successorTransform (V α) x y = PDS.successorTransform (V β) x y := by
    intro x y
    rw [successorTransform_V_eq_single α x y, successorTransform_V_eq_single β x y]
    cases y with
    | none =>
        rw [weight_successorTransform_V_none, weight_successorTransform_V_none]
    | some b =>
        rw [weight_successorTransform_V_some, weight_successorTransform_V_some]
  refine PDS.equivalent_of_weight_eq_of_successorTransform_equivalent
    (D := System.singleQueryDomain Bool) (nonNeg_V hα0 hα1) (nonNeg_V hβ0 hβ1)
    (by rw [weight_V, weight_V]) (fun s hs => dom_eq_of_mem_support_V hs)
    (fun {x} hx => absurd (System.singleton_mem_singleQueryDomain x) hx)
    (fun {x} _ y => ?_)
  rw [hsucc x y]
  exact PDS.equivalent_refl _

/-! ## The gap between `δ` and `Δ` -/

open Classical in
/-- `δ(V₀, V_{1/2}) = 1`: the two extremes of the family have disjoint
supports, each of weight one, so the thesis's remark below Definition 2.28 is
exact. -/
theorem statDist_V_zero_V_half : statDist (V 0) (V (1 / 2)) = 1 := by
  have hsub : ((V 0) - (V (1 / 2))).support ⊆
      ({atom zeroFn, atom oneFn, atom idFn, atom flipFn} :
        Finset (System.DDS Bool Bool)) := fun s hs => by
    rcases Finset.mem_union.mp (Finsupp.support_sub hs) with h | h
    · exact support_V_subset 0 h
    · exact support_V_subset (1 / 2) h
  rw [Probability.statDist_eq_sum_of_support_subset (V 0) (V (1 / 2)) hsub,
    Finset.sum_insert (by
      simp [atom_ne zeroFn_ne_oneFn, atom_ne zeroFn_ne_idFn,
        atom_ne zeroFn_ne_flipFn]),
    Finset.sum_insert (by
      simp [atom_ne oneFn_ne_idFn, atom_ne oneFn_ne_flipFn]),
    Finset.sum_insert (by simp [atom_ne idFn_ne_flipFn]),
    Finset.sum_singleton,
    V_apply_zeroFn, V_apply_zeroFn, V_apply_oneFn, V_apply_oneFn,
    V_apply_idFn, V_apply_idFn, V_apply_flipFn, V_apply_flipFn]
  norm_num

/-- The two extremes of the family are **distinct as PDS** — equivalence is
strictly coarser than equality, which is the whole point of Notation 2.19. -/
theorem V_zero_ne_V_half : V 0 ≠ V (1 / 2) := by
  intro h
  have hval : V 0 (atom idFn) = V (1 / 2) (atom idFn) := by rw [h]
  rw [V_apply_idFn, V_apply_idFn] at hval
  norm_num at hval

/-! ## Definition 2.28's two printed displays -/

/-- The representative pair `(V₀, V_{1/2})` of the class `[V₀]`, as the `Fin 2`
tuple the multi-system distance consumes. -/
def extremes : Fin 2 → PDS Bool Bool := fun k => if k = 0 then V 0 else V (1 / 2)

theorem extremes_zero : extremes 0 = V 0 := rfl
theorem extremes_one : extremes 1 = V (1 / 2) := rfl

theorem supAgreement_extremes : supAgreement extremes = 0 := by
  have hnn : ∀ k, (extremes k).NonNeg := by
    intro k
    fin_cases k
    · exact nonNeg_V le_rfl (by norm_num)
    · exact nonNeg_V (by norm_num) le_rfl
  rw [supAgreement_pair_eq_weight_sub_statDist extremes hnn
    (by rw [extremes_zero, extremes_one, weight_V, weight_V]),
    extremes_zero, extremes_one, weight_V, statDist_V_zero_V_half]
  ring

/-- The constant tuple at the class `[V₀]` — the `𝐒 = 𝐓 = [V]` of the thesis's
own remark below Definition 2.28. -/
def classPair : Fin 2 → PDS Bool Bool := fun _ => V 0

theorem mem_agreementValues_zero :
    (0 : ℝ) ∈ PDS.agreementValues classPair := by
  refine ⟨extremes, fun k => ?_, supAgreement_extremes.symm⟩
  fin_cases k
  · exact PDS.equivalent_refl _
  · exact equivalent_V le_rfl (by norm_num) (by norm_num) le_rfl

theorem bddBelow_agreementValues_classPair :
    BddBelow (PDS.agreementValues classPair) := by
  refine ⟨0, ?_⟩
  rintro a ⟨laws, -, rfl⟩
  exact supAgreement_nonneg laws

/-- **Definition 2.28's second printed display, evaluated**: at the class
`[V₀]` the printed `inf` over representative pairs makes the display `1`. -/
theorem printedMultiSystemDistance_classPair :
    PDS.printedMultiSystemDistance classPair = 1 := by
  have hle : sInf (PDS.agreementValues classPair) ≤ 0 :=
    csInf_le bddBelow_agreementValues_classPair mem_agreementValues_zero
  have hge : 0 ≤ sInf (PDS.agreementValues classPair) := by
    refine le_csInf ⟨supAgreement classPair, classPair,
      fun _ => PDS.equivalent_refl _, rfl⟩ ?_
    rintro a ⟨laws, -, rfl⟩
    exact supAgreement_nonneg laws
  show 1 - sInf (PDS.agreementValues classPair) = 1
  rw [le_antisymm hle hge, sub_zero]

/-- **Definition 2.28's first printed display, evaluated**: the class distance
at the same class pair is `0`. -/
theorem classDistance_classPair :
    PDS.classDistance (classPair 0) (classPair 1) = 0 :=
  PDS.classDistance_self (nonNeg_V le_rfl (by norm_num))

/-- **The erratum, kernel-checked.**  Definition 2.28 asserts that its two
printed displays are the same number.  At the class pair `𝐒 = 𝐓 = [V₀]` — the
very pair the thesis's own remark below the definition cites — the first
display is `0` and the second is `1`. -/
theorem definition_2_28_printed_displays_disagree :
    ENNReal.ofReal (PDS.printedMultiSystemDistance classPair)
      ≠ PDS.classDistance (classPair 0) (classPair 1) := by
  rw [printedMultiSystemDistance_classPair, classDistance_classPair]
  simp

/-- **The corrected reading agrees at the same class pair.**  Turning the
printed `inf` over representative tuples into a `sup`
(`PDS.multiSystemDistance`) restores Definition 2.28's asserted identity
here. -/
theorem corrected_display_agrees_at_V :
    ENNReal.ofReal (PDS.multiSystemDistance classPair)
      = PDS.classDistance (classPair 0) (classPair 1) := by
  have hprob : (V (0 : ℝ)).isProbDist := isProbDist_V le_rfl (by norm_num)
  have hle : PDS.multiSystemDistance classPair ≤ 0 := by
    have hstep := PDS.multiSystemDistance_le_statDist_of_equivalent
      (P := classPair) (PDS.equivalent_refl (V 0)) (PDS.equivalent_refl (V 0))
      hprob hprob
    rwa [Probability.statDist_self] at hstep
  have hge : 0 ≤ PDS.multiSystemDistance classPair :=
    PDS.multiSystemDistance_nonneg classPair (weight_V 0)
  rw [le_antisymm hle hge, classDistance_classPair]
  simp

end Example216

end

end RandomSystems
