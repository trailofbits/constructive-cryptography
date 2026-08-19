/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ClassDistance

/-!
# Attainment: Lanzenberger Theorems 2.31 and 2.32

`ClassDistance.lean` proves `Adv⊥ ≤ Δ` unconditionally and records what the
converse needs.  This file supplies it, on the slice Lanzenberger's standing
finiteness assumptions cut out:

* the query alphabet is finite (`[Fintype X]`);
* every deterministic system in either support presents **one** common domain
  `D` (Definition 2.14's clause, named at a single `D` for both systems);
* `D` answers at most `q` queries (`QBounded D q`);
* both laws are honest (`Distribution.NonNeg`).

**The bundle is not bookkeeping.**  Without it the equality is *false*, not
merely unproved: on the fully defined presentation a rejected query is a
visible `⊥`, so an environment reading refusals off the transcript separates
systems that no static pair of representatives separates.  The refutation is
`AttainmentCounterexample` in the sibling random-systems repository
(`four_pattern_unrestricted_class_distance_ne_optimal_advantage`), at
`PDS Bool PUnit`, where `Adv⊥ = ½` while every equivalent pair has
`statDist = 1`.  Ruling R9 restricts `Δ`'s infimum to *honest* pairs, which can
only raise it, so the refutation survives the ruling unchanged.

## Main definitions

* `System.DDS.successor`, `System.DDE.Total.successor`,
  `PDS.successorTransform` — Lanzenberger **Notation 2.34**'s `s↑x`, `e↑y`,
  `S↑x↓y`.  `S↑x↓y` is a genuine sub-distribution: its weight is the
  probability that `S` answers `y` to `x` (`PDS.weight_successorTransform`),
  which is why Definition 2.1 must allow arbitrary weight.
* `System.DDS.prepend`, `PDS.prependTransform` — the inverse move, used to
  reassemble a system from its first-answer branches.
* `PDS.HaveCommonDomainAndBounded` — the finite shared-domain slice, as a
  hypothesis bundle rather than a subtype.  `List X` is infinite even at
  finite `X`, so no `Fintype` exists on `System.DDS X Y`; the thesis's
  finiteness is carried by these predicates.
* `PDS.FiniteClassJointWitness` — the output shape of Lemma 2.33.
* `PDS.BoundedAttainmentWitness` — the invariant of the query induction.

## Main results

* `PDS.exists_finiteClassJointWitness_of_common_side_weights` — Lanzenberger
  **Lemma 2.33** at finite first-query classes, in the corrected `max` form.
* `PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded` — Lanzenberger
  **Theorem 2.31**, `Δ(S, T) = Adv⊥(S, T)` on the slice, and
  `PDS.exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded`
  its attainment half.
* `PDS.classDistance_eq_Adv_of_commonDomain_bounded` — the same equality read
  through the L1 coding map, i.e. against Definition 2.26's own advantage.
* `PDS.exists_equivalent_coupling_offDiagonalMass_eq_advFullyDefined_of_commonDomain_bounded`
  — Lanzenberger **Theorem 2.32**, the coupling theorem for random systems.

## Provenance

Every proof architecture here is transplanted from the sibling `random-systems`
repository, restated on this tree's carrier (`PDS X Y = Distribution
(System.DDS X Y)`) and on this tree's metric (`PDS.advFullyDefined`,
`PDS.classDistance`); the quarry's `Adv`/`Δ` are different objects and none of
its statements is copied verbatim.  File:line citations are given at each
declaration group.
-/

namespace RandomSystems

noncomputable section

open Probability (Distribution statDist)

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}

/-! ## Lanzenberger Notation 2.34: successor systems, environments, laws

Quarry architecture: `RandomSystems/RandomSystem.lean:1896` (`DDS.successor`),
`:1923` (`DDE.successor`), `:1935` (`PDS.successorTransform`), `:2132`
(the first-answer decomposition of the transcript law), `:2169` (the weight
identity). -/


open Classical in
/-- LanMau20 Notation 7: the **successor system** `s↑x` "behaves like
`s` after the first query `x` has been input" — `s↑x(x̂ⁱ) := s(x‖x̂ⁱ)`
when `s` answers the first query `x`; the empty history stays outside
the domain.  When `x` is `⊥`-answered, CR18 Def 3.3's skip semantics
apply: `s⊥` deletes the undefined query and leaves the state of `s`
unchanged, so the successor is `s` itself. -/
noncomputable def System.DDS.successor (s : System.DDS X Y) (x : X) :
    System.DDS X Y :=
  if [x] ∈ System.dom s then
  ⟨fun l => if l = [] then Part.none else s.1 (x :: l), by
    constructor
    · intro h
      rw [PFun.mem_dom] at h
      simp at h
    · intro l₁ l₂ hpre hne h₂
      have h₂' : x :: l₂ ∈ s.1.Dom := by
        rw [PFun.mem_dom] at h₂ ⊢
        by_cases hl₂ : l₂ = []
        · rw [if_pos hl₂] at h₂
          simp at h₂
        · rwa [if_neg hl₂] at h₂
      rw [PFun.mem_dom]
      rw [if_neg hne, ← PFun.mem_dom]
      exact s.2.2 (List.cons_prefix_cons.mpr ⟨rfl, hpre⟩)
        (List.cons_ne_nil x l₁) h₂'⟩
  else s

/-- LanMau20 Notation 7 for environments: the successor environment
`e↑y(ŷⁱ) := e(y‖ŷⁱ)` continues `e` after it has received the first
answer `y` (with the `s⊥`-semantics the answer alphabet is `Y ∪ {⊥}`,
so `y : Option Y`). -/
def System.DDE.Total.successor (e : System.DDE.Total Y X) (y : Option Y) :
    System.DDE.Total Y X :=
  fun ys => e (y :: ys)

open Classical in
/-- LanMau20 Notation 7: `S↑x↓y` is "the transformation of `S` with the
partial function `s ↦ s↑x↓y`", where `s↑x↓y` equals `s↑x` if `s(x) = y`
and is undefined otherwise — keep exactly the systems whose first
`s⊥`-answer to `x` is `y` (the ⊥-answer is an ordinary case of
`y : Option Y`), and step each survivor to its successor.  Its weight
is the probability that `S` answers `y` to the first query `x` — in
general a strict sub-distribution. -/
noncomputable def PDS.successorTransform (S : PDS X Y) (x : X)
    (y : Option Y) : PDS X Y :=
  Distribution.fTransform (fun s => System.DDS.successor s x)
    (S.filter fun s => System.output (System.fullyDefined s) [x]
      (by rw [System.dom_fullyDefined]; simp) = y)

/-- LanMau20 Notation 7 / CR18 Def 3.3: on a `⊥`-answered first query
the state is unchanged — `s↑x = s` when `s(x)` is undefined. -/
theorem System.successor_of_not_mem {s : System.DDS X Y} {x : X}
    (hx : [x] ∉ System.dom s) :
    System.DDS.successor s x = s := by
  unfold System.DDS.successor
  rw [if_neg hx]

/-- LanMau20 Notation 7 pointwise, answered case: on nonempty histories
`s↑x(x̂ⁱ) = s(x‖x̂ⁱ)`. -/
theorem System.successor_apply_of_mem {s : System.DDS X Y} {x : X}
    (hx : [x] ∈ System.dom s) {l : List X} (hl : l ≠ []) :
    (System.DDS.successor s x).1 l = s.1 (x :: l) := by
  unfold System.DDS.successor
  rw [if_pos hx]
  exact if_neg hl

/-- LanMau20 Notation 7 at the domain level, answered case: `s↑x` is
defined on a nonempty history exactly when `s` is defined on its
`x`-extension. -/
theorem System.mem_dom_successor_iff {s : System.DDS X Y} {x : X}
    (hx : [x] ∈ System.dom s) {m : List X} (hm : m ≠ []) :
    m ∈ System.dom (System.DDS.successor s x) ↔ x :: m ∈ System.dom s :=
  iff_of_eq (congrArg Part.Dom (System.successor_apply_of_mem hx hm))

open Classical in
/-- CR18 Def 3.3's bookkeeping through one query: the kept prefix of
`x‖m` keeps `x` exactly when `s` answers it, and the remainder is the
kept prefix of the successor system `s↑x`. -/
theorem System.keptPrefix_successor (s : System.DDS X Y) (x : X) (m : List X) :
    System.keptPrefix s (x :: m)
      = (if [x] ∈ System.dom s then [x] else [])
          ++ System.keptPrefix (System.DDS.successor s x) m := by
  by_cases hx : [x] ∈ System.dom s
  · rw [if_pos hx]
    have haux : ∀ (m acc : List X),
        List.foldl (fun acc q =>
            if acc ++ [q] ∈ System.dom s then acc ++ [q] else acc)
          (x :: acc) m
          = x :: List.foldl (fun acc q =>
              if acc ++ [q] ∈ System.dom (System.DDS.successor s x)
              then acc ++ [q] else acc) acc m := by
      intro m
      induction m with
      | nil => intro acc; rfl
      | cons q m ihm =>
          intro acc
          simp only [List.foldl_cons]
          have hstep : (if (x :: acc) ++ [q] ∈ System.dom s
                then (x :: acc) ++ [q] else x :: acc)
              = x :: (if acc ++ [q] ∈ System.dom (System.DDS.successor s x)
                  then acc ++ [q] else acc) := by
            by_cases hq : acc ++ [q] ∈ System.dom (System.DDS.successor s x)
            · have hq' : (x :: acc) ++ [q] ∈ System.dom s :=
                (System.mem_dom_successor_iff hx (by simp)).mp hq
              rw [if_pos hq', if_pos hq, List.cons_append]
            · have hq' : (x :: acc) ++ [q] ∉ System.dom s := fun hmem =>
                hq ((System.mem_dom_successor_iff hx (by simp)).mpr hmem)
              rw [if_neg hq', if_neg hq]
          rw [hstep, ihm]
    simp only [System.keptPrefix, List.foldl_cons, List.nil_append]
    rw [if_pos hx]
    exact haux m []
  · rw [if_neg hx, System.successor_of_not_mem hx, List.nil_append]
    simp only [System.keptPrefix, List.foldl_cons, List.nil_append]
    rw [if_neg hx]

open Classical in
/-- The pointwise heart of the LanMau20 §4.2 decomposition: after the
first query `x`, the fully defined completion `s⊥` answers exactly as
`(s↑x)⊥` — on answered queries by Notation 7's shift, on `⊥`-answered
queries by CR18 Def 3.3's skip semantics. -/
theorem System.output_fullyDefined_successor (s : System.DDS X Y) (x : X) {l : List X}
    (h : l ∈ System.dom (System.fullyDefined (System.DDS.successor s x)))
    (h' : x :: l ∈ System.dom (System.fullyDefined s)) :
    System.output (System.fullyDefined (System.DDS.successor s x)) l h
      = System.output (System.fullyDefined s) (x :: l) h' := by
  have hl : l ≠ [] := by
    have hmem := h
    rw [System.dom_fullyDefined] at hmem
    exact hmem
  by_cases hx : [x] ∈ System.dom s
  · have key : ∀ (c : List X), c ≠ [] →
        (if hcand : c ∈ System.dom (System.DDS.successor s x) then
          some (System.output (System.DDS.successor s x) c hcand)
        else none)
          = (if hcand : x :: c ∈ System.dom s then
              some (System.output s (x :: c) hcand)
            else none) := by
      intro c hc
      by_cases hmem : c ∈ System.dom (System.DDS.successor s x)
      · rw [dif_pos hmem, dif_pos ((System.mem_dom_successor_iff hx hc).mp hmem)]
        refine congrArg some (Part.mem_unique ?_ (Part.get_mem _))
        rw [← System.successor_apply_of_mem hx hc]
        exact Part.get_mem hmem
      · rw [dif_neg hmem,
          dif_neg fun hmem' => hmem ((System.mem_dom_successor_iff hx hc).mpr hmem')]
    simp only [System.output_fullyDefined, List.dropLast_cons_of_ne_nil hl,
      List.getLast_cons hl, System.keptPrefix_successor, if_pos hx,
      List.cons_append]
    exact key (System.keptPrefix (System.DDS.successor s x) l.dropLast
      ++ [l.getLast hl]) (by simp)
  · simp only [System.output_fullyDefined, List.dropLast_cons_of_ne_nil hl,
      List.getLast_cons hl, System.keptPrefix_successor, System.successor_of_not_mem hx,
      if_neg hx, List.nil_append]

/-- The completion's answer after an initial query `x` is read off the
successor system: `(s↑x)⊥` answers a history exactly as `s⊥` answers its
`x`-extension.  This is `System.output_fullyDefined_successor` in the
`answer`-shaped form the transcript engine produces. -/
theorem System.answer_successor (s : System.DDS X Y) (x : X) (l : List X)
    (x' : X) :
    System.answer (System.DDS.successor s x) l x' =
      System.answer s (x :: l) x' :=
  System.output_fullyDefined_successor s x
    (by rw [System.dom_fullyDefined]; simp)
    (by rw [System.dom_fullyDefined]; simp)

/-- CR18 Def 3.7 through LanMau20 §4.2: one transcript step splits off
the head entry `(x, s⊥(x))` and continues as the transcript of the
successor system against the successor environment. -/
theorem System.transcript_successor (s : System.DDS X Y) (e : System.DDE.Total Y X) {x : X}
    (he : e [] = some x) (n : ℕ) :
    System.DDE.Total.transcript s e (n + 1)
      = (x, System.output (System.fullyDefined s) [x]
            (by rw [System.dom_fullyDefined]; simp)) ::
          System.DDE.Total.transcript (System.DDS.successor s x)
            (System.DDE.Total.successor e
              (System.output (System.fullyDefined s) [x]
                (by rw [System.dom_fullyDefined]; simp))) n := by
  have key : ∀ y₀ : Option Y,
      System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp) = y₀ →
      ∀ m : ℕ, System.DDE.Total.transcript s e (m + 1)
        = (x, y₀) :: System.DDE.Total.transcript (System.DDS.successor s x)
            (System.DDE.Total.successor e y₀) m := by
    intro y₀ hy₀ m
    induction m with
    | zero =>
        have h0 : e (System.transcriptOutputs (System.DDE.Total.transcript s e 0))
            = some x := he
        rw [System.DDE.Total.transcript_succ_of_query s e h0, ← hy₀]
        rfl
    | succ m ih =>
        cases hfire : System.DDE.Total.successor e y₀
            (System.transcriptOutputs (System.DDE.Total.transcript
              (System.DDS.successor s x) (System.DDE.Total.successor e y₀) m)) with
        | none =>
            have hstall : e (System.transcriptOutputs
                (System.DDE.Total.transcript s e (m + 1))) = none := by
              rw [ih]; exact hfire
            rw [System.DDE.Total.transcript_succ_of_stop s e hstall, System.DDE.Total.transcript_succ_of_stop (System.DDS.successor s x) (System.DDE.Total.successor e y₀) hfire]
            exact ih
        | some x' =>
            have hfire' : e (System.transcriptOutputs
                (System.DDE.Total.transcript s e (m + 1))) = some x' := by
              rw [ih]; exact hfire
            rw [System.DDE.Total.transcript_succ_of_query s e hfire', System.DDE.Total.transcript_succ_of_query (System.DDS.successor s x) (System.DDE.Total.successor e y₀) hfire]
            simp only [ih, System.transcriptInputs, List.map_cons,
              List.cons_append]
            rw [System.answer_successor]
  exact key _ rfl n

open Classical in
/-- LanMau20 §4.2, the Lemma 2 step of Theorem 1 at the transcript
level: the length-`(n+1)` transcript distribution partitions over the
first answer `y` — each summand is the cons-pushforward by `(x, y)` of
the length-`n` transcript distribution of the successor transformation
`S↑x↓y` against the successor environment `e↑y`. -/
theorem PDS.trLawFullyDefined_successor (S : PDS X Y) (e : System.DDE.Total Y X)
    {x : X} (he : e [] = some x) (n : ℕ) :
    trLawFullyDefined e (n + 1) S
      = ∑ y ∈ S.support.image (fun s =>
            System.output (System.fullyDefined s) [x]
              (by rw [System.dom_fullyDefined]; simp)),
          Distribution.fTransform (fun t => (x, y) :: t)
            (trLawFullyDefined (System.DDE.Total.successor e y) n (PDS.successorTransform S x y)) := by
  refine Finsupp.ext fun t => ?_
  rw [Finsupp.finset_sum_apply]
  refine Eq.trans (Distribution.fTransform_apply_eq_mass _ _ _) ?_
  refine Eq.trans (Distribution.mass_eq_sum_mass_fiber S _
    (fun s => System.output (System.fullyDefined s) [x]
      (by rw [System.dom_fullyDefined]; simp)) _
    fun s hs => Finset.mem_image_of_mem _ hs) ?_
  refine Finset.sum_congr rfl fun y hy => ?_
  refine Eq.trans ?_ (Distribution.fTransform_apply_eq_mass _ _ _).symm
  refine Eq.trans ?_ (Distribution.mass_fTransform _ _ _).symm
  refine Eq.trans ?_ (Distribution.mass_fTransform _ _ _).symm
  refine Eq.trans ?_ (Distribution.mass_filter S _ _).symm
  refine Distribution.mass_congr S fun s => ?_
  beta_reduce
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [System.transcript_successor s e he n, h2] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [System.transcript_successor s e he n, h2]
    exact h1

open Classical in
/-- LanMau20 Notation 7's weight remark: the weight of `S↑x↓y` is the
probability that `S`'s first answer to `x` is `y` — in general the
transformation produces a strict sub-distribution. -/
theorem PDS.weight_successorTransform (S : PDS X Y) (x : X) (y : Option Y) :
    (PDS.successorTransform S x y).weight
      = S.mass fun s => System.output (System.fullyDefined s) [x]
          (by rw [System.dom_fullyDefined]; simp) = y := by
  refine Eq.trans (Distribution.weight_fTransform _ _) ?_
  refine Eq.trans (Distribution.mass_true _).symm ?_
  refine Eq.trans (Distribution.mass_filter S _ _) ?_
  refine Distribution.mass_congr S fun s => ?_
  beta_reduce
  exact iff_of_eq (true_and _)


theorem System.output_fullyDefined_eq_none_iff {s : System.DDS X Y} {x : X} :
    System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp) = none
      ↔ [x] ∉ System.dom s := by
  constructor
  · intro h hx
    have hsome := System.output_fullyDefined_append_of_mem s [] x
      (Or.inr rfl) hx
    exact Option.some_ne_none _ ((h.symm.trans hsome).symm)
  · intro hx
    simp only [System.output_fullyDefined]
    split
    · rename_i hmem
      exact absurd hmem hx
    · rfl

open Classical in
/-- The `⊥`-marginal of **any** PDS is its pass-through filter: the
skip-aware successor is the identity on atoms that do not answer `x`,
so no separate `⊥`-branch representative ever exists or is needed —
`S↑x↓⊥` is `S` restricted to the atoms that `⊥`-answer `x`. -/
theorem PDS.successorTransform_none_eq_filter (S : PDS X Y) (x : X) :
    PDS.successorTransform S x none
      = S.filter fun s => [x] ∉ System.dom s := by
  unfold PDS.successorTransform
  have hfil : S.filter (fun s => System.output (System.fullyDefined s) [x]
      (by rw [System.dom_fullyDefined]; simp) = none)
      = S.filter fun s => [x] ∉ System.dom s := by
    refine Finsupp.ext fun s => ?_
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hs : [x] ∈ System.dom s
    · rw [if_neg fun h => System.output_fullyDefined_eq_none_iff.mp h hs,
        if_neg fun h => h hs]
    · rw [if_pos (System.output_fullyDefined_eq_none_iff.mpr hs), if_pos hs]
  rw [hfil]
  refine Eq.trans (Distribution.fTransform_congr (g := id) _
    fun s hs => System.successor_of_not_mem ?_) (Distribution.fTransform_id _)
  have hs' : s ∈ S.support.filter fun s => [x] ∉ System.dom s := by
    rw [← Finsupp.support_filter]
    exact hs
  exact (Finset.mem_filter.mp hs').2

/-! ## L2a: the finite shared-domain slice

Lanzenberger's Definition 2.9 finiteness clause and Definition 2.14's
common-domain clause, as the **hypothesis bundle** the attainment induction
consumes.  There is deliberately no subtype: `System.DDS X Y` admits no
`Fintype` even at finite `X`, because `List X` is infinite, and the finiteness
the induction actually uses is (i) a finite first-query alphabet, (ii) one
common domain, (iii) a uniform answered-query bound on it.  Everything else it
needs is already finite for free — a `Distribution` is a `Finsupp`, so both
supports, and hence the realized first-answer sets below, are `Finset`s with no
hypothesis at all.

Quarry architecture: `RandomSystems/BoundedAttainment.lean:53` (the residual
domain), `:74` (its bound), `:90` (the bundle), `:99`–`:115` (the realized
first-answer carriers). -/

/-- The residual common domain after an answered first query `x`.

The empty history is excluded because a DDS domain never contains it; a
nonempty residual history `m` is admitted exactly when `x :: m` was admitted
before the query. -/
def System.successorDomain (D : Set (List X)) (x : X) : Set (List X) :=
  {m | m ≠ [] ∧ x :: m ∈ D}

/-- Every deterministic atom with fixed domain `D` has the source residual
domain after an answered first query. -/
theorem System.successor_domain_eq_of_fixed_domain_and_answered
    {s : System.DDS X Y} {D : Set (List X)} {x : X}
    (hs : System.dom s = D) (hx : [x] ∈ D) :
    System.dom (System.DDS.successor s x) = System.successorDomain D x := by
  have hxs : [x] ∈ System.dom s := hs.symm ▸ hx
  ext m
  constructor
  · intro hm
    have hne : m ≠ [] := fun h => by
      subst h
      exact System.empty_not_mem _ hm
    exact ⟨hne, hs ▸ (System.mem_dom_successor_iff hxs hne).mp hm⟩
  · rintro ⟨hne, hm⟩
    exact (System.mem_dom_successor_iff hxs hne).mpr (hs.symm ▸ hm)

/-- The residual domain of a `(q + 1)`-bounded source domain is `q`-bounded. -/
theorem System.successor_domain_is_bounded_by_predecessor_of_bounded
    {D : Set (List X)} {x : X} {q : Nat}
    (hD : QBounded D (q + 1)) :
    QBounded (System.successorDomain D x) q := by
  intro m hm
  have hlen := hD (x :: m) hm.2
  simp only [List.length_cons] at hlen
  omega



/-- **The finite shared-domain slice**: the two systems present one common
domain `D`, and `D` answers at most `q` queries.

The domain clause is `PDS.HasDomain` at a *named* `D` on each side —
Definition 2.14's attribute, which is what the theory reads.  It is deliberately
not `PDS.HasFixedDomain`, the one-system *existential* form: two instances of
that supply two possibly different domains, and across distinct domains every
statement below is false, the same failure the coding map
(`PDS.advFullyDefined_eq_Adv_of_dom_eq`) records.  The common `D` is a
parameter, not an existential.

Finiteness of the query alphabet stays a typeclass hypothesis on the theorems
that enumerate first queries; it is not part of this bundle, because the parts
of the induction that only move the domain around do not need it.

**Thesis §2.5, "On the Number of Queries" (printed p. 38), realized here.**
The thesis fixes the convention that the query count is a property of the
*system* — "the number of queries that a system answers" — and not of the
distinguisher, calling the difference conceptual.  `QBounded D q` is that
convention: a predicate on the system's own domain, carried by this bundle and
by nothing else.  The metric has no counterpart that could carry the other
convention: `PDS.advFullyDefined` takes its supremum over *all* total
environments and *all* interaction lengths, so a distinguisher-side budget is
not expressible without a new object.  The bridge the thesis asserts between
the two perspectives — restrict the system by CR18 Definition 3.10's filter
`[q]`, i.e. `System.filterQueries` — is deliberately not stated: that filter's
completion receipt is still open, and the paragraph's second half (a bound on
the components inducing a bound `q'` on a construction built from them) is a
statement about wiring systems together, which belongs to the attachment
track. -/
def PDS.HaveCommonDomainAndBounded
    (S T : PDS X Y) (D : Set (List X)) (q : Nat) : Prop :=
  PDS.HasDomain S D ∧ PDS.HasDomain T D ∧ QBounded D q

/-- The slice bundle is symmetric in its two systems: it is a conjunction of
one clause per side and a clause about `D` alone. -/
theorem PDS.HaveCommonDomainAndBounded.symm {S T : PDS X Y} {D : Set (List X)}
    {q : Nat} (h : PDS.HaveCommonDomainAndBounded S T D q) :
    PDS.HaveCommonDomainAndBounded T S D q :=
  ⟨h.2.1, h.1, h.2.2⟩

/-- The slice is inherited by a longer budget: a `q`-bounded domain is
`q'`-bounded for every `q' ≥ q`. -/
theorem PDS.HaveCommonDomainAndBounded.mono {S T : PDS X Y} {D : Set (List X)}
    {q q' : Nat} (h : PDS.HaveCommonDomainAndBounded S T D q) (hq : q ≤ q') :
    PDS.HaveCommonDomainAndBounded S T D q' :=
  ⟨h.1, h.2.1, fun l hl => (h.2.2 l hl).trans hq⟩

open Classical in
/-- The finite set of first `Option`-answers occurring on either side at `x`.

It is finite because a PDS has finite support; no finiteness assumption on the
answer alphabet is needed. -/
noncomputable def PDS.firstAnswerImage
    (S T : PDS X Y) (x : X) : Finset (Option Y) :=
  (S.support ∪ T.support).image fun s =>
    System.output (System.fullyDefined s) [x]
      (by rw [System.dom_fullyDefined]; simp)

open Classical in
/-- The finite set of queries admitted as a first query by `D`. -/
noncomputable def PDS.firstQueries [Fintype X] (D : Set (List X)) : Finset X :=
  Finset.univ.filter fun x => [x] ∈ D

open Classical in
/-- The finite set of realized proper first answers on either side.  Finiteness
comes from PDS support, not from an ambient `[Fintype Y]`. -/
noncomputable def PDS.firstAnsweredValues
    (S T : PDS X Y) (x : X) : Finset Y :=
  (PDS.firstAnswerImage S T x).biUnion Option.toFinset


open Classical in
/-- Successor sampling preserves honesty.  This invariant has to be stated
explicitly now that the distribution carrier itself permits signed mass. -/
theorem PDS.successorTransform_nonNeg_of_nonNeg {S : PDS X Y}
    (hS : S.NonNeg) (x : X) (y : Option Y) :
    (PDS.successorTransform S x y).NonNeg := by
  unfold PDS.successorTransform
  refine Distribution.NonNeg.fTransform ?_ _
  intro s
  rw [Finsupp.filter_apply]
  split
  · exact hS s
  · exact le_rfl

open Classical in
/-- Membership in the proper-answer carrier is exactly membership of the
corresponding `some` answer in the finite `Option` answer image. -/
theorem PDS.mem_first_answered_values_iff_some_mem_first_answer_image
    {S T : PDS X Y} {x : X} {v : Y} :
    v ∈ PDS.firstAnsweredValues S T x ↔
      some v ∈ PDS.firstAnswerImage S T x := by
  unfold PDS.firstAnsweredValues
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨y, hy, hv⟩
    cases y with
    | none => simp at hv
    | some v' =>
        simp only [Option.toFinset_some, Finset.mem_singleton] at hv
        subst v'
        exact hy
  · intro hv
    exact ⟨some v, hv, by simp⟩

/-- A finite first-query carrier exposes exactly the singleton histories in
its defining domain. -/
theorem PDS.mem_first_queries_iff_singleton_mem_domain [Fintype X]
    {D : Set (List X)} {x : X} :
    x ∈ PDS.firstQueries D ↔ [x] ∈ D := by
  classical
  simp [PDS.firstQueries]


/-! ## Prepending an initial query (Theorem 2.31's reassembly move)

Quarry architecture: `RandomSystems/RandomSystem.lean:2193` (`DDS.prepend`),
`:2346` (`prependTransform`), `:2469` (the branch-additivity of `δ`), `:2576`
(the transcript law of one prepended class).

`prepend x y s` answers the first query `x` with `y` and then continues as `s`.
The answered case `y = some v` is the thesis's own construction: domain
`{[x]} ∪ x‖dom s`, value `v` at `[x]`, `s`'s value beyond, undefined at every
other first query.  The `⊥`-answer case `y = none` has no thesis analogue (the
thesis totalizes over a finite alphabet): by CR18 Definition 3.3's skip
semantics a `⊥` at `x` leaves the state unchanged, so the continuation is `s`
itself, unshifted, with the `x`-headed part of the domain carved out —
validity forces the carving, since `[x] ∉ dom` propagates to every
`x`-headed history by prefix closure. -/
def System.DDS.prepend (x : X) (y : Option Y)
    (s : System.DDS X Y) : System.DDS X Y :=
  match y with
  | some v =>
      ⟨fun l => match l with
        | [] => Part.none
        | [x'] => ⟨x' = x, fun _ => v⟩
        | x' :: c :: m =>
            ⟨x' = x ∧ (s.1 (c :: m)).Dom, fun h => (s.1 (c :: m)).get h.2⟩,
       by
        constructor
        · exact fun h => h
        · intro l₁ l₂ hpre hne hdom
          obtain ⟨u, rfl⟩ := hpre
          cases l₁ with
          | nil => exact absurd rfl hne
          | cons a m =>
              cases m with
              | nil =>
                  cases u with
                  | nil => exact hdom
                  | cons c u' => exact hdom.1
              | cons c m' =>
                  exact ⟨hdom.1, s.2.2
                    (List.cons_prefix_cons.mpr ⟨rfl, List.prefix_append m' u⟩)
                    (List.cons_ne_nil c m') hdom.2⟩⟩
  | none =>
      System.filterDom (fun l => l.head? ≠ some x)
        (fun l₁ l₂ hpre h2 => by
          obtain ⟨u, rfl⟩ := hpre
          cases l₁ with
          | nil => simp
          | cons a m => exact h2)
        s

/-- The prepended query is answered: `[x] ∈ dom (prepend x y s)` for
`y = some v`. -/
theorem System.singleton_mem_dom_prepend_some (x : X) (v : Y) (s : System.DDS X Y) :
    [x] ∈ System.dom (System.DDS.prepend x (some v) s) :=
  rfl

/-- The prepended query is `⊥`-answered: `[x] ∉ dom (prepend x none s)`. -/
theorem System.singleton_not_mem_dom_prepend_none (x : X) (s : System.DDS X Y) :
    [x] ∉ System.dom (System.DDS.prepend x none s) :=
  fun h => h.2 rfl

/-- Thesis §2.4.2 step 3, answered case: the domain of `prepend x (some v) s`
is `{[x]} ∪ x‖dom s`. -/
theorem System.dom_prepend_some (x : X) (v : Y) (s : System.DDS X Y) :
    System.dom (System.DDS.prepend x (some v) s)
      = {l : List X | l = [x] ∨ ∃ m ∈ System.dom s, l = x :: m} := by
  ext l
  rcases l with _ | ⟨a, _ | ⟨c, m⟩⟩
  · exact iff_of_false (fun h => h)
      (by rintro (h | ⟨m, _, h⟩) <;> simp at h)
  · show a = x ↔ _
    constructor
    · rintro rfl
      exact Or.inl rfl
    · rintro (h | ⟨m', hm', h⟩) <;> exact (List.cons_eq_cons.mp h).1
  · show a = x ∧ (s.1 (c :: m)).Dom ↔ _
    constructor
    · rintro ⟨rfl, hD⟩
      exact Or.inr ⟨c :: m, hD, rfl⟩
    · rintro (h | ⟨m', hm', h⟩)
      · exact absurd h (by simp)
      · exact ⟨(List.cons_eq_cons.mp h).1,
          by rw [(List.cons_eq_cons.mp h).2]; exact hm'⟩

/-- Thesis §2.4.2 step 3, `⊥`-answer case: prepending a `⊥` carves the
`x`-headed histories out of the domain and keeps the rest. -/
theorem System.dom_prepend_none (x : X) (s : System.DDS X Y) :
    System.dom (System.DDS.prepend x none s)
      = {l ∈ System.dom s | l.head? ≠ some x} :=
  rfl

/-- CR18 Def 3.3 skip semantics, prepend side: on a system that does
not answer `x`, prepending the `⊥`-answer at `x` carves nothing —
`prepend x none s = s`.  (Every use site has this hypothesis for free:
a PDS equivalent to a `⊥`-branch successor transformation puts all its
mass on atoms that do not answer `x`.) -/
theorem System.prepend_none_of_not_mem {s : System.DDS X Y} {x : X}
    (hx : [x] ∉ System.dom s) :
    System.DDS.prepend x none s = s := by
  refine Subtype.ext (funext fun l => ?_)
  refine Part.ext' ?_ fun h₁ h₂ => rfl
  show (s.1 l).Dom ∧ l.head? ≠ some x ↔ (s.1 l).Dom
  refine and_iff_left_of_imp fun hD heq => ?_
  cases l with
  | nil => simp at heq
  | cons a m =>
      have ha : a = x := Option.some.inj heq
      exact hx (System.prefix_closed s
        (List.cons_prefix_cons.mpr ⟨ha.symm, List.nil_prefix⟩)
        (List.cons_ne_nil x []) hD)

/-- Thesis §2.4.2 step 3, the inversion law: after prepending `(x, v)`
the successor at `x` recovers `s` — `(prepend x (some v) s)↑x = s`. -/
theorem System.successor_prepend (x : X) (v : Y) (s : System.DDS X Y) :
    System.DDS.successor (System.DDS.prepend x (some v) s) x = s := by
  refine Subtype.ext (funext fun l => ?_)
  cases l with
  | nil =>
      refine Part.ext'
        (iff_of_false (System.empty_not_mem _) (System.empty_not_mem s))
        fun h₁ _ => absurd h₁ (System.empty_not_mem _)
  | cons a m =>
      rw [System.successor_apply_of_mem (System.singleton_mem_dom_prepend_some x v s)
        (List.cons_ne_nil a m)]
      refine Part.ext' ?_ fun h₁ h₂ => rfl
      show x = x ∧ (s.1 (a :: m)).Dom ↔ (s.1 (a :: m)).Dom
      exact and_iff_right rfl

/-- The inversion law in the `⊥`-answer case: the prepended `⊥` is a
skipped query (CR18 Def 3.3), so the successor at `x` recovers `s`
whenever `s` does not answer `x`. -/
theorem System.successor_prepend_none {s : System.DDS X Y} {x : X}
    (hx : [x] ∉ System.dom s) :
    System.DDS.successor (System.DDS.prepend x none s) x = s := by
  rw [System.prepend_none_of_not_mem hx, System.successor_of_not_mem hx]

/-- Thesis §2.4.2 step 3: the prepended system's first `s⊥`-answer to
`x` is exactly the prepended answer `y` (the `⊥` case included). -/
theorem System.output_fullyDefined_prepend (x : X) (y : Option Y)
    (s : System.DDS X Y) :
    System.output (System.fullyDefined (System.DDS.prepend x y s)) [x]
      (by rw [System.dom_fullyDefined]; simp) = y := by
  cases y with
  | some v =>
      exact System.output_fullyDefined_append_of_mem
        (System.DDS.prepend x (some v) s) [] x (Or.inr rfl)
        (System.singleton_mem_dom_prepend_some x v s)
  | none =>
      simp only [System.output_fullyDefined]
      split
      · rename_i hmem
        exact absurd hmem (System.singleton_not_mem_dom_prepend_none x s)
      · rfl

/-- Thesis §2.4.2 step 3: prepending an **answered** query is injective
(`(prepend x (some v))↑x` is a left inverse), so its pushforward
preserves `δ`.  Prepending a `⊥` is *not* injective: validity forbids
storing the carved `x`-branch, so systems differing only there are
identified — on the systems the proof feeds it (`[x] ∉ dom s`) it is
the identity (`System.prepend_none_of_not_mem`). -/
theorem System.prepend_injective (x : X) (v : Y) :
    Function.Injective (System.DDS.prepend x (some v)) :=
  Function.LeftInverse.injective
    (g := fun s => System.DDS.successor s x)
    fun s => System.successor_prepend x v s

/-- Thesis §2.4.2 step 3 at the distribution level: `S′ₓᵧ` is the
`prepend x y`-transformation of a rebuilt representative. -/
noncomputable def PDS.prependTransform (S : PDS X Y) (x : X)
    (y : Option Y) : PDS X Y :=
  Distribution.fTransform (System.DDS.prepend x y) S

/-- On a PDS all of whose atoms `⊥`-answer `x`, prepending the
`⊥`-answer is the identity transformation. -/
theorem PDS.prependTransform_of_forall_not_mem {S : PDS X Y} {x : X}
    (h : ∀ s ∈ S.support, [x] ∉ System.dom s) :
    PDS.prependTransform S x none = S :=
  Eq.trans (Distribution.fTransform_congr (g := id) S
    fun s hs => System.prepend_none_of_not_mem (h s hs)) (Distribution.fTransform_id S)

open Classical in
/-- Thesis §2.4.2 step 3, the round trip: `(S′ₓᵧ)↑x↓y = S` — the
successor transformation at `(x, y)` undoes the prepend
transformation.  Every prepended atom answers `y` first
(`System.output_fullyDefined_prepend`), so the filter keeps everything, and
the successor inverts the prepend atom-wise.  The `⊥`-answer case
needs the (use-site-free) hypothesis that no atom of `S` answers `x`. -/
theorem PDS.successorTransform_prependTransform (S : PDS X Y) (x : X)
    (y : Option Y) (h : y = none → ∀ s ∈ S.support, [x] ∉ System.dom s) :
    PDS.successorTransform (PDS.prependTransform S x y) x y = S := by
  unfold PDS.successorTransform PDS.prependTransform
  have hfil : (Distribution.fTransform (System.DDS.prepend x y) S).filter
      (fun s => System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp) = y)
      = Distribution.fTransform (System.DDS.prepend x y) S := by
    refine Finsupp.ext fun t => ?_
    rw [Finsupp.filter_apply]
    by_cases ht : t ∈ (Distribution.fTransform (System.DDS.prepend x y) S).support
    · obtain ⟨s', hs', rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support ht)
      rw [if_pos (System.output_fullyDefined_prepend x y s')]
    · rw [Finsupp.notMem_support_iff.mp ht]
      exact ite_self 0
  rw [hfil, Distribution.fTransform_comp]
  refine Eq.trans (Distribution.fTransform_congr (g := id) S ?_)
    (Distribution.fTransform_id S)
  intro s hs
  show System.DDS.successor (System.DDS.prepend x y s) x = s
  cases y with
  | some v => exact System.successor_prepend x v s
  | none => exact System.successor_prepend_none (h rfl s hs)

/-- Thesis §2.4.2 step 3: the prepend transformation preserves the
statistical distance (answered case; injectivity plus
`Probability.statDist_fTransform_injective`).

The quarry's `δ`-level companion carries a non-negativity hypothesis on the
right-hand law; `statDist` does not need one, because it indexes its sum by the
support of the *difference* rather than by the support of its first
argument. -/
theorem PDS.statDist_prependTransform (S T : PDS X Y) (x : X) (v : Y) :
    statDist (PDS.prependTransform S x (some v)) (PDS.prependTransform T x (some v))
      = statDist S T :=
  Probability.statDist_fTransform_injective S T _ (System.prepend_injective x v)

/-- The `⊥`-answer case of `PDS.statDist_prependTransform`: on PDS whose atoms all
`⊥`-answer `x`, the prepend transformation is the identity, so `δ` is
trivially preserved. -/
theorem PDS.statDist_prependTransform_none {S T : PDS X Y} {x : X}
    (hS : ∀ s ∈ S.support, [x] ∉ System.dom s)
    (hT : ∀ t ∈ T.support, [x] ∉ System.dom t) :
    statDist (PDS.prependTransform S x none) (PDS.prependTransform T x none) = statDist S T := by
  rw [PDS.prependTransform_of_forall_not_mem hS,
    PDS.prependTransform_of_forall_not_mem hT]

/-! ### Per-x reassembly (thesis §2.4.2, Theorem 2.31 steps 4–5) -/

/-- Distinct first answers give distinct prepended atoms: the first
`s⊥`-answer at `x` is part of the atom (`System.output_fullyDefined_prepend`),
whatever the continuations.  In particular a `⊥`-class atom never
collides with an answered-class atom (their domains differ at `[x]`),
and two answered classes never collide however their continuations
overlap. -/
theorem System.prepend_ne_of_ne {x : X} {y y' : Option Y} (h : y ≠ y')
    (s s' : System.DDS X Y) :
    System.DDS.prepend x y s ≠ System.DDS.prepend x y' s' := by
  intro heq
  have h1 := System.output_fullyDefined_prepend x y s
  simp only [heq] at h1
  exact h (h1.symm.trans (System.output_fullyDefined_prepend x y' s'))

open Classical in
/-- The support of a prepend transformation consists of prepended
atoms. -/
theorem PDS.support_prependTransform_subset {S : PDS X Y} {x : X}
    {y : Option Y} :
    (PDS.prependTransform S x y).support
      ⊆ S.support.image (System.DDS.prepend x y) :=
  Finsupp.mapDomain_support

open Classical in
/-- Thesis §2.4.2 step 4: the classes of the per-`x` reassembly have
pairwise disjoint supports — every atom carries its first answer. -/
theorem PDS.pairwiseDisjoint_support_prependTransform
    (Sf Tf : Option Y → PDS X Y) (x : X) (ys : Finset (Option Y)) :
    (↑ys : Set (Option Y)).PairwiseDisjoint fun y =>
      (PDS.prependTransform (Sf y) x y).support
        ∪ (PDS.prependTransform (Tf y) x y).support := by
  intro y _ y' _ hne
  refine Finset.disjoint_left.mpr fun t ht ht' => ?_
  have h1 : ∃ s, t = System.DDS.prepend x y s := by
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (PDS.support_prependTransform_subset h)
      exact ⟨s, rfl⟩
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (PDS.support_prependTransform_subset h)
      exact ⟨s, rfl⟩
  have h2 : ∃ s', t = System.DDS.prepend x y' s' := by
    rcases Finset.mem_union.mp ht' with h | h
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (PDS.support_prependTransform_subset h)
      exact ⟨s, rfl⟩
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (PDS.support_prependTransform_subset h)
      exact ⟨s, rfl⟩
  obtain ⟨s, rfl⟩ := h1
  obtain ⟨s', heq⟩ := h2
  exact System.prepend_ne_of_ne hne s s' heq

open Classical in
/-- Thesis §2.4.2 step 4 (LanMau20 Lemma 2 again): the statistical
distance of per-`x` reassemblies is the sum of the per-answer
distances — the classes are support-disjoint, prepending an answered
query preserves `δ` by injectivity, and the `⊥`-class prepend is the
identity on its pass-through support. -/
theorem PDS.statDist_sum_prependTransform (Sf Tf : Option Y → PDS X Y) (x : X)
    (ys : Finset (Option Y))
    (hS : none ∈ ys → ∀ s ∈ (Sf none).support, [x] ∉ System.dom s)
    (hT : none ∈ ys → ∀ t ∈ (Tf none).support, [x] ∉ System.dom t) :
    statDist (∑ y ∈ ys, PDS.prependTransform (Sf y) x y)
        (∑ y ∈ ys, PDS.prependTransform (Tf y) x y)
      = ∑ y ∈ ys, statDist (Sf y) (Tf y) := by
  refine Eq.trans (Probability.statDist_sum_of_disjoint_support _ _
    (PDS.pairwiseDisjoint_support_prependTransform Sf Tf x ys)) ?_
  refine Finset.sum_congr rfl fun y hy => ?_
  cases y with
  | none => exact PDS.statDist_prependTransform_none (hS hy) (hT hy)
  | some v => exact PDS.statDist_prependTransform (Sf (some v)) (Tf (some v)) x v

/-- The prepend transformation preserves weight (it is a pushforward). -/
theorem PDS.weight_prependTransform (S : PDS X Y) (x : X) (y : Option Y) :
    (PDS.prependTransform S x y).weight = S.weight :=
  Distribution.weight_fTransform _ _

/-- Thesis §2.4.2 step 5's bookkeeping: the reassembled PDS carries the
total weight of its classes. -/
theorem PDS.weight_sum_prependTransform (Sf : Option Y → PDS X Y) (x : X)
    (ys : Finset (Option Y)) :
    (∑ y ∈ ys, PDS.prependTransform (Sf y) x y).weight
      = ∑ y ∈ ys, (Sf y).weight := by
  rw [Distribution.weight_finset_sum]
  exact Finset.sum_congr rfl fun y _ => PDS.weight_prependTransform (Sf y) x y

open Classical in
theorem PDS.successorTransform_finset_sum {ι : Type*} (t : Finset ι)
    (Rf : ι → PDS X Y) (x : X) (y : Option Y) :
    PDS.successorTransform (∑ i ∈ t, Rf i) x y
      = ∑ i ∈ t, PDS.successorTransform (Rf i) x y := by
  show Finsupp.mapDomain (fun s => System.DDS.successor s x)
      (Finsupp.filter (fun s => System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp) = y) (∑ i ∈ t, Rf i))
    = ∑ i ∈ t, Finsupp.mapDomain (fun s => System.DDS.successor s x)
        (Finsupp.filter (fun s => System.output (System.fullyDefined s) [x]
          (by rw [System.dom_fullyDefined]; simp) = y) (Rf i))
  rw [Finsupp.filter_sum, Finsupp.mapDomain_finset_sum]

open Classical in
/-- A prepended class answers only its own `y`: at any other first
answer the successor transformation of the class vanishes. -/
theorem PDS.successorTransform_prependTransform_of_ne {S : PDS X Y}
    {x : X} {y y' : Option Y} (h : y ≠ y') :
    PDS.successorTransform (PDS.prependTransform S x y) x y' = 0 := by
  unfold PDS.successorTransform PDS.prependTransform
  have hfil : (Distribution.fTransform (System.DDS.prepend x y) S).filter
      (fun s => System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp) = y')
      = 0 := by
    refine Finsupp.ext fun t => ?_
    rw [Finsupp.filter_apply]
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_cases ht : t ∈ (Distribution.fTransform (System.DDS.prepend x y) S).support
    · obtain ⟨s', _, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support ht)
      rw [if_neg fun hP =>
        h ((System.output_fullyDefined_prepend x y s').symm.trans hP)]
    · rw [Finsupp.notMem_support_iff.mp ht, ite_self]
  rw [hfil]
  exact Finsupp.mapDomain_zero

open Classical in
/-- Thesis §2.4.2 step 5: the successor transformation at `(x, y)`
recovers the `y`-class of the per-`x` reassembly — the other classes
vanish and the `(x, y)`-round trip undoes the prepend. -/
theorem PDS.successorTransform_sum_prependTransform
    (Sf : Option Y → PDS X Y) (x : X) (ys : Finset (Option Y))
    {y : Option Y} (hy : y ∈ ys)
    (hnone : y = none → ∀ s ∈ (Sf none).support, [x] ∉ System.dom s) :
    PDS.successorTransform (∑ y' ∈ ys, PDS.prependTransform (Sf y') x y') x y
      = Sf y := by
  rw [PDS.successorTransform_finset_sum]
  rw [Finset.sum_eq_single_of_mem y hy
    fun y' _ hne => PDS.successorTransform_prependTransform_of_ne hne]
  exact PDS.successorTransform_prependTransform (Sf y) x y
    fun h => by subst h; exact hnone rfl


theorem PDS.trLawFullyDefined_finset_sum {ι : Type*} (t : Finset ι)
    (Rf : ι → PDS X Y) (e : System.DDE.Total Y X) (n : ℕ) :
    trLawFullyDefined e n (∑ i ∈ t, Rf i)
      = ∑ i ∈ t, trLawFullyDefined e n (Rf i) := by
  show Finsupp.mapDomain (fun s => System.DDE.Total.transcript s e n) (∑ i ∈ t, Rf i)
    = ∑ i ∈ t, Finsupp.mapDomain (fun s => System.DDE.Total.transcript s e n) (Rf i)
  rw [Finsupp.mapDomain_finset_sum]

open Classical in
/-- Thesis §2.4.2 step 6 ingredient, per class: the transcript
distribution of one prepended class, in an environment opening with
`x`, is the `(x, y)`-cons pushforward of the class representative's
transcript distribution in the successor environment
(`PDS.trLawFullyDefined_successor` read backwards through the round trip). -/
theorem PDS.trLawFullyDefined_prependTransform (S : PDS X Y) {x : X}
    (y : Option Y) {e : System.DDE.Total Y X} (he : e [] = some x)
    (hnone : y = none → ∀ s ∈ S.support, [x] ∉ System.dom s) (n : ℕ) :
    trLawFullyDefined e (n + 1) (PDS.prependTransform S x y)
      = Distribution.fTransform (fun t => (x, y) :: t)
          (trLawFullyDefined (System.DDE.Total.successor e y) n S) := by
  rcases eq_or_ne S 0 with rfl | hS0
  · simp only [PDS.prependTransform, trLawFullyDefined   , Distribution.fTransform_zero]
  · have hne : (PDS.prependTransform S x y).support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      cases y with
      | none =>
          rw [PDS.prependTransform_of_forall_not_mem (hnone rfl)]
          exact hS0
      | some v =>
          intro h0
          exact hS0 ((Finsupp.mapDomain_injective (System.prepend_injective x v))
            (h0.trans Finsupp.mapDomain_zero.symm))
    rw [PDS.trLawFullyDefined_successor (PDS.prependTransform S x y) e he n]
    have himg : (PDS.prependTransform S x y).support.image
        (fun s => System.output (System.fullyDefined s) [x]
          (by rw [System.dom_fullyDefined]; simp)) = {y} := by
      refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr
        ⟨hne.image _, ?_⟩
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨s', _, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support ht)
      exact System.output_fullyDefined_prepend x y s'
    rw [himg, Finset.sum_singleton,
      PDS.successorTransform_prependTransform S x y hnone]

open Classical in
/-- Thesis §2.4.2 step 6 ingredient: in an environment opening with
`x`, the transcript distribution of the per-`x` reassembly decomposes
into the per-answer cons-pushforwards of the class representatives'
transcript distributions in the successor environments. -/
theorem PDS.trLawFullyDefined_sum_prependTransform
    (Sf : Option Y → PDS X Y) (x : X) (ys : Finset (Option Y))
    {e : System.DDE.Total Y X} (he : e [] = some x)
    (hnone : none ∈ ys → ∀ s ∈ (Sf none).support, [x] ∉ System.dom s)
    (n : ℕ) :
    trLawFullyDefined e (n + 1) (∑ y ∈ ys, PDS.prependTransform (Sf y) x y)
      = ∑ y ∈ ys, Distribution.fTransform (fun t => (x, y) :: t)
          (trLawFullyDefined (System.DDE.Total.successor e y) n (Sf y)) := by
  rw [PDS.trLawFullyDefined_finset_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  exact PDS.trLawFullyDefined_prependTransform (Sf y) y he
    (fun h => by subst h; exact hnone hy) n

/-! ### Lanzenberger Lemma 2.5 at the first-answer branches

Quarry architecture: `RandomSystems/TranscriptBranchDistance.lean:35`.  The
partition is by the first entry of the transcript, whose disjointness is
*derived* from the distinct first answers rather than assumed. -/

open Classical in
/-- **Lemma 2.5, as the attainment induction consumes it**: statistical
distance is additive across finitely many transcript branches whose distinct
first answers make their pushed-forward supports disjoint.

The quarry's `δ`-level form carries a branchwise non-negativity hypothesis on
the right-hand family, and defends it as Lemma 2.5's own: `δ μ ν = ∑ₐ max(μ a −
ν a, 0)` misses a cell where `ν` is negative and `μ` vanishes.  `statDist`
sums over the difference's support instead, so that cell is counted on both
sides and the hypothesis is not needed here. -/
theorem System.statDist_sum_cons_fTransform (x : X) (ys : Finset (Option Y))
    (Sf Tf : Option Y → Distribution (List (X × Option Y))) :
    statDist (∑ y ∈ ys, Distribution.fTransform (fun t => (x, y) :: t) (Sf y))
        (∑ y ∈ ys, Distribution.fTransform (fun t => (x, y) :: t) (Tf y))
      = ∑ y ∈ ys, statDist (Sf y) (Tf y) := by
  have hdisj : (↑ys : Set (Option Y)).PairwiseDisjoint fun y =>
      (Distribution.fTransform (fun t => (x, y) :: t) (Sf y)).support ∪
        (Distribution.fTransform (fun t => (x, y) :: t) (Tf y)).support := by
    intro y _ y' _ hne
    refine Finset.disjoint_left.mpr fun t ht ht' => ?_
    have hleft : ∃ s, t = (x, y) :: s := by
      rcases Finset.mem_union.mp ht with hs | hs
      · obtain ⟨s, _, hs⟩ := Distribution.mem_support_fTransform _ _ hs
        exact ⟨s, hs.symm⟩
      · obtain ⟨s, _, hs⟩ := Distribution.mem_support_fTransform _ _ hs
        exact ⟨s, hs.symm⟩
    have hright : ∃ s, t = (x, y') :: s := by
      rcases Finset.mem_union.mp ht' with hs | hs
      · obtain ⟨s, _, hs⟩ := Distribution.mem_support_fTransform _ _ hs
        exact ⟨s, hs.symm⟩
      · obtain ⟨s, _, hs⟩ := Distribution.mem_support_fTransform _ _ hs
        exact ⟨s, hs.symm⟩
    obtain ⟨s, hs⟩ := hleft
    obtain ⟨s', hs'⟩ := hright
    exact hne (congrArg Prod.snd (List.cons.inj (hs.symm.trans hs')).1)
  refine Eq.trans (Probability.statDist_sum_of_disjoint_support _ _ hdisj) ?_
  exact Finset.sum_congr rfl fun y _ =>
    Probability.statDist_fTransform_injective (Sf y) (Tf y) _
      fun _ _ h => (List.cons.inj h).2

/-- The nowhere-defined system refuses every history.  `System.dom_emptySystem`
in the `∉` form the glue calculus reads. -/
theorem System.notMem_dom_emptySystem (l : List X) :
    l ∉ System.dom (System.emptySystem : System.DDS X Y) := by
  rw [System.dom_emptySystem]
  exact Set.notMem_empty l

/-! ## Lanzenberger Lemma 2.33: the joint of a family of branch pairs

Quarry architecture: `RandomSystems/RandomSystem.lean:2757` (the glue
constructor), `:3167`–`:3439` (per-class choices and the cross-class joint),
`:3771` (the distance identity), `:4075`/`:4113` (the witness and its
existence).

The construction.  Each participating class `i` gets a *choice law* — a
distribution over `Option (Y × DDS X Y)`, one first answer together with its
continuation.  The two sides' choice laws at `i` share the mass
`choiceOf i ⊓ choiceOf i`, of weight `overlapOf i`, and the whole construction
turns on `τ = min_{i ∈ C} overlapOf i`: the shared component is *trimmed* to
that common weight (`trimOf`), the two residual components have disjoint
supports at every class, and the class-indexed profiles are glued into one
deterministic system per sample (`glueProfile`).  The result is a pair of
systems agreeing exactly on mass `τ`, so

  `δ(left, right) = wS − τ = max_{i ∈ C} ∑_v δ(Bs i v, Bt i v)`,

the **`max`** over classes, which is what the induction's adaptive step
`sup_e = max_x ∑_y sup_{e'}` needs.  `PDS.FiniteClassJointWitness` records that
`max` as a pair of fields rather than as a `Finset.max'`:
`statDist_eq_selected_sum` at an attaining class `chosen`, and
`branch_sum_le_statDist` at every class.

**Orientation caution (thesis errata).**  The thesis's own `min`/`max` over
classes is misprinted at the neighbouring Theorem 2.29, whose upper bound
prints `min_{i≠j}` where the correct reading is `max_{i≠j}`; the printed form
is refuted kernel-checked in the quarry
(`MultiSystemCoupling.lean:958 printed_min_form_counterexample`, three laws on
`Fin 3`).  Nothing printed is transplanted here — the orientation above is
derived from the construction (`τ` is the *minimum* overlap, hence the
*maximum* distance), and it is the quarry's own reading of Lemma 2.33.

`System.DDS.glue` is the tuple-atom constructor of the cross-query joint: a
glued atom selects one per-query slice for each first query, and no product
over `X` is ever formed. -/
def System.DDS.glue (g : X → System.DDS X Y) : System.DDS X Y :=
  ⟨fun l => match l with
    | [] => Part.none
    | x :: m => (g x).1 (x :: m),
   by
    constructor
    · exact fun h => h
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨u, rfl⟩ := hpre
      cases l₁ with
      | nil => exact absurd rfl hne
      | cons a m =>
          exact (g a).2.2
            (List.cons_prefix_cons.mpr ⟨rfl, List.prefix_append m u⟩)
            (List.cons_ne_nil a m) hdom⟩

/-- The glued system consults the `x`-slice on `x`-headed histories. -/
theorem System.glue_apply_cons (g : X → System.DDS X Y) (x : X) (m : List X) :
    (System.DDS.glue g).1 (x :: m) = (g x).1 (x :: m) :=
  rfl

/-- Membership in the glued domain is per-slice. -/
theorem System.cons_mem_dom_glue (g : X → System.DDS X Y) (x : X) (m : List X) :
    x :: m ∈ System.dom (System.DDS.glue g)
      ↔ x :: m ∈ System.dom (g x) :=
  Iff.rfl

/-- The glued system's first `s⊥`-answer to `x` is the `x`-slice's
first answer — unconditionally (the `⊥` case included). -/
theorem System.output_fullyDefined_glue (g : X → System.DDS X Y) (x : X) :
    System.output (System.fullyDefined (System.DDS.glue g)) [x]
      (by rw [System.dom_fullyDefined]; simp)
      = System.output (System.fullyDefined (g x)) [x]
        (by rw [System.dom_fullyDefined]; simp) :=
  rfl

/-- Thesis §2.4.2 footnote 8, answered case: after an answered first
query `x` the glued system continues as the `x`-slice's successor. -/
theorem System.successor_glue (g : X → System.DDS X Y) (x : X)
    (hx : [x] ∈ System.dom (g x)) :
    System.DDS.successor (System.DDS.glue g) x
      = System.DDS.successor (g x) x := by
  unfold System.DDS.successor
  rw [if_pos (show [x] ∈ System.dom (System.DDS.glue g) from hx),
    if_pos hx]
  rfl

/-- CR18 Def 3.3 skip semantics at the joint: a `⊥`-answered first
query leaves the whole glued state unchanged (`glue g`, not `g x` —
the joint must keep its other branches alive for requeries). -/
theorem System.successor_glue_of_not_mem (g : X → System.DDS X Y) (x : X)
    (hx : [x] ∉ System.dom (g x)) :
    System.DDS.successor (System.DDS.glue g) x = System.DDS.glue g :=
  successor_of_not_mem fun h => hx h

/-- Milestone-2 compatibility: a glued family of prepended slices
answers the prescribed first answer at every first query. -/
theorem System.output_fullyDefined_glue_prepend (yf : X → Option Y)
    (sf : X → System.DDS X Y) (x : X) :
    System.output (System.fullyDefined (System.DDS.glue
        (fun x' => System.DDS.prepend x' (yf x') (sf x')))) [x]
      (by rw [System.dom_fullyDefined]; simp) = yf x :=
  (System.output_fullyDefined_glue _ x).trans
    (output_fullyDefined_prepend x (yf x) (sf x))

/-- Milestone-2 compatibility, answered case: the successor of a glued
prepended family at an answered first query recovers the prescribed
continuation slice. -/
theorem System.successor_glue_prepend (yf : X → Option Y)
    (sf : X → System.DDS X Y) (x : X) {v : Y} (hv : yf x = some v) :
    System.DDS.successor (System.DDS.glue
        (fun x' => System.DDS.prepend x' (yf x') (sf x'))) x
      = sf x := by
  rw [System.successor_glue _ x
    (by rw [hv]; exact singleton_mem_dom_prepend_some x v (sf x))]
  rw [hv]
  exact successor_prepend x v (sf x)

/-! ### Cross-query joint groundwork (thesis Lemma 2.33) -/

/-- CR18 Def 3.3: the first `s⊥`-answer to `x` is `⊥` exactly on
systems that do not answer `x`. -/

theorem System.output_fullyDefined_glue_empty (g : X → System.DDS X Y) (x : X)
    (hg : g x = System.emptySystem) :
    System.output (System.fullyDefined (System.DDS.glue g)) [x]
      (by rw [System.dom_fullyDefined]; simp) = none := by
  rw [System.output_fullyDefined_glue g x]
  exact System.output_fullyDefined_eq_none_iff.mpr (by rw [hg]; exact (System.notMem_dom_emptySystem [x]))

-- Further local copies of `Distribution`-level plumbing for the cross-query
-- joint (to be upstreamed into `Distribution.lean` once it is free to rebuild).


def System.sliceOf (c : Option (Y × System.DDS X Y)) (x : X) :
    System.DDS X Y :=
  match c with
  | some (v, a) => System.DDS.prepend x (some v) a
  | none => System.emptySystem

/-- Thesis §2.4.2 footnote 8: the tuple atom of the cross-query joint —
glue the slices selected by a choice profile, one per class. -/
def System.glueProfile {I : Type*} (cls : X → I)
    (p : I → Option (Y × System.DDS X Y)) : System.DDS X Y :=
  System.DDS.glue fun x => System.sliceOf (p (cls x)) x

/-- The continuation selected by a choice (the `⊥`-choice selects the
inert empty system). -/
def System.contOf (c : Option (Y × System.DDS X Y)) : System.DDS X Y :=
  (Option.map Prod.snd c).getD System.emptySystem

theorem System.output_fullyDefined_glueProfile {I : Type*} (cls : X → I)
    (p : I → Option (Y × System.DDS X Y)) (x : X) :
    System.output (System.fullyDefined (System.glueProfile cls p)) [x]
      (by rw [System.dom_fullyDefined]; simp)
      = Option.map Prod.fst (p (cls x)) := by
  refine (System.output_fullyDefined_glue _ x).trans ?_
  rcases hp : p (cls x) with _ | ⟨v, a⟩
  · simp only [System.sliceOf, Option.map_none]
    exact System.output_fullyDefined_eq_none_iff.mpr ((System.notMem_dom_emptySystem [x]))
  · simp only [System.sliceOf, Option.map_some]
    exact output_fullyDefined_prepend x (some v) a

theorem System.successor_glueProfile_some {I : Type*} {cls : X → I}
    {p : I → Option (Y × System.DDS X Y)} {x : X} {v : Y}
    {a : System.DDS X Y} (hp : p (cls x) = some (v, a)) :
    System.DDS.successor (System.glueProfile cls p) x = a := by
  have hmem : [x] ∈ System.dom (System.sliceOf (p (cls x)) x) := by
    rw [hp]
    exact singleton_mem_dom_prepend_some x v a
  refine Eq.trans (System.successor_glue _ x hmem) ?_
  have hkey : System.DDS.successor (System.sliceOf (p (cls x)) x) x = a := by
    rw [hp]
    exact successor_prepend x v a
  exact hkey

open Classical in
/-- The engine of the cross-query joint's marginals: the
`(x, some v)`-successor transformation of a glued-profile pushforward
is the continuation-pushforward of the `v`-filtered `cls x`-marginal
of the profile distribution. -/
theorem PDS.successorTransform_fTransform_glueProfile {I : Type*}
    (cls : X → I) (ρ : Distribution (I → Option (Y × System.DDS X Y)))
    (x : X) (v : Y) :
    PDS.successorTransform (Distribution.fTransform (System.glueProfile cls) ρ) x (some v)
      = Distribution.fTransform System.contOf
          ((Distribution.fTransform (fun p => p (cls x)) ρ).filter
            fun c => Option.map Prod.fst c = some v) := by
  unfold PDS.successorTransform
  have hfil : (Distribution.fTransform (System.glueProfile cls) ρ).filter
      (fun t => System.output (System.fullyDefined t) [x]
        (by rw [System.dom_fullyDefined]; simp) = some v)
      = Distribution.fTransform (System.glueProfile cls)
          (ρ.filter fun p => Option.map Prod.fst (p (cls x)) = some v) := by
    rw [Distribution.filter_fTransform]
    refine congrArg (Distribution.fTransform (System.glueProfile cls)) ?_
    refine Finsupp.ext fun p => ?_
    rw [Finsupp.filter_apply, Finsupp.filter_apply]
    by_cases hp : Option.map Prod.fst (p (cls x)) = some v
    · rw [if_pos hp,
        if_pos ((System.output_fullyDefined_glueProfile cls p x).trans hp)]
    · rw [if_neg hp, if_neg fun h => hp
        ((System.output_fullyDefined_glueProfile cls p x).symm.trans h)]
  rw [hfil, Distribution.fTransform_comp,
    Distribution.filter_fTransform (fun p => p (cls x)) ρ
      (fun c => Option.map Prod.fst c = some v),
    Distribution.fTransform_comp]
  refine Distribution.fTransform_congr _ fun p hp => ?_
  have hQ : Option.map Prod.fst (p (cls x)) = some v := by
    have hp' : p ∈ (ρ.filter fun q =>
        Option.map Prod.fst (q (cls x)) = some v).support := hp
    rw [Finsupp.support_filter] at hp'
    exact (Finset.mem_filter.mp hp').2
  rcases hc : p (cls x) with _ | ⟨v', a⟩
  · rw [hc] at hQ
    exact absurd hQ (by simp)
  · rw [hc] at hQ
    obtain rfl : v' = v := by simpa using hQ
    show System.DDS.successor (System.glueProfile cls p) x = System.contOf (p (cls x))
    rw [hc]
    exact System.successor_glueProfile_some hc


noncomputable def PDS.classChoiceDist (vs : Finset Y)
    (B : Y → PDS X Y) (β : ℝ) :
    Distribution (Option (Y × System.DDS X Y)) :=
  (∑ v ∈ vs, Distribution.fTransform (fun s => some (v, s)) (B v))
    + Finsupp.single none β

theorem PDS.weight_classChoiceDist (vs : Finset Y)
    (B : Y → PDS X Y) (β : ℝ) :
    (PDS.classChoiceDist vs B β).weight = (∑ v ∈ vs, (B v).weight) + β := by
  unfold PDS.classChoiceDist
  rw [Distribution.weight_add, Distribution.weight_finset_sum, Distribution.weight_single]
  refine congrArg (· + β) ?_
  exact Finset.sum_congr rfl fun v _ => Distribution.weight_fTransform _ _

open Classical in
theorem PDS.contOf_filter_classChoiceDist_of_mem {vs : Finset Y}
    {B : Y → PDS X Y} {β : ℝ} {v : Y} (hv : v ∈ vs) :
    Distribution.fTransform System.contOf ((PDS.classChoiceDist vs B β).filter
        fun c => Option.map Prod.fst c = some v)
      = B v := by
  have hside : ∀ v' ∈ vs, v' ≠ v →
      Distribution.fTransform System.contOf ((Distribution.fTransform
        (fun s : System.DDS X Y => some (v', s)) (B v')).filter
          fun c => Option.map Prod.fst c = some v) = 0 := by
    intro v' _ hne
    rw [Distribution.filter_fTransform, Distribution.filter_of_forall_not _ _ fun s => by simp [hne],
      Distribution.fTransform_zero, Distribution.fTransform_zero]
  unfold PDS.classChoiceDist
  rw [Finsupp.filter_add, Finsupp.filter_sum,
    Finsupp.filter_single_of_neg
      (p := fun c => Option.map Prod.fst c = some v) (by simp),
    add_zero, Distribution.fTransform_finset_sum,
    Finset.sum_eq_single_of_mem v hv hside, Distribution.filter_fTransform,
    Distribution.filter_of_forall _ _ fun s => by simp, Distribution.fTransform_comp,
    show (System.contOf ∘ fun s : System.DDS X Y => some (v, s)) = id from
      funext fun s => rfl, Distribution.fTransform_id]

open Classical in
theorem PDS.contOf_filter_classChoiceDist_of_not_mem {vs : Finset Y}
    {B : Y → PDS X Y} {β : ℝ} {v : Y} (hv : v ∉ vs) :
    Distribution.fTransform System.contOf ((PDS.classChoiceDist vs B β).filter
        fun c => Option.map Prod.fst c = some v)
      = 0 := by
  unfold PDS.classChoiceDist
  rw [Finsupp.filter_add, Finsupp.filter_sum,
    Finsupp.filter_single_of_neg
      (p := fun c => Option.map Prod.fst c = some v) (by simp),
    add_zero, Distribution.fTransform_finset_sum]
  refine Eq.trans (Finset.sum_congr rfl fun v' hv' => ?_)
    Finset.sum_const_zero
  have hne : v' ≠ v := fun h => hv (h ▸ hv')
  rw [Distribution.filter_fTransform, Distribution.filter_of_forall_not _ _ fun s => by simp [hne],
    Distribution.fTransform_zero, Distribution.fTransform_zero]

open Classical in
theorem PDS.filter_none_classChoiceDist (vs : Finset Y)
    (B : Y → PDS X Y) (β : ℝ) :
    (PDS.classChoiceDist vs B β).filter
        (fun c => Option.map Prod.fst c = none)
      = Finsupp.single none β := by
  unfold PDS.classChoiceDist
  rw [Finsupp.filter_add, Finsupp.filter_sum,
    Finsupp.filter_single_of_pos
      (p := fun c => Option.map Prod.fst c = none) (by simp)]
  refine Eq.trans (congrArg (· + Finsupp.single none β) ?_) (zero_add _)
  refine Eq.trans (Finset.sum_congr rfl fun v' _ => ?_)
    Finset.sum_const_zero
  rw [Distribution.filter_fTransform, Distribution.filter_of_forall_not _ _ fun s => by simp,
    Distribution.fTransform_zero]

open Classical in
/-- Thesis Lemma 2.33, the marginal half at the `A`-level: for any
shared summand `E ≤ A` of uniform weight, the `(x, some v)`-marginal of
the glued joint `E`-part + (( - )⁺)-part recovers the `v`-slice of the
class's own choice distribution. -/
theorem PDS.successorTransform_crossJointAtom {I : Type*} (cls : X → I)
    (C : Finset I) (E A : I → Distribution (Option (Y × System.DDS X Y)))
    (u w : ℝ)
    (hEnn : ∀ i ∈ C, (E i).NonNeg)
    (hE : ∀ i ∈ C, (E i).weight = u)
    (hA : ∀ i ∈ C, (A i).weight = w) (hle : ∀ i ∈ C, E i ≤ A i)
    {x : X} (hx : cls x ∈ C) (v : Y) :
    PDS.successorTransform (Distribution.fTransform (System.glueProfile cls)
        (Distribution.jointProfile u none C E
          + Distribution.jointProfile (w - u) none C fun i => A i - E i))
      x (some v)
      = Distribution.fTransform System.contOf
          ((A (cls x)).filter fun c => Option.map Prod.fst c = some v) := by
  have hX' : ∀ j ∈ C, Distribution.weight (A j - E j) = w - u := by
    intro j hj
    rw [Distribution.weight_sub _ _, hA j hj, hE j hj]
  rw [PDS.successorTransform_fTransform_glueProfile, Distribution.fTransform_add,
    Distribution.jointProfile_marginal u none C E hEnn hE hx,
    Distribution.jointProfile_marginal (w - u) none C _
      (fun j hj => Distribution.nonNeg_sub_of_le (hle j hj)) hX' hx,
    Distribution.add_sub_cancel']

/-- One side's per-class choice distribution, from the branch data
(thesis Lemma 2.33; the `⊥`-choice carries the pass-through mass
`w − Σ_v |B i v|`). -/
noncomputable def PDS.choiceOf (vs : Finset Y) (B : Y → PDS X Y)
    (w : ℝ) : Distribution (Option (Y × System.DDS X Y)) :=
  PDS.classChoiceDist vs B (w - ∑ v ∈ vs, (B v).weight)

/-- The per-class overlap: the weight of the common part of the two
sides' choice distributions. -/
noncomputable def PDS.overlapOf {I : Type*} (vs : I → Finset Y)
    (Bs Bt : I → Y → PDS X Y) (wS wT : ℝ) (i : I) : ℝ :=
  Distribution.weight (((PDS.choiceOf (vs i) (Bs i) wS) ⊓ (PDS.choiceOf (vs i) (Bt i) wT)))

/-- The shared trimmed common part: the per-class common part scaled
down to the uniform weight `τ` (thesis Lemma 2.33's trim). -/
noncomputable def PDS.trimOf {I : Type*} (vs : I → Finset Y)
    (Bs Bt : I → Y → PDS X Y) (wS wT : ℝ) (τ : ℝ) (i : I) :
    Distribution (Option (Y × System.DDS X Y)) :=
  (τ / PDS.overlapOf vs Bs Bt wS wT i) •
    ((PDS.choiceOf (vs i) (Bs i) wS) ⊓ (PDS.choiceOf (vs i) (Bt i) wT))

theorem PDS.classChoiceDist_nonNeg {vs : Finset Y}
    {B : Y → PDS X Y} {β : ℝ}
    (hB : ∀ v ∈ vs, (B v).NonNeg) (hβ : 0 ≤ β) :
    (PDS.classChoiceDist vs B β).NonNeg := fun c => by
  unfold PDS.classChoiceDist
  rw [Finsupp.add_apply, Finsupp.finset_sum_apply]
  exact add_nonneg
    (Finset.sum_nonneg fun v hv => ((hB v hv).fTransform _) c)
    (Distribution.single_nonNeg hβ _ c)

theorem PDS.choiceOf_nonNeg {vs : Finset Y} {B : Y → PDS X Y}
    {w : ℝ} (hB : ∀ v ∈ vs, (B v).NonNeg)
    (hw : ∑ v ∈ vs, (B v).weight ≤ w) : (PDS.choiceOf vs B w).NonNeg :=
  PDS.classChoiceDist_nonNeg hB (sub_nonneg.mpr hw)

theorem PDS.overlapOf_nonneg {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {i : I}
    (hBs : ∀ v ∈ vs i, (Bs i v).NonNeg) (hBt : ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∑ v ∈ vs i, (Bt i v).weight ≤ wT) :
    0 ≤ PDS.overlapOf vs Bs Bt wS wT i :=
  (Distribution.nonNeg_inf (PDS.choiceOf_nonNeg hBs hwS)
    (PDS.choiceOf_nonNeg hBt hwT)).weight_nonneg

theorem PDS.trimOf_nonNeg {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    {i : I}
    (hBs : ∀ v ∈ vs i, (Bs i v).NonNeg) (hBt : ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∑ v ∈ vs i, (Bt i v).weight ≤ wT) :
    (PDS.trimOf vs Bs Bt wS wT τ i).NonNeg := fun c => by
  unfold PDS.trimOf
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact mul_nonneg
    (div_nonneg hτ (PDS.overlapOf_nonneg hBs hBt hwS hwT))
    (Distribution.nonNeg_inf (PDS.choiceOf_nonNeg hBs hwS) (PDS.choiceOf_nonNeg hBt hwT) c)

open Classical in
/-- Thesis Lemma 2.33, the joint of one side: the shared trimmed part
`E` plus the side's own (( - )⁺)`D − E`, glued into profile atoms.  Both
sides instantiate `E` with the **same** trim term, which is what makes
their joints share the coupled mass. -/
noncomputable def PDS.crossJointOf {I : Type*} (cls : X → I)
    (C : Finset I) (D E : I → Distribution (Option (Y × System.DDS X Y)))
    (w τ : ℝ) : PDS X Y :=
  Distribution.fTransform (System.glueProfile cls)
    (Distribution.jointProfile τ none C E
      + Distribution.jointProfile (w - τ) none C fun i => D i - E i)

theorem PDS.weight_choiceOf {vs : Finset Y} {B : Y → PDS X Y}
    {w : ℝ} (_hw : ∑ v ∈ vs, (B v).weight ≤ w) :
    (PDS.choiceOf vs B w).weight = w := by
  unfold PDS.choiceOf
  rw [PDS.weight_classChoiceDist]
  ring

theorem PDS.div_overlapOf_le_one {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ} {i : I}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ PDS.overlapOf vs Bs Bt wS wT i) :
    τ / PDS.overlapOf vs Bs Bt wS wT i ≤ 1 :=
  div_le_one_of_le₀ hτ (le_trans hτ0 hτ)

theorem PDS.trimOf_le_left {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ} {i : I}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ PDS.overlapOf vs Bs Bt wS wT i)
    (hSnn : (PDS.choiceOf (vs i) (Bs i) wS).NonNeg)
    (hTnn : (PDS.choiceOf (vs i) (Bt i) wT).NonNeg) :
    PDS.trimOf vs Bs Bt wS wT τ i ≤ PDS.choiceOf (vs i) (Bs i) wS := by
  refine Finsupp.le_def.mpr fun c => ?_
  unfold PDS.trimOf
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact le_trans
    (mul_le_of_le_one_left (Distribution.nonNeg_inf hSnn hTnn c)
      (PDS.div_overlapOf_le_one hτ0 hτ))
    (Distribution.inf_le_left_apply (PDS.choiceOf (vs i) (Bs i) wS)
      (PDS.choiceOf (vs i) (Bt i) wT) c)

theorem PDS.trimOf_le_right {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ} {i : I}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ PDS.overlapOf vs Bs Bt wS wT i)
    (hSnn : (PDS.choiceOf (vs i) (Bs i) wS).NonNeg)
    (hTnn : (PDS.choiceOf (vs i) (Bt i) wT).NonNeg) :
    PDS.trimOf vs Bs Bt wS wT τ i ≤ PDS.choiceOf (vs i) (Bt i) wT := by
  refine Finsupp.le_def.mpr fun c => ?_
  unfold PDS.trimOf
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact le_trans
    (mul_le_of_le_one_left (Distribution.nonNeg_inf hSnn hTnn c)
      (PDS.div_overlapOf_le_one hτ0 hτ))
    (Distribution.inf_le_right_apply (PDS.choiceOf (vs i) (Bs i) wS)
      (PDS.choiceOf (vs i) (Bt i) wT) c)

theorem PDS.weight_trimOf {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ} {i : I}
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ PDS.overlapOf vs Bs Bt wS wT i) :
    Distribution.weight (PDS.trimOf vs Bs Bt wS wT τ i) = τ := by
  unfold PDS.trimOf
  rw [Distribution.weight_smul]
  show τ / PDS.overlapOf vs Bs Bt wS wT i * PDS.overlapOf vs Bs Bt wS wT i = τ
  rcases eq_or_ne (PDS.overlapOf vs Bs Bt wS wT i) 0 with h0 | h0
  · rw [h0, mul_zero]
    exact (le_antisymm (hτ.trans h0.le) hτ0).symm
  · exact div_mul_cancel₀ τ h0


theorem PDS.overlapOf_le_left {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {i : I}
    (hwS : ∑ v ∈ vs i, (Bs i v).weight ≤ wS) :
    PDS.overlapOf vs Bs Bt wS wT i ≤ wS := by
  refine le_trans (Distribution.weight_le_weight_of_le
    (Finsupp.le_def.mpr (Distribution.inf_le_left_apply _ _))) ?_
  rw [PDS.weight_choiceOf hwS]

theorem PDS.overlapOf_le_right {I : Type*} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {i : I}
    (hwT : ∑ v ∈ vs i, (Bt i v).weight ≤ wT) :
    PDS.overlapOf vs Bs Bt wS wT i ≤ wT := by
  refine le_trans (Distribution.weight_le_weight_of_le
    (Finsupp.le_def.mpr (Distribution.inf_le_right_apply _ _))) ?_
  rw [PDS.weight_choiceOf hwT]

open Classical in
/-- Thesis Lemma 2.33, marginal preservation (`S`-side, answered
case): the `(x, some v)`-marginal of the `S`-joint recovers the
prescribed branch representative — cleanly, both for `v` in the class
(`= Bs (cls x) v`) and outside (`= 0`, next lemma). -/
theorem PDS.successorTransform_crossJointOf_left {I : Type*}
    {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ PDS.overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) {v : Y} (hv : v ∈ vs (cls x)) :
    PDS.successorTransform (PDS.crossJointOf cls C
        (fun i => PDS.choiceOf (vs i) (Bs i) wS)
        (PDS.trimOf vs Bs Bt wS wT τ) wS τ) x (some v)
      = Bs (cls x) v := by
  unfold PDS.crossJointOf
  rw [PDS.successorTransform_crossJointAtom cls C _ _ τ wS
    (fun i hi => PDS.trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
    (fun i hi => PDS.weight_trimOf hτ0 (hτ i hi))
    (fun i hi => PDS.weight_choiceOf (hwS i hi))
    (fun i hi => PDS.trimOf_le_left hτ0 (hτ i hi)
      (PDS.choiceOf_nonNeg (hBs i hi) (hwS i hi))
      (PDS.choiceOf_nonNeg (hBt i hi) (hwT i hi))) hx v]
  exact PDS.contOf_filter_classChoiceDist_of_mem hv

open Classical in
theorem PDS.successorTransform_crossJointOf_left_of_not_mem
    {I : Type*} {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ PDS.overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) {v : Y} (hv : v ∉ vs (cls x)) :
    PDS.successorTransform (PDS.crossJointOf cls C
        (fun i => PDS.choiceOf (vs i) (Bs i) wS)
        (PDS.trimOf vs Bs Bt wS wT τ) wS τ) x (some v)
      = 0 := by
  unfold PDS.crossJointOf
  rw [PDS.successorTransform_crossJointAtom cls C _ _ τ wS
    (fun i hi => PDS.trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
    (fun i hi => PDS.weight_trimOf hτ0 (hτ i hi))
    (fun i hi => PDS.weight_choiceOf (hwS i hi))
    (fun i hi => PDS.trimOf_le_left hτ0 (hτ i hi)
      (PDS.choiceOf_nonNeg (hBs i hi) (hwS i hi))
      (PDS.choiceOf_nonNeg (hBt i hi) (hwT i hi))) hx v]
  exact PDS.contOf_filter_classChoiceDist_of_not_mem hv

open Classical in
/-- Thesis Lemma 2.33, marginal preservation (`T`-side, answered
case) — with the **same** shared trim term as the `S`-side. -/
theorem PDS.successorTransform_crossJointOf_right {I : Type*}
    {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ PDS.overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) {v : Y} (hv : v ∈ vs (cls x)) :
    PDS.successorTransform (PDS.crossJointOf cls C
        (fun i => PDS.choiceOf (vs i) (Bt i) wT)
        (PDS.trimOf vs Bs Bt wS wT τ) wT τ) x (some v)
      = Bt (cls x) v := by
  unfold PDS.crossJointOf
  rw [PDS.successorTransform_crossJointAtom cls C _ _ τ wT
    (fun i hi => PDS.trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
    (fun i hi => PDS.weight_trimOf hτ0 (hτ i hi))
    (fun i hi => PDS.weight_choiceOf (hwT i hi))
    (fun i hi => PDS.trimOf_le_right hτ0 (hτ i hi)
      (PDS.choiceOf_nonNeg (hBs i hi) (hwS i hi))
      (PDS.choiceOf_nonNeg (hBt i hi) (hwT i hi))) hx v]
  exact PDS.contOf_filter_classChoiceDist_of_mem hv

open Classical in
theorem PDS.successorTransform_crossJointOf_right_of_not_mem
    {I : Type*} {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ PDS.overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) {v : Y} (hv : v ∉ vs (cls x)) :
    PDS.successorTransform (PDS.crossJointOf cls C
        (fun i => PDS.choiceOf (vs i) (Bt i) wT)
        (PDS.trimOf vs Bs Bt wS wT τ) wT τ) x (some v)
      = 0 := by
  unfold PDS.crossJointOf
  rw [PDS.successorTransform_crossJointAtom cls C _ _ τ wT
    (fun i hi => PDS.trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
    (fun i hi => PDS.weight_trimOf hτ0 (hτ i hi))
    (fun i hi => PDS.weight_choiceOf (hwT i hi))
    (fun i hi => PDS.trimOf_le_right hτ0 (hτ i hi)
      (PDS.choiceOf_nonNeg (hBs i hi) (hwS i hi))
      (PDS.choiceOf_nonNeg (hBt i hi) (hwT i hi))) hx v]
  exact PDS.contOf_filter_classChoiceDist_of_not_mem hv

open Classical in
/-- The joint carries the side's full weight. -/
theorem PDS.weight_crossJointOf {I : Type*} {cls : X → I}
    {C : Finset I} (D E : I → Distribution (Option (Y × System.DDS X Y)))
    {w τ : ℝ} (hE : ∀ i ∈ C, (E i).weight = τ)
    (hD : ∀ i ∈ C, (D i).weight = w) (_hle : ∀ i ∈ C, E i ≤ D i)
    (_hτw : τ ≤ w) :
    Distribution.weight (PDS.crossJointOf cls C D E w τ) = w := by
  unfold PDS.crossJointOf
  rw [Distribution.weight_fTransform, Distribution.weight_add,
    Distribution.jointProfile_weight τ none C E hE,
    Distribution.jointProfile_weight (w - τ) none C _ fun j hj => by
      rw [Distribution.weight_sub _ _, hD j hj, hE j hj]]
  ring

open Classical in
/-- A cross-query joint is honest whenever its shared part and both residual
parts are honest.  This was implicit when `Distribution` used nonnegative
coefficients; it is an explicit invariant on the signed carrier. -/
theorem PDS.crossJointOf_nonNeg {I : Type*} {cls : X → I}
    {C : Finset I} (D E : I → Distribution (Option (Y × System.DDS X Y)))
    {w τ : ℝ} (_hD : ∀ i ∈ C, (D i).NonNeg)
    (hE : ∀ i ∈ C, (E i).NonNeg) (hle : ∀ i ∈ C, E i ≤ D i)
    (hτ0 : 0 ≤ τ) (hτw : τ ≤ w) :
    (PDS.crossJointOf cls C D E w τ).NonNeg := by
  unfold PDS.crossJointOf
  refine Distribution.NonNeg.fTransform ?_ _
  intro p
  rw [Finsupp.add_apply]
  exact add_nonneg
    (Distribution.jointProfile_nonNeg hτ0 none C hE p)
    (Distribution.jointProfile_nonNeg (sub_nonneg.mpr hτw) none C
      (fun i hi => Distribution.nonNeg_sub_of_le (hle i hi)) p)


open Classical in
/-- The retraction of `System.glueProfile`: read a profile back off a system by
probing one representative query of each realized class — the first answer
there, together with the successor system after it. -/
noncomputable def System.profileOf {I : Type*} (cls : X → I)
    (t : System.DDS X Y) (i : I) : Option (Y × System.DDS X Y) :=
  if h : ∃ x, cls x = i then
    Option.map (fun v => (v, System.DDS.successor t (Classical.choose h)))
      (System.output (System.fullyDefined t) [Classical.choose h]
        (by rw [System.dom_fullyDefined]; simp))
  else none

open Classical in
theorem System.profileOf_glueProfile {I : Type*} (cls : X → I)
    (p : I → Option (Y × System.DDS X Y))
    (hout : ∀ i, ¬(∃ x, cls x = i) → p i = none) :
    System.profileOf cls (System.glueProfile cls p) = p := by
  funext i
  unfold System.profileOf
  split
  · rename_i h
    have hx₀ : cls (Classical.choose h) = i := Classical.choose_spec h
    rw [System.output_fullyDefined_glueProfile cls p (Classical.choose h), hx₀]
    rcases hc : p i with _ | ⟨v, a⟩
    · rfl
    · simp only [Option.map_some]
      rw [System.successor_glueProfile_some (show p (cls (Classical.choose h))
          = some (v, a) by rw [hx₀]; exact hc)]
  · rename_i h
    exact (hout i h).symm

open Classical in
theorem PDS.fTransform_profileOf_glueProfile {I : Type*}
    (cls : X → I) (ρ : Distribution (I → Option (Y × System.DDS X Y)))
    (hsupp : ∀ p ∈ ρ.support, ∀ i, ¬(∃ x, cls x = i) → p i = none) :
    Distribution.fTransform (System.profileOf cls)
        (Distribution.fTransform (System.glueProfile cls) ρ) = ρ := by
  rw [Distribution.fTransform_comp]
  refine Eq.trans (Distribution.fTransform_congr (g := id) ρ
    fun p hp => System.profileOf_glueProfile cls p (hsupp p hp))
    (Distribution.fTransform_id ρ)

open Classical in
/-- The joints' profile distributions put no choice outside `C`. -/

theorem PDS.statDist_crossJointOf {I : Type*} {cls : X → I} {C : Finset I}
    {vs : I → Finset Y} {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ}
    (hC : C.Nonempty) (hreal : ∀ i ∈ C, ∃ x, cls x = i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT) :
    (statDist (PDS.crossJointOf cls C (fun i => PDS.choiceOf (vs i) (Bs i) wS)
          (PDS.trimOf vs Bs Bt wS wT (C.inf' hC (PDS.overlapOf vs Bs Bt wS wT)))
          wS (C.inf' hC (PDS.overlapOf vs Bs Bt wS wT)))
        (PDS.crossJointOf cls C (fun i => PDS.choiceOf (vs i) (Bt i) wT)
          (PDS.trimOf vs Bs Bt wS wT (C.inf' hC (PDS.overlapOf vs Bs Bt wS wT)))
          wT (C.inf' hC (PDS.overlapOf vs Bs Bt wS wT))) : ℝ)
      = (wS : ℝ) - (C.inf' hC (PDS.overlapOf vs Bs Bt wS wT) : ℝ) := by
  set τ := C.inf' hC (PDS.overlapOf vs Bs Bt wS wT) with hτdef
  set E := PDS.trimOf vs Bs Bt wS wT τ with hEdef
  set DS := fun i => PDS.choiceOf (vs i) (Bs i) wS with hDSdef
  set DT := fun i => PDS.choiceOf (vs i) (Bt i) wT with hDTdef
  have hτle : ∀ i ∈ C, τ ≤ PDS.overlapOf vs Bs Bt wS wT i :=
    fun i hi => Finset.inf'_le _ hi
  have hDSnn : ∀ i ∈ C, (DS i).NonNeg :=
    fun i hi => PDS.choiceOf_nonNeg (hBs i hi) (hwS i hi)
  have hDTnn : ∀ i ∈ C, (DT i).NonNeg :=
    fun i hi => PDS.choiceOf_nonNeg (hBt i hi) (hwT i hi)
  have hτ0 : 0 ≤ τ := by
    rw [hτdef]
    exact Finset.le_inf' hC _ fun j hj =>
      PDS.overlapOf_nonneg (hBs j hj) (hBt j hj) (hwS j hj) (hwT j hj)
  have hτwS : τ ≤ wS := by
    obtain ⟨i, hi⟩ := hC
    exact (hτle i hi).trans (PDS.overlapOf_le_left (hwS i hi))
  have hEnn : ∀ i ∈ C, (E i).NonNeg := fun i hi =>
    PDS.trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi)
  have hEw : ∀ i ∈ C, Distribution.weight (E i) = τ :=
    fun i hi => PDS.weight_trimOf hτ0 (hτle i hi)
  have hDSw : ∀ i ∈ C, Distribution.weight (DS i) = wS :=
    fun i hi => PDS.weight_choiceOf (hwS i hi)
  have hDTw : ∀ i ∈ C, Distribution.weight (DT i) = wT :=
    fun i hi => PDS.weight_choiceOf (hwT i hi)
  have hleS : ∀ i ∈ C, E i ≤ DS i := fun i hi =>
    PDS.trimOf_le_left hτ0 (hτle i hi) (hDSnn i hi) (hDTnn i hi)
  have hleT : ∀ i ∈ C, E i ≤ DT i := fun i hi =>
    PDS.trimOf_le_right hτ0 (hτle i hi) (hDSnn i hi) (hDTnn i hi)
  have hXw : ∀ i ∈ C, Distribution.weight (DS i - E i) = wS - τ := fun i hi => by
    rw [Distribution.weight_sub _ _, hDSw i hi, hEw i hi]
  have hYw : ∀ i ∈ C, Distribution.weight (DT i - E i) = wT - τ := fun i hi => by
    rw [Distribution.weight_sub _ _, hDTw i hi, hEw i hi]
  have hwTτ : 0 ≤ (wT : ℝ) - τ := by
    obtain ⟨i, hi⟩ := hC
    have := Distribution.weight_le_weight_of_le (hleT i hi)
    rw [hEw i hi, hDTw i hi] at this
    linarith
  have hTside : (Distribution.jointProfile τ none C E
      + Distribution.jointProfile (wT - τ) none C fun i => DT i - E i).NonNeg := fun p => by
    rw [Finsupp.add_apply]
    exact add_nonneg
      (Distribution.jointProfile_nonNeg hτ0 none C hEnn p)
      (Distribution.jointProfile_nonNeg hwTτ none C
        (fun j hj => Distribution.nonNeg_sub_of_le (hleT j hj)) p)
  have hTside' : (Distribution.jointProfile (wT - τ) none C fun i => DT i - E i).NonNeg :=
    Distribution.jointProfile_nonNeg hwTτ none C fun j hj => Distribution.nonNeg_sub_of_le (hleT j hj)
  have hJρ : statDist (PDS.crossJointOf cls C DS E wS τ) (PDS.crossJointOf cls C DT E wT τ)
      = statDist (Distribution.jointProfile τ none C E
            + Distribution.jointProfile (wS - τ) none C fun i => DS i - E i)
          (Distribution.jointProfile τ none C E
            + Distribution.jointProfile (wT - τ) none C fun i => DT i - E i) := by
    refine le_antisymm (Probability.statDist_fTransform_le _ _ (System.glueProfile cls)) ?_
    have hS := PDS.fTransform_profileOf_glueProfile cls
      (Distribution.jointProfile τ none C E
        + Distribution.jointProfile (wS - τ) none C fun i => DS i - E i)
      fun p hp i hnx => Distribution.add_jointProfile_support_default τ (wS - τ) none C _ _
        p hp i fun hiC => hnx (hreal i hiC)
    have hT := PDS.fTransform_profileOf_glueProfile cls
      (Distribution.jointProfile τ none C E
        + Distribution.jointProfile (wT - τ) none C fun i => DT i - E i)
      fun p hp i hnx => Distribution.add_jointProfile_support_default τ (wT - τ) none C _ _
        p hp i fun hiC => hnx (hreal i hiC)
    rw [← hS, ← hT]
    exact Probability.statDist_fTransform_le _ _ (System.profileOf cls)
  have hρstatDist : statDist (Distribution.jointProfile τ none C E
        + Distribution.jointProfile (wS - τ) none C fun i => DS i - E i)
      (Distribution.jointProfile τ none C E
        + Distribution.jointProfile (wT - τ) none C fun i => DT i - E i)
      = statDist (Distribution.jointProfile (wS - τ) none C fun i => DS i - E i)
          (Distribution.jointProfile (wT - τ) none C fun i => DT i - E i) :=
    Distribution.statDist_add_add_left _ _ _
  obtain ⟨i₀, hi₀, hτeq⟩ :=
    Finset.exists_mem_eq_inf' hC (PDS.overlapOf vs Bs Bt wS wT)
  rw [← hτdef] at hτeq
  have hlow : statDist (DS i₀) (DT i₀)
      ≤ statDist (Distribution.jointProfile (wS - τ) none C fun i => DS i - E i)
          (Distribution.jointProfile (wT - τ) none C fun i => DT i - E i) := by
    have hkey := Probability.statDist_fTransform_le
      (Distribution.jointProfile (wS - τ) none C fun i => DS i - E i)
      (Distribution.jointProfile (wT - τ) none C fun i => DT i - E i)
      (fun p => p i₀)
    rw [Distribution.jointProfile_marginal (wS - τ) none C _
        (fun j hj => Distribution.nonNeg_sub_of_le (hleS j hj)) hXw hi₀,
      Distribution.jointProfile_marginal (wT - τ) none C _
        (fun j hj => Distribution.nonNeg_sub_of_le (hleT j hj)) hYw hi₀,
      Distribution.statDist_sub_sub] at hkey
    exact hkey
  have hval : (statDist (DS i₀) (DT i₀) : ℝ)
      = (wS : ℝ) - (PDS.overlapOf vs Bs Bt wS wT i₀ : ℝ) := by
    have hstatDistw := Distribution.statDist_eq_weight_sub_weight_inf (DS i₀) (DT i₀)
    rw [hDSw i₀ hi₀] at hstatDistw
    exact hstatDistw
  have hwSτ : 0 ≤ (wS : ℝ) - τ := by linarith
  have hSside' : (Distribution.jointProfile (wS - τ) none C fun i => DS i - E i).NonNeg :=
    Distribution.jointProfile_nonNeg hwSτ none C fun j hj => Distribution.nonNeg_sub_of_le (hleS j hj)
  rw [hJρ, hρstatDist]
  refine le_antisymm ?_ ?_
  · exact (Probability.statDist_le_weight hSside' hTside').trans
      (le_of_eq (Distribution.jointProfile_weight (wS - τ) none C _ hXw))
  · calc (wS : ℝ) - (τ : ℝ)
        = (wS : ℝ) - (PDS.overlapOf vs Bs Bt wS wT i₀ : ℝ) := by rw [hτeq]
      _ = (statDist (DS i₀) (DT i₀) : ℝ) := hval.symm
      _ ≤ _ := by exact_mod_cast hlow

open Classical in
theorem PDS.filter_ans_fTransform_glueProfile {I : Type*}
    (cls : X → I) (ρ : Distribution (I → Option (Y × System.DDS X Y)))
    (x : X) (y₀ : Option Y) :
    (Distribution.fTransform (System.glueProfile cls) ρ).filter
      (fun t => System.output (System.fullyDefined t) [x]
        (by rw [System.dom_fullyDefined]; simp) = y₀)
      = Distribution.fTransform (System.glueProfile cls)
          (ρ.filter fun p => Option.map Prod.fst (p (cls x)) = y₀) := by
  rw [Distribution.filter_fTransform]
  refine congrArg (Distribution.fTransform (System.glueProfile cls)) ?_
  refine Finsupp.ext fun p => ?_
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases hp : Option.map Prod.fst (p (cls x)) = y₀
  · rw [if_pos hp,
      if_pos ((System.output_fullyDefined_glueProfile cls p x).trans hp)]
  · rw [if_neg hp, if_neg fun h => hp
      ((System.output_fullyDefined_glueProfile cls p x).symm.trans h)]

open Classical in
theorem PDS.weight_filter_marginal {I : Type*} (cls : X → I)
    (ρ : Distribution (I → Option (Y × System.DDS X Y))) (x : X)
    (y₀ : Option Y) :
    Distribution.weight (ρ.filter fun p => Option.map Prod.fst (p (cls x)) = y₀)
      = Distribution.weight ((Distribution.fTransform (fun p => p (cls x)) ρ).filter
          fun c => Option.map Prod.fst c = y₀) := by
  rw [Distribution.filter_fTransform, Distribution.weight_fTransform]

open Classical in
/-- Thesis Lemma 2.33, the `⊥`-bookkeeping (`S`-side): the joint's
`⊥`-marginal weight at any query of a participating class is exactly
the class's pass-through mass — no `⊥`-branch representative exists or
is needed (`successorTransform_none_eq_filter`); milestone 4 recurses
on the joint's own `⊥`-filter. -/
theorem PDS.weight_successorTransform_none_crossJointOf {I : Type*}
    {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ PDS.overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) :
    Distribution.weight (PDS.successorTransform (PDS.crossJointOf cls C
        (fun i => PDS.choiceOf (vs i) (Bs i) wS)
        (PDS.trimOf vs Bs Bt wS wT τ) wS τ) x none)
      = wS - ∑ v ∈ vs (cls x), (Bs (cls x) v).weight := by
  have htleS : ∀ j ∈ C, PDS.trimOf vs Bs Bt wS wT τ j ≤ PDS.choiceOf (vs j) (Bs j) wS :=
    fun j hj => PDS.trimOf_le_left hτ0 (hτ j hj)
      (PDS.choiceOf_nonNeg (hBs j hj) (hwS j hj))
      (PDS.choiceOf_nonNeg (hBt j hj) (hwT j hj))
  have hX' : ∀ j ∈ C, Distribution.weight
      (PDS.choiceOf (vs j) (Bs j) wS - PDS.trimOf vs Bs Bt wS wT τ j)
      = wS - τ := by
    intro j hj
    rw [Distribution.weight_sub _ _,
      PDS.weight_choiceOf (hwS j hj), PDS.weight_trimOf hτ0 (hτ j hj)]
  unfold PDS.successorTransform PDS.crossJointOf
  rw [Distribution.weight_fTransform, PDS.filter_ans_fTransform_glueProfile,
    Distribution.weight_fTransform, PDS.weight_filter_marginal, Distribution.fTransform_add,
    Distribution.jointProfile_marginal τ none C _
      (fun i hi => PDS.trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
      (fun i hi => PDS.weight_trimOf hτ0 (hτ i hi)) hx,
    Distribution.jointProfile_marginal (wS - τ) none C _
      (fun j hj => Distribution.nonNeg_sub_of_le (htleS j hj)) hX' hx,
    Distribution.add_sub_cancel']
  have hfin : Finsupp.filter (fun c => Option.map Prod.fst c = none)
      ((fun i => PDS.choiceOf (vs i) (Bs i) wS) (cls x))
      = Finsupp.single none
          (wS - ∑ v ∈ vs (cls x), (Bs (cls x) v).weight) :=
    PDS.filter_none_classChoiceDist (vs (cls x)) (Bs (cls x)) _
  rw [hfin, Distribution.weight_single]

open Classical in
theorem PDS.weight_successorTransform_none_crossJointOf_right
    {I : Type*} {cls : X → I} {C : Finset I} {vs : I → Finset Y}
    {Bs Bt : I → Y → PDS X Y} {wS wT : ℝ} {τ : ℝ}
    (hτ0 : 0 ≤ τ)
    (hτ : ∀ i ∈ C, τ ≤ PDS.overlapOf vs Bs Bt wS wT i)
    (hBs : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBt : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight ≤ wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight ≤ wT)
    {x : X} (hx : cls x ∈ C) :
    Distribution.weight (PDS.successorTransform (PDS.crossJointOf cls C
        (fun i => PDS.choiceOf (vs i) (Bt i) wT)
        (PDS.trimOf vs Bs Bt wS wT τ) wT τ) x none)
      = wT - ∑ v ∈ vs (cls x), (Bt (cls x) v).weight := by
  have htleT : ∀ j ∈ C, PDS.trimOf vs Bs Bt wS wT τ j ≤ PDS.choiceOf (vs j) (Bt j) wT :=
    fun j hj => PDS.trimOf_le_right hτ0 (hτ j hj)
      (PDS.choiceOf_nonNeg (hBs j hj) (hwS j hj))
      (PDS.choiceOf_nonNeg (hBt j hj) (hwT j hj))
  have hY' : ∀ j ∈ C, Distribution.weight
      (PDS.choiceOf (vs j) (Bt j) wT - PDS.trimOf vs Bs Bt wS wT τ j)
      = wT - τ := by
    intro j hj
    rw [Distribution.weight_sub _ _,
      PDS.weight_choiceOf (hwT j hj), PDS.weight_trimOf hτ0 (hτ j hj)]
  unfold PDS.successorTransform PDS.crossJointOf
  rw [Distribution.weight_fTransform, PDS.filter_ans_fTransform_glueProfile,
    Distribution.weight_fTransform, PDS.weight_filter_marginal, Distribution.fTransform_add,
    Distribution.jointProfile_marginal τ none C _
      (fun i hi => PDS.trimOf_nonNeg hτ0 (hBs i hi) (hBt i hi) (hwS i hi) (hwT i hi))
      (fun i hi => PDS.weight_trimOf hτ0 (hτ i hi)) hx,
    Distribution.jointProfile_marginal (wT - τ) none C _
      (fun j hj => Distribution.nonNeg_sub_of_le (htleT j hj)) hY' hx,
    Distribution.add_sub_cancel']
  have hfin : Finsupp.filter (fun c => Option.map Prod.fst c = none)
      ((fun i => PDS.choiceOf (vs i) (Bt i) wT) (cls x))
      = Finsupp.single none
          (wT - ∑ v ∈ vs (cls x), (Bt (cls x) v).weight) :=
    PDS.filter_none_classChoiceDist (vs (cls x)) (Bt (cls x)) _
  rw [hfin, Distribution.weight_single]

open Classical in
theorem PDS.pairwiseDisjoint_support_taggedBranches
    (Bs Bt : Y → PDS X Y) (vs : Finset Y) :
    (↑vs : Set Y).PairwiseDisjoint fun v =>
      (Distribution.fTransform (fun s => some (v, s)) (Bs v)).support ∪
        (Distribution.fTransform (fun s => some (v, s)) (Bt v)).support := by
  intro v _ v' _ hvv'
  refine Finset.disjoint_left.mpr fun c hc hc' => ?_
  have hshape : ∀ {z : Y},
      c ∈ (Distribution.fTransform (fun s => some (z, s)) (Bs z)).support ∪
          (Distribution.fTransform (fun s => some (z, s)) (Bt z)).support →
      ∃ s, c = some (z, s) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support hz)
      exact ⟨s, rfl⟩
    · obtain ⟨s, _, rfl⟩ :=
        Finset.mem_image.mp (Finsupp.mapDomain_support hz)
      exact ⟨s, rfl⟩
  obtain ⟨s, hs⟩ := hshape hc
  obtain ⟨t, ht⟩ := hshape hc'
  exact hvv' (congrArg Prod.fst (Option.some.inj (hs.symm.trans ht)))

open Classical in
theorem PDS.statDist_choiceOf_eq_sum_of_branch_statDists
    {vs : Finset Y} {Bs Bt : Y → PDS X Y} {wS wT : ℝ}
    (_hBt : ∀ v ∈ vs, (Bt v).NonNeg)
    (hwS : ∑ v ∈ vs, (Bs v).weight = wS)
    (hwT : ∑ v ∈ vs, (Bt v).weight = wT) :
    statDist (PDS.choiceOf vs Bs wS) (PDS.choiceOf vs Bt wT) =
      ∑ v ∈ vs, statDist (Bs v) (Bt v) := by
  classical
  unfold PDS.choiceOf PDS.classChoiceDist
  rw [← hwS, ← hwT]
  simp only [sub_self, Finsupp.single_zero, add_zero]
  rw [show (∑ v ∈ vs, Distribution.fTransform (fun s => some (v, s)) (Bs v))
        = ∑ v ∈ vs, Distribution.fTransform
            (fun s : System.DDS X Y => (some (v, s) : Option (Y × System.DDS X Y)))
            ((fun v => Bs v) v) from rfl,
    Probability.statDist_sum_of_disjoint_support _ _
      (PDS.pairwiseDisjoint_support_taggedBranches Bs Bt vs)]
  exact Finset.sum_congr rfl fun v _ =>
    Probability.statDist_fTransform_injective (Bs v) (Bt v)
      (fun s : System.DDS X Y => some (v, s))
      (fun _ _ h => congrArg Prod.snd (Option.some.inj h))

open Classical in
theorem PDS.support_crossJointOf_rejects_of_class_not_mem
    {I : Type*} {cls : X → I} {C : Finset I}
    (D E : I → Distribution (Option (Y × System.DDS X Y)))
    (w τ : ℝ) {x : X} (hx : cls x ∉ C) :
    ∀ s ∈ (PDS.crossJointOf cls C D E w τ).support,
      [x] ∉ System.dom s := by
  intro s hs
  unfold PDS.crossJointOf at hs
  obtain ⟨p, hp, rfl⟩ := Distribution.mem_support_fTransform _ _ hs
  apply System.output_fullyDefined_eq_none_iff.mp
  rw [System.output_fullyDefined_glueProfile]
  have hpnone := Distribution.add_jointProfile_support_default τ (w - τ) none C E
    (fun i => D i - E i) p hp (cls x) hx
  simp [hpnone]

/-- The source-shaped output of thesis Lemma 2.33 / LanMau20 Lemma 6.

The participating classes are finite, every left branch family reassembles to
the common left weight `wS`, and every right branch family reassembles to the
possibly different common right weight `wT`.  The joint systems expose the
prescribed successor marginals, reject queries outside the participating
classes, and attain the largest per-class sum of branch distances. -/
structure PDS.FiniteClassJointWitness {I : Type*} (cls : X → I) (C : Finset I)
    (vs : I → Finset Y) (Bs Bt : I → Y → PDS X Y)
    (wS wT : ℝ) where
  left : PDS X Y
  right : PDS X Y
  left_nonNeg : left.NonNeg
  right_nonNeg : right.NonNeg
  chosen : I
  chosen_mem : chosen ∈ C
  left_weight : left.weight = wS
  right_weight : right.weight = wT
  left_successor_of_mem : ∀ {x v}, cls x ∈ C → v ∈ vs (cls x) →
    PDS.successorTransform left x (some v) = Bs (cls x) v
  right_successor_of_mem : ∀ {x v}, cls x ∈ C → v ∈ vs (cls x) →
    PDS.successorTransform right x (some v) = Bt (cls x) v
  left_successor_of_not_mem : ∀ {x v}, cls x ∈ C → v ∉ vs (cls x) →
    PDS.successorTransform left x (some v) = 0
  right_successor_of_not_mem : ∀ {x v}, cls x ∈ C → v ∉ vs (cls x) →
    PDS.successorTransform right x (some v) = 0
  left_successor_none : ∀ {x}, cls x ∈ C →
    PDS.successorTransform left x none = 0
  right_successor_none : ∀ {x}, cls x ∈ C →
    PDS.successorTransform right x none = 0
  left_rejects_of_class_not_mem : ∀ {x}, cls x ∉ C →
    ∀ s ∈ left.support, [x] ∉ System.dom s
  right_rejects_of_class_not_mem : ∀ {x}, cls x ∉ C →
    ∀ t ∈ right.support, [x] ∉ System.dom t
  delta_eq_selected_sum :
    (statDist left right : ℝ) =
      ∑ v ∈ vs chosen, (statDist (Bs chosen v) (Bt chosen v) : ℝ)
  branch_sum_le_delta : ∀ i ∈ C,
    (∑ v ∈ vs i, (statDist (Bs i v) (Bt i v) : ℝ)) ≤
      (statDist left right : ℝ)

open Classical in
/-- Thesis Lemma 2.33 / LanMau20 Lemma 6 specialized to finite
first-query classes.  The two sides may have different common weights; only
the weights within each side are required to agree. -/
theorem PDS.exists_finiteClassJointWitness_of_common_side_weights
    {I : Type*} (cls : X → I) (C : Finset I) (hC : C.Nonempty)
    (hreal : ∀ i ∈ C, ∃ x, cls x = i) (vs : I → Finset Y)
    (Bs Bt : I → Y → PDS X Y) (wS wT : ℝ)
    (hBsnn : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg)
    (hBtnn : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg)
    (hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight = wS)
    (hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight = wT) :
    Nonempty (PDS.FiniteClassJointWitness cls C vs Bs Bt wS wT) := by
  let τ := C.inf' hC (PDS.overlapOf vs Bs Bt wS wT)
  let E := PDS.trimOf vs Bs Bt wS wT τ
  let S' := PDS.crossJointOf cls C (fun i => PDS.choiceOf (vs i) (Bs i) wS)
    E wS τ
  let T' := PDS.crossJointOf cls C (fun i => PDS.choiceOf (vs i) (Bt i) wT)
    E wT τ
  have hτle : ∀ i ∈ C, τ ≤ PDS.overlapOf vs Bs Bt wS wT i :=
    fun i hi => Finset.inf'_le _ hi
  have hτ0 : 0 ≤ τ :=
    Finset.le_inf' hC _ fun j hj =>
      PDS.overlapOf_nonneg (hBsnn j hj) (hBtnn j hj) (hwS j hj).le (hwT j hj).le
  have hτwS : τ ≤ wS := by
    obtain ⟨i, hi⟩ := hC
    exact (hτle i hi).trans (PDS.overlapOf_le_left (hwS i hi).le)
  have hτwT : τ ≤ wT := by
    obtain ⟨i, hi⟩ := hC
    exact (hτle i hi).trans (PDS.overlapOf_le_right (hwT i hi).le)
  have hSw : S'.weight = wS := by
    dsimp [S', E]
    exact PDS.weight_crossJointOf _ _
      (fun i hi => PDS.weight_trimOf hτ0 (hτle i hi))
      (fun i hi => PDS.weight_choiceOf (hwS i hi).le)
      (fun i hi => PDS.trimOf_le_left hτ0 (hτle i hi)
        (PDS.choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
        (PDS.choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)) hτwS
  have hTw : T'.weight = wT := by
    dsimp [T', E]
    exact PDS.weight_crossJointOf _ _
      (fun i hi => PDS.weight_trimOf hτ0 (hτle i hi))
      (fun i hi => PDS.weight_choiceOf (hwT i hi).le)
      (fun i hi => PDS.trimOf_le_right hτ0 (hτle i hi)
        (PDS.choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
        (PDS.choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)) hτwT
  have hSnn : S'.NonNeg := by
    dsimp [S', E]
    exact PDS.crossJointOf_nonNeg _ _
      (fun i hi => PDS.choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
      (fun i hi => PDS.trimOf_nonNeg hτ0 (hBsnn i hi) (hBtnn i hi)
        (hwS i hi).le (hwT i hi).le)
      (fun i hi => PDS.trimOf_le_left hτ0 (hτle i hi)
        (PDS.choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
        (PDS.choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)) hτ0 hτwS
  have hTnn : T'.NonNeg := by
    dsimp [T', E]
    exact PDS.crossJointOf_nonNeg _ _
      (fun i hi => PDS.choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)
      (fun i hi => PDS.trimOf_nonNeg hτ0 (hBsnn i hi) (hBtnn i hi)
        (hwS i hi).le (hwT i hi).le)
      (fun i hi => PDS.trimOf_le_right hτ0 (hτle i hi)
        (PDS.choiceOf_nonNeg (hBsnn i hi) (hwS i hi).le)
        (PDS.choiceOf_nonNeg (hBtnn i hi) (hwT i hi).le)) hτ0 hτwT
  obtain ⟨i₀, hi₀, hτeq⟩ :=
    Finset.exists_mem_eq_inf' hC (PDS.overlapOf vs Bs Bt wS wT)
  have hτeq' : PDS.overlapOf vs Bs Bt wS wT i₀ = τ := by
    simpa [τ] using hτeq.symm
  have hcross : (statDist S' T' : ℝ) = (wS : ℝ) - (τ : ℝ) := by
    simpa [S', T', E, τ] using
      PDS.statDist_crossJointOf (cls := cls) (vs := vs) (Bs := Bs) (Bt := Bt)
        (wS := wS) (wT := wT) hC hreal hBsnn hBtnn
        (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le)
  have hbranch : ∀ i ∈ C,
      (∑ v ∈ vs i, (statDist (Bs i v) (Bt i v) : ℝ)) =
        (wS : ℝ) - (PDS.overlapOf vs Bs Bt wS wT i : ℝ) := by
    intro i hi
    have hstatDist := Distribution.statDist_eq_weight_sub_weight_inf
      (PDS.choiceOf (vs i) (Bs i) wS) (PDS.choiceOf (vs i) (Bt i) wT)
    rw [PDS.weight_choiceOf (hwS i hi).le,
      PDS.statDist_choiceOf_eq_sum_of_branch_statDists
        (hBtnn i hi) (hwS i hi) (hwT i hi)] at hstatDist
    simpa [PDS.overlapOf] using hstatDist
  refine ⟨{
    left := S'
    right := T'
    left_nonNeg := hSnn
    right_nonNeg := hTnn
    chosen := i₀
    chosen_mem := hi₀
    left_weight := hSw
    right_weight := hTw
    left_successor_of_mem := ?_
    right_successor_of_mem := ?_
    left_successor_of_not_mem := ?_
    right_successor_of_not_mem := ?_
    left_successor_none := ?_
    right_successor_none := ?_
    left_rejects_of_class_not_mem := ?_
    right_rejects_of_class_not_mem := ?_
    delta_eq_selected_sum := ?_
    branch_sum_le_delta := ?_
  }⟩
  · intro x v hx hv
    simpa [S', E] using PDS.successorTransform_crossJointOf_left
      hτ0 hτle hBsnn hBtnn
      (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx hv
  · intro x v hx hv
    simpa [T', E] using PDS.successorTransform_crossJointOf_right
      hτ0 hτle hBsnn hBtnn
      (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx hv
  · intro x v hx hv
    simpa [S', E] using PDS.successorTransform_crossJointOf_left_of_not_mem
      hτ0 hτle hBsnn hBtnn
      (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx hv
  · intro x v hx hv
    simpa [T', E] using PDS.successorTransform_crossJointOf_right_of_not_mem
      hτ0 hτle hBsnn hBtnn
      (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx hv
  · intro x hx
    have hnn : (PDS.successorTransform S' x none).NonNeg := by
      dsimp [S', E]
      unfold PDS.successorTransform PDS.crossJointOf
      refine Distribution.NonNeg.fTransform ?_ _
      intro t
      rw [Finsupp.filter_apply]
      split
      · refine Distribution.NonNeg.fTransform (fun p => ?_) _ t
        rw [Finsupp.add_apply]
        refine add_nonneg
          (Distribution.jointProfile_nonNeg hτ0 none C (fun j hj =>
            PDS.trimOf_nonNeg hτ0 (hBsnn j hj) (hBtnn j hj)
              (hwS j hj).le (hwT j hj).le) p) ?_
        refine Distribution.jointProfile_nonNeg (by
            have := hτwS
            linarith) none C
          (fun j hj => Distribution.nonNeg_sub_of_le (PDS.trimOf_le_left hτ0 (hτle j hj)
            (PDS.choiceOf_nonNeg (hBsnn j hj) (hwS j hj).le)
            (PDS.choiceOf_nonNeg (hBtnn j hj) (hwT j hj).le))) p
      · exact le_refl 0
    apply Distribution.eq_zero_of_nonNeg_of_weight_eq_zero hnn
    rw [show Distribution.weight (PDS.successorTransform S' x none) =
        wS - ∑ v ∈ vs (cls x), (Bs (cls x) v).weight by
      simpa [S', E] using PDS.weight_successorTransform_none_crossJointOf
        hτ0 hτle hBsnn hBtnn
        (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx,
      hwS (cls x) hx, sub_self]
  · intro x hx
    have hnn : (PDS.successorTransform T' x none).NonNeg := by
      dsimp [T', E]
      unfold PDS.successorTransform PDS.crossJointOf
      refine Distribution.NonNeg.fTransform ?_ _
      intro t
      rw [Finsupp.filter_apply]
      split
      · refine Distribution.NonNeg.fTransform (fun p => ?_) _ t
        rw [Finsupp.add_apply]
        refine add_nonneg
          (Distribution.jointProfile_nonNeg hτ0 none C (fun j hj =>
            PDS.trimOf_nonNeg hτ0 (hBsnn j hj) (hBtnn j hj)
              (hwS j hj).le (hwT j hj).le) p) ?_
        refine Distribution.jointProfile_nonNeg (by
            have := hτwT
            linarith) none C
          (fun j hj => Distribution.nonNeg_sub_of_le (PDS.trimOf_le_right hτ0 (hτle j hj)
            (PDS.choiceOf_nonNeg (hBsnn j hj) (hwS j hj).le)
            (PDS.choiceOf_nonNeg (hBtnn j hj) (hwT j hj).le))) p
      · exact le_refl 0
    apply Distribution.eq_zero_of_nonNeg_of_weight_eq_zero hnn
    rw [show Distribution.weight (PDS.successorTransform T' x none) =
        wT - ∑ v ∈ vs (cls x), (Bt (cls x) v).weight by
      simpa [T', E] using PDS.weight_successorTransform_none_crossJointOf_right
        hτ0 hτle hBsnn hBtnn
        (fun i hi => (hwS i hi).le) (fun i hi => (hwT i hi).le) hx,
      hwT (cls x) hx, sub_self]
  · intro x hx
    simpa [S', E] using PDS.support_crossJointOf_rejects_of_class_not_mem
      (X := X) (Y := Y) (cls := cls)
      (fun i => PDS.choiceOf (vs i) (Bs i) wS) E wS τ hx
  · intro x hx
    simpa [T', E] using PDS.support_crossJointOf_rejects_of_class_not_mem
      (X := X) (Y := Y) (cls := cls)
      (fun i => PDS.choiceOf (vs i) (Bt i) wT) E wT τ hx
  · calc
      (statDist S' T' : ℝ) = (wS : ℝ) - (τ : ℝ) := hcross
      _ = (wS : ℝ) - (PDS.overlapOf vs Bs Bt wS wT i₀ : ℝ) := by
        rw [hτeq']
      _ = ∑ v ∈ vs i₀, (statDist (Bs i₀ v) (Bt i₀ v) : ℝ) :=
        (hbranch i₀ hi₀).symm
  · intro i hi
    calc
      (∑ v ∈ vs i, (statDist (Bs i v) (Bt i v) : ℝ)) =
          (wS : ℝ) - (PDS.overlapOf vs Bs Bt wS wT i : ℝ) :=
        hbranch i hi
      _ ≤ (wS : ℝ) - (τ : ℝ) := by
        exact sub_le_sub_left (by exact_mod_cast hτle i hi) _
      _ = (statDist S' T' : ℝ) := hcross.symm


open Classical in
/-- An honest law puts nonzero mass on any event one of its support atoms
satisfies. -/
theorem PDS.mass_ne_zero_of_mem_support {A : Type*} {μ : Distribution A}
    (hμ : μ.NonNeg) {P : A → Prop} {a : A} (ha : a ∈ μ.support) (hP : P a) :
    μ.mass P ≠ 0 := by
  intro h0
  refine Finsupp.mem_support_iff.mp ha ?_
  refine le_antisymm ?_ (hμ a)
  rw [← h0]
  unfold Distribution.mass
  simp only [Finsupp.sum]
  have hle : μ a = if P a then μ a else 0 := by rw [if_pos hP]
  rw [hle]
  refine Finset.single_le_sum (f := fun b => if P b then μ b else 0)
    (fun b _ => ?_) ha
  by_cases h : P b
  · simpa [h] using hμ b
  · simp [h]

open Classical in
/-- **Answer-image membership is nonvanishing of the branch weight.**  A first
answer occurs in the support image exactly when its successor law is not the
zero law, so two systems with equal branch weights have equal answer images.
This is what lets the reassembly criterion below compare answer partitions
without assuming a finite answer alphabet. -/
theorem PDS.mem_image_firstAnswer_iff_weight_successorTransform_ne_zero
    {R : PDS X Y} (hR : R.NonNeg) {x : X} {y : Option Y} :
    y ∈ R.support.image (fun s =>
        System.output (System.fullyDefined s) [x]
          (by rw [System.dom_fullyDefined]; simp))
      ↔ Distribution.weight (PDS.successorTransform R x y) ≠ 0 := by
  rw [PDS.weight_successorTransform]
  constructor
  · rintro hy h0
    obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp hy
    exact PDS.mass_ne_zero_of_mem_support hR hs hans h0
  · intro hmass
    by_contra hy
    refine hmass ?_
    unfold Distribution.mass
    simp only [Finsupp.sum]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [if_neg fun hans => hy (Finset.mem_image.mpr ⟨s, hs, hans⟩)]

/-! ## Lanzenberger Theorem 2.31: the query induction

Quarry architecture: `RandomSystems/BoundedAttainment.lean` throughout —
`:177`–`:246` (the transcript law at the trivial and at the stalled
environment), `:254` (the successor slice), `:290`–`:367` (the depth-zero
collapse), `:422`–`:577` (the first-answer carriers), `:584` (the reassembly
criterion), `:705` (the witness), `:723`/`:751` (base and induction).

The induction is on `q`, the number of queries the common domain answers.
At `q = 0` the domain is empty, both systems have collapsed onto the
nowhere-defined system, and the distance is the weight gap.  At `q + 1` the
first query is chosen from the finite carrier `firstQueries D`; the successors
at each realized answer are a pair on the residual domain with bound `q`, the
induction hypothesis supplies representatives and an attaining environment for
each, and Lemma 2.33 glues them into one pair — the `max` over first queries
being exactly the adaptive step `sup_e = max_x ∑_y sup_{e'}`.  The attaining
environment opens with the maximizing query and continues with the branch
environment the answer selects. -/

/-- At horizon zero the transcript law contains only the empty transcript and
the PDS weight. -/
theorem PDS.trLawFullyDefined_zero_eq_single_weight
    (S : PDS X Y) (e : System.DDE.Total Y X) :
    trLawFullyDefined e 0 S = Finsupp.single [] S.weight := by
  show Distribution.fTransform (fun _ => ([] : List (X × Option Y))) S = _
  exact Distribution.fTransform_const_eq_single_weight _ S

/-- An environment that stalls initially produces the empty transcript at
every horizon. -/
theorem System.transcript_eq_nil_of_stop_at_start
    {e : System.DDE.Total Y X} (he : e [] = none)
    (s : System.DDS X Y) :
    ∀ n, System.DDE.Total.transcript s e n = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [System.DDE.Total.transcript_succ_of_stop s e (by rw [ih]; exact he), ih]

open Classical in
/-- A PDS observed by an initially stalled environment exposes only its
weight, at every horizon. -/
theorem PDS.trLawFullyDefined_eq_single_weight_of_stop_at_start
    {e : System.DDE.Total Y X} (he : e [] = none)
    (S : PDS X Y) (n : Nat) :
    trLawFullyDefined e n S = Finsupp.single [] S.weight := by
  show Distribution.fTransform _ S = _
  have hfun : (fun s : System.DDS X Y => System.DDE.Total.transcript s e n) =
      fun _ => ([] : List (X × Option Y)) := by
    funext s
    exact System.transcript_eq_nil_of_stop_at_start he s n
  rw [hfun]
  exact Distribution.fTransform_const_eq_single_weight _ S

open Classical in
/-- If every support atom rejects `x`, the observable `none` successor is the
original PDS, exactly as required by CR18 skip semantics. -/
theorem PDS.successorTransform_none_eq_self_of_support_rejects
    {S : PDS X Y} {x : X}
    (h : ∀ s ∈ S.support, [x] ∉ System.dom s) :
    PDS.successorTransform S x none = S := by
  rw [successorTransform_none_eq_filter]
  refine Finsupp.ext fun s => ?_
  rw [Finsupp.filter_apply]
  by_cases hs : s ∈ S.support
  · rw [if_pos (h s hs)]
  · rw [Finsupp.notMem_support_iff.mp hs]
    exact ite_self 0

open Classical in
/-- An answer absent from the support answer image has a zero successor
subdistribution. -/
theorem PDS.successorTransform_eq_zero_of_not_mem_firstAnswerImage
    {S : PDS X Y} {x : X} {y : Option Y}
    (hy : y ∉ S.support.image (fun s =>
      System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp))) :
    PDS.successorTransform S x y = 0 := by
  unfold PDS.successorTransform
  rw [show S.filter (fun s =>
      System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp) = y) = 0 by
    apply Finsupp.ext
    intro s
    rw [Finsupp.filter_apply, Finsupp.coe_zero, Pi.zero_apply]
    split
    · rename_i hs
      by_cases hmem : s ∈ S.support
      · exact False.elim (hy (Finset.mem_image.mpr ⟨s, hmem, hs⟩))
      · exact Finsupp.notMem_support_iff.mp hmem
    · rfl]
  simp [Distribution.fTransform]


open Classical in
/-- Every successor pair is eligible for the induction hypothesis at one less
depth.  The theorem deliberately exposes the source restrictions in its name
and retains `[Fintype X]`, even though this local domain calculation itself
does not enumerate `X`. -/
theorem PDS.HaveCommonDomainAndBounded.successor
    [Fintype X] {S T : PDS X Y} {D : Set (List X)} {q : Nat}
    {x : X} (h : PDS.HaveCommonDomainAndBounded S T D (q + 1))
    (hx : [x] ∈ D) (y : Option Y) :
    PDS.HaveCommonDomainAndBounded
      (PDS.successorTransform S x y) (PDS.successorTransform T x y)
      (System.successorDomain D x) q := by
  rcases h with ⟨hS, hT, hD⟩
  refine ⟨?_, ?_,
    System.successor_domain_is_bounded_by_predecessor_of_bounded hD⟩
  · intro s' hs'
    unfold PDS.successorTransform at hs'
    obtain ⟨s, hs, rfl⟩ := Distribution.mem_support_fTransform _ _ hs'
    have hsS : s ∈ S.support := by
      have hsFilter : s ∈ S.support.filter (fun s =>
          System.output (System.fullyDefined s) [x]
            (by rw [System.dom_fullyDefined]; simp) = y) := by
        rw [← Finsupp.support_filter]
        exact hs
      exact (Finset.mem_filter.mp hsFilter).1
    exact System.successor_domain_eq_of_fixed_domain_and_answered
      (hS s hsS) hx
  · intro t' ht'
    unfold PDS.successorTransform at ht'
    obtain ⟨t, ht, rfl⟩ := Distribution.mem_support_fTransform _ _ ht'
    have htT : t ∈ T.support := by
      have htFilter : t ∈ T.support.filter (fun t =>
          System.output (System.fullyDefined t) [x]
            (by rw [System.dom_fullyDefined]; simp) = y) := by
        rw [← Finsupp.support_filter]
        exact ht
      exact (Finset.mem_filter.mp htFilter).1
    exact System.successor_domain_eq_of_fixed_domain_and_answered
      (hT t htT) hx

/-- A deterministic DDS whose domain is zero-bounded is the empty DDS. -/
theorem System.eq_emptySystem_of_qBounded_zero
    (s : System.DDS X Y) (h : QBounded (System.dom s) 0) :
    s = System.emptySystem := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro y
  constructor
  · intro hy
    have hdom : l ∈ System.dom s := Part.dom_iff_mem.mpr ⟨y, hy⟩
    have hlen := h l hdom
    have hl : l = [] :=
      List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst l
    exact (System.empty_not_mem s hdom).elim
  · intro hy
    simp [System.emptySystem] at hy

open Classical in
/-- A fixed-domain distribution at source depth zero is concentrated on the
empty DDS, with its original (possibly non-unit) weight. -/
theorem PDS.eq_single_emptySystem_of_dom_eq_of_qBounded_zero
    {S : PDS X Y} {D : Set (List X)}
    (hS : (∀ s ∈ S.support, System.dom s = D)) (hD : QBounded D 0) :
    S = Finsupp.single System.emptySystem S.weight := by
  apply Finsupp.eq_single_iff.mpr
  constructor
  · intro s hs
    rw [Finset.mem_singleton]
    apply System.eq_emptySystem_of_qBounded_zero s
    intro l hl
    exact hD l ((hS s hs) ▸ hl)
  · rw [Distribution.weight_eq_finsupp_sum, Finsupp.sum]
    have hsub : S.support ⊆ {System.emptySystem} := by
      intro s hs
      rw [Finset.mem_singleton]
      apply System.eq_emptySystem_of_qBounded_zero s
      intro l hl
      exact hD l ((hS s hs) ▸ hl)
    rcases Finset.subset_singleton_iff.mp hsub with hsupp | hsupp
    · have hnot : System.emptySystem ∉ S.support := by
        rw [hsupp]
        simp
      rw [hsupp, Finset.sum_empty, Finsupp.notMem_support_iff.mp hnot]
    · rw [hsupp, Finset.sum_singleton]

open Classical in
/-- The source depth-zero static distance is exactly the weight difference. -/
theorem PDS.statDist_eq_max_weight_sub_weight_of_bounded_zero
    [Fintype X] {S T : PDS X Y} {D : Set (List X)}
    (h : PDS.HaveCommonDomainAndBounded S T D 0) :
    statDist S T = max (S.weight - T.weight) 0 := by
  rcases h with ⟨hS, hT, hD⟩
  let p := S.weight
  let q := T.weight
  have hSeq : S = Finsupp.single System.emptySystem p := by
    simpa [p] using
      PDS.eq_single_emptySystem_of_dom_eq_of_qBounded_zero hS hD
  have hTeq : T = Finsupp.single System.emptySystem q := by
    simpa [q] using
      PDS.eq_single_emptySystem_of_dom_eq_of_qBounded_zero hT hD
  calc
    statDist S T = statDist (Finsupp.single System.emptySystem p)
        (Finsupp.single System.emptySystem q) := congrArg₂ statDist hSeq hTeq
    _ = max (p - q) 0 :=
      Probability.statDist_single_single _ _ _
    _ = max (S.weight - T.weight) 0 := rfl

/-- Pushing a one-atom empty-system distribution to transcripts yields one
transcript atom with the same weight. -/
theorem PDS.trLawFullyDefined_single_emptySystem
    (e : System.DDE.Total Y X) (n : Nat) (p : ℝ) :
    trLawFullyDefined e n (Finsupp.single System.emptySystem p) =
      Finsupp.single
        (System.DDE.Total.transcript
          (System.emptySystem (X := X) (Y := Y)) e n) p := by
  simp [trLawFullyDefined   , Distribution.fTransform]


open Classical in
/-- At a query admitted by the common domain, the finite first-answer image
contains no observable rejection. -/
theorem PDS.none_notMem_firstAnswerImage_of_commonDomain_answered
    {S T : PDS X Y} {D : Set (List X)} {x : X}
    (hS : (∀ s ∈ S.support, System.dom s = D))
    (hT : (∀ s ∈ T.support, System.dom s = D)) (hx : [x] ∈ D) :
    none ∉ PDS.firstAnswerImage S T x := by
  intro hnone
  obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp hnone
  have hsdom : System.dom s = D := by
    rcases Finset.mem_union.mp hs with hsS | hsT
    · exact hS s hsS
    · exact hT s hsT
  have hmem : [x] ∈ System.dom s := hsdom.symm ▸ hx
  exact (System.output_fullyDefined_eq_none_iff.mp hans) hmem

open Classical in
/-- At an answered common-domain query, the finite `Option`-answer image is
exactly the image of its finite proper-answer carrier. -/
theorem PDS.firstAnswerImage_eq_image_some_of_commonDomain_answered
    {S T : PDS X Y} {D : Set (List X)} {x : X}
    (hS : (∀ s ∈ S.support, System.dom s = D))
    (hT : (∀ s ∈ T.support, System.dom s = D)) (hx : [x] ∈ D) :
    PDS.firstAnswerImage S T x =
      (PDS.firstAnsweredValues S T x).image some := by
  ext y
  cases y with
  | none =>
      simp only [Finset.mem_image]
      constructor
      · exact fun h =>
          (PDS.none_notMem_firstAnswerImage_of_commonDomain_answered
            hS hT hx h).elim
      · rintro ⟨v, -, h⟩
        cases h
  | some v =>
      rw [Finset.mem_image]
      constructor
      · intro hv
        exact ⟨v,
          mem_first_answered_values_iff_some_mem_first_answer_image.mpr hv,
          rfl⟩
      · rintro ⟨v', hv', h⟩
        cases Option.some.inj h
        exact mem_first_answered_values_iff_some_mem_first_answer_image.mp hv'

open Classical in
/-- Summing the weights of the finitely many successor fibers over any
finite cover of the realized first-answer image recovers the original
subdistribution weight. -/
theorem PDS.sum_weight_successorTransform_eq_weight_of_image_subset
    {S : PDS X Y} {x : X} {ys : Finset (Option Y)}
    (hcover : S.support.image (fun s =>
      System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp)) ⊆ ys) :
    ∑ y ∈ ys, (PDS.successorTransform S x y).weight = S.weight := by
  rw [← Distribution.mass_true S]
  simp only [weight_successorTransform, Distribution.mass, Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  let ans := System.output (System.fullyDefined s) [x]
    (by rw [System.dom_fullyDefined]; simp)
  have hans : ans ∈ ys := hcover (Finset.mem_image_of_mem _ hs)
  rw [Finset.sum_eq_single_of_mem ans hans]
  · simp [ans]
  · intro y hy hne
    rw [if_neg]
    exact fun h => hne h.symm

open Classical in
/-- For an answered common-domain query, the proper successor branches on
one side have total mass equal to that side's original weight.  No common
mass between the two sides is assumed. -/
theorem PDS.sum_weight_successorTransform_some_eq_weight_of_commonDomain_answered
    {S T : PDS X Y} {D : Set (List X)} {x : X}
    (hS : (∀ s ∈ S.support, System.dom s = D))
    (hT : (∀ s ∈ T.support, System.dom s = D)) (hx : [x] ∈ D) :
    ∑ v ∈ PDS.firstAnsweredValues S T x,
        (PDS.successorTransform S x (some v)).weight = S.weight := by
  have hcover : S.support.image (fun s =>
      System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp)) ⊆
      PDS.firstAnswerImage S T x := by
    intro y hy
    exact Finset.mem_image.mpr <| by
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
      exact ⟨s, Finset.mem_union_left _ hs, rfl⟩
  have hsum := PDS.sum_weight_successorTransform_eq_weight_of_image_subset hcover
  rw [PDS.firstAnswerImage_eq_image_some_of_commonDomain_answered
    hS hT hx, Finset.sum_image] at hsum
  · exact hsum
  · intro a _ b _ hab
    exact Option.some.inj hab

open Classical in
/-- The first-step transcript decomposition may be summed over any finite
answer carrier covering the realized answer image; the additional fibers are
zero. -/
theorem PDS.trLawFullyDefined_successor_eq_sum_over_cover
    {S : PDS X Y} {e : System.DDE.Total Y X} {x : X} {n : Nat}
    {ys : Finset (Option Y)} (he : e [] = some x)
    (hcover : S.support.image (fun s =>
      System.output (System.fullyDefined s) [x]
        (by rw [System.dom_fullyDefined]; simp)) ⊆ ys) :
    trLawFullyDefined e (n + 1) S =
      ∑ y ∈ ys, Distribution.fTransform (fun t => (x, y) :: t)
        (trLawFullyDefined (System.DDE.Total.successor e y) n (PDS.successorTransform S x y)) := by
  rw [PDS.trLawFullyDefined_successor S e he n]
  apply Finset.sum_subset hcover
  intro y hy hyimage
  have hzero : PDS.successorTransform S x y = 0 :=
    PDS.successorTransform_eq_zero_of_not_mem_firstAnswerImage hyimage
  rw [hzero]
  simp [trLawFullyDefined   , Distribution.fTransform]

open Classical in
/-- The union answer image of two systems is a common finite carrier for the
first-step transcript decomposition of either side. -/
theorem PDS.trLawFullyDefined_successor_eq_sum_over_firstAnswerImage
    {S T : PDS X Y} {e : System.DDE.Total Y X} {x : X} {n : Nat}
    (he : e [] = some x) :
    trLawFullyDefined e (n + 1) S =
      ∑ y ∈ PDS.firstAnswerImage S T x,
        Distribution.fTransform (fun t => (x, y) :: t)
          (trLawFullyDefined (System.DDE.Total.successor e y) n (PDS.successorTransform S x y)) := by
  apply PDS.trLawFullyDefined_successor_eq_sum_over_cover he
  intro y hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr
    ⟨s, Finset.mem_union_left _ hs, rfl⟩

open Classical in
/-- If every support atom rejects a query, every proper-answer successor at
that query is zero. -/
theorem PDS.successorTransform_some_eq_zero_of_support_rejects
    {S : PDS X Y} {x : X} {v : Y}
    (h : ∀ s ∈ S.support, [x] ∉ System.dom s) :
    PDS.successorTransform S x (some v) = 0 := by
  apply PDS.successorTransform_eq_zero_of_not_mem_firstAnswerImage
  rintro hy
  obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp hy
  have hnone := System.output_fullyDefined_eq_none_iff.mpr (h s hs)
  rw [hnone] at hans
  cases hans

open Classical in
/-- If every support atom answers a query, its observable rejection successor
is zero. -/
theorem PDS.successorTransform_none_eq_zero_of_support_answers
    {S : PDS X Y} {x : X}
    (h : ∀ s ∈ S.support, [x] ∈ System.dom s) :
    PDS.successorTransform S x none = 0 := by
  apply PDS.successorTransform_eq_zero_of_not_mem_firstAnswerImage
  rintro hy
  obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp hy
  exact (System.output_fullyDefined_eq_none_iff.mp hans) (h s hs)

open Classical in
/-- A fixed-domain source is reconstructed, up to transcript equivalence,
from its weight, all answered first-query successors, and rejection outside
the fixed domain.  The finite-input hypothesis is retained because this is a
boundary lemma for the finite-source induction. -/
theorem PDS.equivalent_of_weight_eq_of_successorTransform_equivalent
    [Fintype X] {R S : PDS X Y} {D : Set (List X)}
    (hRnn : R.NonNeg) (hSnn : S.NonNeg)
    (hweight : R.weight = S.weight)
    (hS : (∀ s ∈ S.support, System.dom s = D))
    (hRreject : ∀ {x : X}, [x] ∉ D →
      ∀ r ∈ R.support, [x] ∉ System.dom r)
    (hsucc : ∀ {x : X}, [x] ∈ D → ∀ y : Option Y,
      PDS.equivalent (PDS.successorTransform R x y)
        (PDS.successorTransform S x y)) :
    PDS.equivalent R S := by
  intro e n
  induction n generalizing e with
  | zero =>
      rw [PDS.trLawFullyDefined_zero_eq_single_weight,
        PDS.trLawFullyDefined_zero_eq_single_weight, hweight]
  | succ n ih =>
      rcases he : e [] with _ | x
      · rw [PDS.trLawFullyDefined_eq_single_weight_of_stop_at_start he,
          PDS.trLawFullyDefined_eq_single_weight_of_stop_at_start he,
          hweight]
      · have hSreject : [x] ∉ D →
            ∀ s ∈ S.support, [x] ∉ System.dom s := by
          intro hx s hs hdom
          exact hx ((hS s hs) ▸ hdom)
        have hbranchweight : ∀ y : Option Y,
            (PDS.successorTransform R x y).weight =
              (PDS.successorTransform S x y).weight := by
          intro y
          by_cases hx : [x] ∈ D
          · exact PDS.weight_eq_of_equivalent (hsucc hx y)
          · cases y with
            | none =>
                rw [PDS.successorTransform_none_eq_self_of_support_rejects
                    (hRreject hx),
                  PDS.successorTransform_none_eq_self_of_support_rejects
                    (hSreject hx), hweight]
            | some v =>
                rw [PDS.successorTransform_some_eq_zero_of_support_rejects
                    (hRreject hx),
                  PDS.successorTransform_some_eq_zero_of_support_rejects
                    (hSreject hx)]
        have himage : R.support.image (fun r =>
              System.output (System.fullyDefined r) [x]
                (by rw [System.dom_fullyDefined]; simp)) =
            S.support.image (fun s =>
              System.output (System.fullyDefined s) [x]
                (by rw [System.dom_fullyDefined]; simp)) := by
          ext y
          rw [PDS.mem_image_firstAnswer_iff_weight_successorTransform_ne_zero hRnn,
            PDS.mem_image_firstAnswer_iff_weight_successorTransform_ne_zero hSnn,
            hbranchweight y]
        rw [PDS.trLawFullyDefined_successor R e he n,
          PDS.trLawFullyDefined_successor S e he n, himage]
        refine Finset.sum_congr rfl fun y _ => congrArg
          (Distribution.fTransform fun t => (x, y) :: t) ?_
        by_cases hx : [x] ∈ D
        · exact hsucc hx y (System.DDE.Total.successor e y) n
        · cases y with
          | none =>
              rw [PDS.successorTransform_none_eq_self_of_support_rejects
                  (hRreject hx),
                PDS.successorTransform_none_eq_self_of_support_rejects
                  (hSreject hx)]
              exact ih (System.DDE.Total.successor e none)
          | some v =>
              rw [PDS.successorTransform_some_eq_zero_of_support_rejects
                  (hRreject hx),
                PDS.successorTransform_some_eq_zero_of_support_rejects
                  (hSreject hx)]

/-- A deterministic system admitting no singleton query is the empty system:
prefix closure would otherwise expose the first query of any nonempty domain
history. -/
theorem System.eq_emptySystem_of_no_singleton_dom
    (s : System.DDS X Y)
    (h : ∀ x : X, [x] ∉ System.dom s) :
    s = System.emptySystem := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro y
  constructor
  · intro hy
    have hdom : l ∈ System.dom s := Part.dom_iff_mem.mpr ⟨y, hy⟩
    cases l with
    | nil => exact (System.empty_not_mem s hdom).elim
    | cons x m =>
        have hsingleton : [x] ∈ System.dom s :=
          s.2.2 (by exact ⟨m, by simp⟩) (by simp) hdom
        exact (h x hsingleton).elim
  · intro hy
    simp [System.emptySystem] at hy

open Classical in
/-- A distribution whose support atoms accept no singleton query is
concentrated on the empty deterministic system, with the same total mass. -/
theorem PDS.eq_single_emptySystem_of_support_rejects_every_query
    {S : PDS X Y}
    (h : ∀ s ∈ S.support, ∀ x : X, [x] ∉ System.dom s) :
    S = Finsupp.single System.emptySystem S.weight := by
  apply Finsupp.eq_single_iff.mpr
  constructor
  · intro s hs
    rw [Finset.mem_singleton]
    exact System.eq_emptySystem_of_no_singleton_dom s (h s hs)
  · rw [Distribution.weight_eq_finsupp_sum, Finsupp.sum]
    have hsub : S.support ⊆ {System.emptySystem} := by
      intro s hs
      rw [Finset.mem_singleton]
      exact System.eq_emptySystem_of_no_singleton_dom s (h s hs)
    rcases Finset.subset_singleton_iff.mp hsub with hsupp | hsupp
    · have hnot : System.emptySystem ∉ S.support := by
        rw [hsupp]
        simp
      rw [hsupp, Finset.sum_empty, Finsupp.notMem_support_iff.mp hnot]
    · rw [hsupp, Finset.sum_singleton]

/-- Internal induction package: representatives preserving both original
transcript classes and their separate masses, together with one finite-
horizon environment whose transcript distance is their static distance. -/

structure PDS.BoundedAttainmentWitness
    (S T : PDS X Y) (q : Nat) where
  left : PDS X Y
  right : PDS X Y
  left_nonNeg : left.NonNeg
  right_nonNeg : right.NonNeg
  left_equivalent : PDS.equivalent left S
  right_equivalent : PDS.equivalent right T
  left_weight : left.weight = S.weight
  right_weight : right.weight = T.weight
  environment : System.DDE.Total Y X
  statDist_eq_trLawFullyDefined :
    (statDist left right : Real) =
      (statDist (trLawFullyDefined environment q S)
        (trLawFullyDefined environment q T) : Real)

open Classical in
/-- Base package for the bounded-depth induction. -/
theorem PDS.exists_boundedAttainmentWitness_zero
    [Fintype X] {S T : PDS X Y} {D : Set (List X)}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : PDS.HaveCommonDomainAndBounded S T D 0) :
    Nonempty (PDS.BoundedAttainmentWitness S T 0) := by
  refine ⟨{
    left := S
    right := T
    left_nonNeg := hSnn
    right_nonNeg := hTnn
    left_equivalent := fun _ _ => rfl
    right_equivalent := fun _ _ => rfl
    left_weight := rfl
    right_weight := rfl
    environment := fun _ => none
    statDist_eq_trLawFullyDefined := ?_
  }⟩
  rw [PDS.trLawFullyDefined_zero_eq_single_weight,
    PDS.trLawFullyDefined_zero_eq_single_weight,
    Probability.statDist_single_single _ _ _]
  exact_mod_cast
    PDS.statDist_eq_max_weight_sub_weight_of_bounded_zero h

open Classical in
set_option maxHeartbeats 2000000 in
/-- The source induction: finite input carrier, one common domain, and a
uniform bound on answered queries suffice to construct representatives whose
static distance is exposed by one bounded transcript experiment. -/
theorem PDS.exists_boundedAttainmentWitness
    [Fintype X] :
    ∀ (q : Nat) (S T : PDS X Y) (D : Set (List X)),
      S.NonNeg → T.NonNeg →
      PDS.HaveCommonDomainAndBounded S T D q →
        Nonempty (PDS.BoundedAttainmentWitness S T q) := by
  intro q
  induction q with
  | zero =>
      intro S T D hSnn hTnn h
      exact
        PDS.exists_boundedAttainmentWitness_zero hSnn hTnn h
  | succ q ih =>
      intro S T D hSnn hTnn h
      let C := PDS.firstQueries D
      have hS : (∀ s ∈ S.support, System.dom s = D) := h.1
      have hT : (∀ s ∈ T.support, System.dom s = D) := h.2.1
      have hxdom : ∀ {x : X}, x ∈ C → [x] ∈ D := by
        intro x hx
        exact mem_first_queries_iff_singleton_mem_domain.mp
          (by simpa [C] using hx)
      by_cases hC : C.Nonempty
      · let branch : (x : {x : X // x ∈ C}) → (v : Y) →
            PDS.BoundedAttainmentWitness
              (PDS.successorTransform S x.1 (some v))
              (PDS.successorTransform T x.1 (some v)) q :=
          fun x v => Classical.choice <| ih
            (PDS.successorTransform S x.1 (some v))
            (PDS.successorTransform T x.1 (some v))
            (System.successorDomain D x.1)
            (successorTransform_nonNeg_of_nonNeg hSnn _ _)
            (successorTransform_nonNeg_of_nonNeg hTnn _ _)
            (HaveCommonDomainAndBounded.successor
              h (hxdom x.property) (some v))
        let vs : X → Finset Y := fun x =>
          PDS.firstAnsweredValues S T x
        let Bs : X → Y → PDS X Y := fun x v =>
          if hx : x ∈ C then (branch ⟨x, hx⟩ v).left else 0
        let Bt : X → Y → PDS X Y := fun x v =>
          if hx : x ∈ C then (branch ⟨x, hx⟩ v).right else 0
        have hwS : ∀ i ∈ C, ∑ v ∈ vs i, (Bs i v).weight = S.weight := by
          intro i hi
          calc
            ∑ v ∈ vs i, (Bs i v).weight =
                ∑ v ∈ vs i, (PDS.successorTransform S i (some v)).weight := by
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [show Bs i v = (branch ⟨i, hi⟩ v).left by
                simp [Bs, hi]]
              exact (branch ⟨i, hi⟩ v).left_weight
            _ = S.weight := by
              exact PDS.sum_weight_successorTransform_some_eq_weight_of_commonDomain_answered
                hS hT (hxdom hi)
        have hwT : ∀ i ∈ C, ∑ v ∈ vs i, (Bt i v).weight = T.weight := by
          intro i hi
          calc
            ∑ v ∈ vs i, (Bt i v).weight =
                ∑ v ∈ vs i, (PDS.successorTransform T i (some v)).weight := by
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [show Bt i v = (branch ⟨i, hi⟩ v).right by
                simp [Bt, hi]]
              exact (branch ⟨i, hi⟩ v).right_weight
            _ = T.weight := by
              simpa [vs, PDS.firstAnsweredValues,
                PDS.firstAnswerImage, Finset.union_comm] using
                (PDS.sum_weight_successorTransform_some_eq_weight_of_commonDomain_answered
                  hT hS (hxdom hi))
        have hBsnn : ∀ i ∈ C, ∀ v ∈ vs i, (Bs i v).NonNeg := by
          intro i hi v hv
          rw [show Bs i v = (branch ⟨i, hi⟩ v).left by simp [Bs, hi]]
          exact (branch ⟨i, hi⟩ v).left_nonNeg
        have hBtnn : ∀ i ∈ C, ∀ v ∈ vs i, (Bt i v).NonNeg := by
          intro i hi v hv
          rw [show Bt i v = (branch ⟨i, hi⟩ v).right by simp [Bt, hi]]
          exact (branch ⟨i, hi⟩ v).right_nonNeg
        let joint : FiniteClassJointWitness (fun x : X => x) C vs Bs Bt
            S.weight T.weight := Classical.choice <|
          PDS.exists_finiteClassJointWitness_of_common_side_weights
            (fun x : X => x) C hC (fun i _ => ⟨i, rfl⟩) vs Bs Bt
              S.weight T.weight hBsnn hBtnn hwS hwT
        have hleft : PDS.equivalent joint.left S := by
          apply
            PDS.equivalent_of_weight_eq_of_successorTransform_equivalent
              joint.left_nonNeg hSnn joint.left_weight hS
          · intro x hx
            apply joint.left_rejects_of_class_not_mem
            intro hxin
            exact hx (hxdom (by simpa using hxin))
          · intro x hx y
            have hxin : x ∈ C := by
              simpa [C] using
                (mem_first_queries_iff_singleton_mem_domain.mpr hx)
            cases y with
            | none =>
                rw [joint.left_successor_none (x := x) (by simpa using hxin),
                  PDS.successorTransform_none_eq_zero_of_support_answers
                    (fun s hs => (hS s hs).symm ▸ hx)]
                exact fun _ _ => rfl
            | some v =>
                by_cases hv : v ∈ vs x
                · rw [joint.left_successor_of_mem (x := x) (v := v)
                      (by simpa using hxin) hv,
                    show Bs x v = (branch ⟨x, hxin⟩ v).left by
                      simp [Bs, hxin]]
                  exact (branch ⟨x, hxin⟩ v).left_equivalent
                · rw [joint.left_successor_of_not_mem (x := x) (v := v)
                      (by simpa using hxin) hv]
                  have hzero : PDS.successorTransform S x (some v) = 0 := by
                    apply PDS.successorTransform_eq_zero_of_not_mem_firstAnswerImage
                    intro himage
                    apply hv
                    apply mem_first_answered_values_iff_some_mem_first_answer_image.mpr
                    obtain ⟨s, hs, hans⟩ := Finset.mem_image.mp himage
                    exact Finset.mem_image.mpr
                      ⟨s, Finset.mem_union_left _ hs, hans⟩
                  rw [hzero]
                  exact fun _ _ => rfl
        have hright : PDS.equivalent joint.right T := by
          apply
            PDS.equivalent_of_weight_eq_of_successorTransform_equivalent
              joint.right_nonNeg hTnn joint.right_weight hT
          · intro x hx
            apply joint.right_rejects_of_class_not_mem
            intro hxin
            exact hx (hxdom (by simpa using hxin))
          · intro x hx y
            have hxin : x ∈ C := by
              simpa [C] using
                (mem_first_queries_iff_singleton_mem_domain.mpr hx)
            cases y with
            | none =>
                rw [joint.right_successor_none (x := x) (by simpa using hxin),
                  PDS.successorTransform_none_eq_zero_of_support_answers
                    (fun t ht => (hT t ht).symm ▸ hx)]
                exact fun _ _ => rfl
            | some v =>
                by_cases hv : v ∈ vs x
                · rw [joint.right_successor_of_mem (x := x) (v := v)
                      (by simpa using hxin) hv,
                    show Bt x v = (branch ⟨x, hxin⟩ v).right by
                      simp [Bt, hxin]]
                  exact (branch ⟨x, hxin⟩ v).right_equivalent
                · rw [joint.right_successor_of_not_mem (x := x) (v := v)
                      (by simpa using hxin) hv]
                  have hzero : PDS.successorTransform T x (some v) = 0 := by
                    apply PDS.successorTransform_eq_zero_of_not_mem_firstAnswerImage
                    intro himage
                    apply hv
                    apply mem_first_answered_values_iff_some_mem_first_answer_image.mpr
                    obtain ⟨t, ht, hans⟩ := Finset.mem_image.mp himage
                    exact Finset.mem_image.mpr
                      ⟨t, Finset.mem_union_right _ ht, hans⟩
                  rw [hzero]
                  exact fun _ _ => rfl
        let x₀ := joint.chosen
        have hx₀ : x₀ ∈ C := joint.chosen_mem
        let e : System.DDE.Total Y X := fun ys =>
          match ys with
          | [] => some x₀
          | some v :: rest =>
              if hv : v ∈ vs x₀ then
                (branch ⟨x₀, hx₀⟩ v).environment rest
              else none
          | none :: _ => none
        have he : e [] = some x₀ := rfl
        have hsuccessor_environment : ∀ {v : Y}, v ∈ vs x₀ →
            System.DDE.Total.successor e (some v) =
              (branch ⟨x₀, hx₀⟩ v).environment := by
          intro v hv
          funext rest
          simp [System.DDE.Total.successor, e, hv]
        have htranscriptS : trLawFullyDefined e (q + 1) S =
            ∑ v ∈ vs x₀,
              Distribution.fTransform (fun t => (x₀, some v) :: t)
                (trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q (PDS.successorTransform S x₀ (some v))) := by
          rw [PDS.trLawFullyDefined_successor_eq_sum_over_firstAnswerImage
              (T := T) he,
            PDS.firstAnswerImage_eq_image_some_of_commonDomain_answered
              hS hT (hxdom hx₀), Finset.sum_image]
          · refine Finset.sum_congr rfl fun v hv => ?_
            rw [hsuccessor_environment hv]
          · intro a _ b _ hab
            exact Option.some.inj hab
        have htranscriptT : trLawFullyDefined e (q + 1) T =
            ∑ v ∈ vs x₀,
              Distribution.fTransform (fun t => (x₀, some v) :: t)
                (trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q (PDS.successorTransform T x₀ (some v))) := by
          rw [PDS.trLawFullyDefined_successor_eq_sum_over_firstAnswerImage
              (S := T) (T := S) he,
            show PDS.firstAnswerImage T S x₀ =
                PDS.firstAnswerImage S T x₀ by
              simp [PDS.firstAnswerImage, Finset.union_comm],
            PDS.firstAnswerImage_eq_image_some_of_commonDomain_answered
              hS hT (hxdom hx₀), Finset.sum_image]
          · refine Finset.sum_congr rfl fun v hv => ?_
            rw [hsuccessor_environment hv]
          · intro a _ b _ hab
            exact Option.some.inj hab
        have hbranch_distance :
            (statDist (∑ v ∈ vs x₀,
                  Distribution.fTransform (fun t => (x₀, some v) :: t)
                    (trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q (PDS.successorTransform S x₀ (some v))))
                (∑ v ∈ vs x₀,
                  Distribution.fTransform (fun t => (x₀, some v) :: t)
                    (trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q (PDS.successorTransform T x₀ (some v)))) : Real) =
              ∑ v ∈ vs x₀,
                (statDist (trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q (PDS.successorTransform S x₀ (some v)))
                    (trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q (PDS.successorTransform T x₀ (some v))) : Real) := by
          have hstatDist :=
            System.statDist_sum_cons_fTransform
              x₀ ((vs x₀).image some)
              (fun y => match y with
                | none => 0
                | some v => trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q
                    (PDS.successorTransform S x₀ (some v)))
              (fun y => match y with
                | none => 0
                | some v => trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q
                    (PDS.successorTransform T x₀ (some v)))
          rw [Finset.sum_image, Finset.sum_image, Finset.sum_image] at hstatDist
          · exact_mod_cast hstatDist
          · intro a _ b _ hab
            exact Option.some.inj hab
          · intro a _ b _ hab
            exact Option.some.inj hab
          · intro a _ b _ hab
            exact Option.some.inj hab
        refine ⟨{
          left := joint.left
          right := joint.right
          left_nonNeg := joint.left_nonNeg
          right_nonNeg := joint.right_nonNeg
          left_equivalent := hleft
          right_equivalent := hright
          left_weight := joint.left_weight
          right_weight := joint.right_weight
          environment := e
          statDist_eq_trLawFullyDefined := ?_
        }⟩
        calc
          (statDist joint.left joint.right : Real) =
              ∑ v ∈ vs x₀, (statDist (Bs x₀ v) (Bt x₀ v) : Real) := by
            simpa [x₀] using joint.delta_eq_selected_sum
          _ = ∑ v ∈ vs x₀,
                (statDist (branch ⟨x₀, hx₀⟩ v).left
                  (branch ⟨x₀, hx₀⟩ v).right : Real) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp [Bs, Bt, hx₀]
          _ = ∑ v ∈ vs x₀,
                (statDist (trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q (PDS.successorTransform S x₀ (some v)))
                    (trLawFullyDefined (branch ⟨x₀, hx₀⟩ v).environment q (PDS.successorTransform T x₀ (some v))) : Real) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            exact (branch ⟨x₀, hx₀⟩ v).statDist_eq_trLawFullyDefined
          _ = (statDist (trLawFullyDefined e (q + 1) S)
                (trLawFullyDefined e (q + 1) T) : Real) := by
            rw [htranscriptS, htranscriptT, hbranch_distance]
      · have hCempty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
        have hxnot : ∀ x : X, [x] ∉ D := by
          intro x hx
          have hxin : x ∈ C := by
            simpa [C] using
              (mem_first_queries_iff_singleton_mem_domain.mpr hx)
          rw [hCempty] at hxin
          simp at hxin
        have hSreject : ∀ s ∈ S.support, ∀ x : X,
            [x] ∉ System.dom s := by
          intro s hs x hdom
          exact hxnot x ((hS s hs) ▸ hdom)
        have hTreject : ∀ t ∈ T.support, ∀ x : X,
            [x] ∉ System.dom t := by
          intro t ht x hdom
          exact hxnot x ((hT t ht) ▸ hdom)
        have hSeq :=
          PDS.eq_single_emptySystem_of_support_rejects_every_query hSreject
        have hTeq :=
          PDS.eq_single_emptySystem_of_support_rejects_every_query hTreject
        let e : System.DDE.Total Y X := fun _ => none
        have he : e [] = none := rfl
        refine ⟨{
          left := S
          right := T
          left_nonNeg := hSnn
          right_nonNeg := hTnn
          left_equivalent := fun _ _ => rfl
          right_equivalent := fun _ _ => rfl
          left_weight := rfl
          right_weight := rfl
          environment := e
          statDist_eq_trLawFullyDefined := ?_
        }⟩
        rw [PDS.trLawFullyDefined_eq_single_weight_of_stop_at_start he,
          PDS.trLawFullyDefined_eq_single_weight_of_stop_at_start he,
          Probability.statDist_single_single _ _ _]
        have hstatic : statDist S T = max (S.weight - T.weight) 0 := by
          calc
            statDist S T = statDist (Finsupp.single System.emptySystem S.weight)
                (Finsupp.single System.emptySystem T.weight) :=
              congrArg₂ statDist hSeq hTeq
            _ = max (S.weight - T.weight) 0 :=
              Probability.statDist_single_single _ _ _
        exact_mod_cast hstatic

/-! ## Lanzenberger Theorem 2.31 and its attainment half

The induction's witness is stated against the *transcript* law at one
environment and one length; both endpoints below are that identity read
through the two eliminators of `PDS.classDistance` and through the two
directions of `PDS.advFullyDefined`'s supremum.

Everything is on `ℝ≥0∞`.  The quarry states both endpoints on `ℝ` and has to
carry `bddAbove` side conditions for its `sSup`; here the supremum is an
`iSup` in a complete lattice and there is nothing to bound. -/

/-- **Lanzenberger Theorem 2.31, attainment half.**  On the finite
shared-domain slice the infimum defining `Δ` is *attained*: there are
representatives of the two classes whose own laws are exactly `Adv⊥(S, T)`
apart, and which moreover keep the two original weights.

The witness is the query induction's output; what this statement adds is the
identification of its transcript identity with `Adv⊥`.  `≤` is one index of
the supremum (`le_iSup`, at the attaining environment and the query bound);
`≥` is the R4 bridge at the representatives, which `Adv⊥` does not
distinguish from `S` and `T` (`advFullyDefined_congr`). -/
theorem PDS.exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded
    [Fintype X] {S T : PDS X Y} {D : Set (List X)} {q : Nat}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : PDS.HaveCommonDomainAndBounded S T D q) :
    ∃ S' T' : PDS X Y,
      S'.NonNeg ∧ T'.NonNeg ∧
      PDS.equivalent S S' ∧ PDS.equivalent T T' ∧
      S'.weight = S.weight ∧ T'.weight = T.weight ∧
      ENNReal.ofReal (statDist S' T') = PDS.advFullyDefined S T := by
  obtain ⟨witness⟩ := PDS.exists_boundedAttainmentWitness q S T D hSnn hTnn h
  refine ⟨witness.left, witness.right, witness.left_nonNeg, witness.right_nonNeg,
    PDS.equivalent_symm witness.left_equivalent,
    PDS.equivalent_symm witness.right_equivalent,
    witness.left_weight, witness.right_weight, le_antisymm ?_ ?_⟩
  · rw [witness.statDist_eq_trLawFullyDefined]
    exact le_iSup_of_le witness.environment (le_iSup_of_le q le_rfl)
  · rw [PDS.advFullyDefined_congr (PDS.equivalent_symm witness.left_equivalent)
      (PDS.equivalent_symm witness.right_equivalent)]
    exact PDS.advFullyDefined_le_statDist witness.left witness.right

/-- **Lanzenberger Theorem 2.31.**  On the finite shared-domain slice the two
presentations of the distance agree:

  `Δ(S, T) = Adv⊥(S, T)`.

`≥` is `PDS.advFullyDefined_le_classDistance`, which holds outright — no
hypothesis at all.  `≤` is the attainment half read through
`PDS.classDistance_le_statDist_of_equivalent` at the attained pair.  Ruling
R9's honesty clauses on that eliminator are paid by the attainment half itself,
which produces an *honest* pair (`witness.left_nonNeg`, `witness.right_nonNeg`)
— the query induction carries honesty as an invariant precisely because the
thesis's representatives are probability systems.

The bundle cannot be dropped.  `AttainmentCounterexample` in the sibling
random-systems repository refutes the unrestricted statement on exactly this
presentation: a rejected query is a visible `⊥`, so a total environment reads
the support's domain pattern off the refusals, and no static pair of
representatives can match that. -/
theorem PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded
    [Fintype X] {S T : PDS X Y} {D : Set (List X)} {q : Nat}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : PDS.HaveCommonDomainAndBounded S T D q) :
    PDS.classDistance S T = PDS.advFullyDefined S T := by
  obtain ⟨S', T', hS'nn, hT'nn, hS', hT', -, -, hattained⟩ :=
    PDS.exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded
      hSnn hTnn h
  refine le_antisymm ?_ (PDS.advFullyDefined_le_classDistance S T)
  rw [← hattained]
  exact PDS.classDistance_le_statDist_of_equivalent hS' hT' hS'nn hT'nn

/-- **Theorem 2.31 against Definition 2.26.**  The same equality, read through
the L1 coding map: on the shared-domain slice `Adv⊥` *is* Lanzenberger's own
advantage (`PDS.advFullyDefined_eq_Adv_of_dom_eq`), so the theorem is a
statement about Definition 2.26 and not merely about Ruling R4's presentation
of it.  This is the form the thesis states. -/
theorem PDS.classDistance_eq_Adv_of_commonDomain_bounded
    [Fintype X] {S T : PDS X Y} {D : Set (List X)} {q : Nat}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg)
    (h : PDS.HaveCommonDomainAndBounded S T D q) :
    PDS.classDistance S T = PDS.Adv S T := by
  rw [PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded hSnn hTnn h,
    PDS.advFullyDefined_eq_Adv_of_dom_eq h.1 h.2.1]


/-! ## Lanzenberger Theorem 2.32: the coupling theorem for random systems

Quarry architecture: `RandomSystems/RandomSystemCoupling.lean:48,73,112` — and
the quarry's own header records what the proof is: *"This module isolates
exactly the second step"*.  Theorem 2.31 supplies the attained pair; Lemma 2.8's
attainment half (`Probability.exists_coupling_offDiagonalMass_eq`, already in
the tree) couples it.  Nothing else happens.

What the composition buys is the *reading*: the interactive advantage of two
random systems is the probability of a **static** failure event, decided once
and for all before any interaction — the two sampled deterministic systems are
simply unequal.  `advFullyDefined_le_offDiagonalMass_of_equivalent` is the
inequality a proof consumes; this is the statement that no coupling does
better. -/

/-- **Lanzenberger Theorem 2.32 (Coupling Theorem for Random Systems).**  On
the finite shared-domain slice there are representatives `S' ≡ S`, `T' ≡ T` and
an honest joint law of `S'` and `T'` whose disagreement mass is exactly
`Adv⊥(S, T)`.

Equal weight is forced, not technical: a coupling shares its mass between the
two marginals, so `|S'| = |J| = |T'|`, and equivalence preserves weight. -/
theorem PDS.exists_equivalent_coupling_offDiagonalMass_eq_advFullyDefined_of_commonDomain_bounded
    [Fintype X] {S T : PDS X Y} {D : Set (List X)} {q : Nat}
    (hSnn : S.NonNeg) (hTnn : T.NonNeg) (hweight : S.weight = T.weight)
    (h : PDS.HaveCommonDomainAndBounded S T D q) :
    ∃ (S' T' : PDS X Y) (J : Distribution (System.DDS X Y × System.DDS X Y)),
      S'.NonNeg ∧ T'.NonNeg ∧
      PDS.equivalent S S' ∧ PDS.equivalent T T' ∧
      Distribution.IsCoupling J S' T' ∧ (∀ p, 0 ≤ J p) ∧
      ENNReal.ofReal (Distribution.offDiagonalMass J) = PDS.advFullyDefined S T := by
  obtain ⟨S', T', hS'nn, hT'nn, hS', hT', hSw, hTw, hattained⟩ :=
    PDS.exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded
      hSnn hTnn h
  obtain ⟨J, hJ, hJnn, hJmass⟩ :=
    Probability.exists_coupling_offDiagonalMass_eq hS'nn hT'nn
      (by rw [hSw, hTw, hweight])
  exact ⟨S', T', J, hS'nn, hT'nn, hS', hT', hJ, hJnn, by rw [hJmass, hattained]⟩

/-- Theorem 2.32 for probability systems, in the thesis's own shape: the joint
is a genuine probability distribution.  Normalization is inherited — a coupling
carries the marginal's weight, and equivalence preserves weight, so the joint
of two attained representatives of probability systems is normalized. -/
theorem PDS.exists_equivalent_probCoupling_offDiagonalMass_eq_advFullyDefined_of_commonDomain_bounded
    [Fintype X] {S T : PDS X Y} {D : Set (List X)} {q : Nat}
    (hS : S.isProbDist) (hT : T.isProbDist)
    (h : PDS.HaveCommonDomainAndBounded S T D q) :
    ∃ (S' T' : PDS X Y) (J : Distribution (System.DDS X Y × System.DDS X Y)),
      J.isProbDist ∧
      PDS.equivalent S S' ∧ PDS.equivalent T T' ∧
      Distribution.IsCoupling J S' T' ∧
      ENNReal.ofReal (Distribution.offDiagonalMass J) = PDS.advFullyDefined S T := by
  obtain ⟨S', T', J, hS'nn, -, hS'e, hT'e, hJ, hJnn, hJmass⟩ :=
    PDS.exists_equivalent_coupling_offDiagonalMass_eq_advFullyDefined_of_commonDomain_bounded
      hS.nonNeg hT.nonNeg (by rw [hS.weight_eq, hT.weight_eq]) h
  refine ⟨S', T', J, ⟨hJnn, ?_⟩, hS'e, hT'e, hJ, hJmass⟩
  calc J.weight = (Distribution.fTransform Prod.fst J).weight :=
        (Distribution.weight_fTransform Prod.fst J).symm
    _ = S'.weight := congrArg Distribution.weight hJ.1
    _ = S.weight := (PDS.weight_eq_of_equivalent hS'e).symm
    _ = 1 := hS.weight_eq


end

end RandomSystems
