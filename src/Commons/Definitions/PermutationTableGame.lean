module

public import Commons.Definitions.Ideal
public import Commons.Schemes.Sponge.Table
public import ConstructiveCryptography.Instances.Game
public import ConstructiveCryptography.Notation.Basic
public import Probability.Permutation.Walk
public import RandomSystems.Game.UntilBad
public import RandomSystems.Typed.AutomatonGame

/-!
# Adaptive table-monitoring games on `StrongURP`

Generic framework for adaptive security proofs over a bidirectional uniform random permutation
`StrongURP X` [1, §4.3], [2, Definition 3.15].

Given a downward-closed predicate `Good : List (PermutationEdge X) → Prop` on directed
partial-permutation tables:

* `tableMonitorGame q Good hGood_mono` retains `π ∼ 𝒰[Equiv.Perm X]` on `Bidirectional X q` and
  sets the monotone binary output (MBO) as soon as `¬ Good (queryHistoryTable q π xs)`.
* `tableMonitorGame_visible` proves that hiding the MBO recovers `StrongURP X` identically.
* `tableMonitorGame_unsetMBOs_eq` and `tableMonitorGame_set_mass_eq` express unset-transcript and
  one-step set-bit masses as uniform permutation events over the recorded table.
* `tableMonitorGame_set_mass_le_of_badEvent` bounds every one-step set-bit transition: replayed
  forward or inverse queries cost zero, and fresh queries pay at most `(|X| / (|X| - q)) · c`
  whenever the fresh reply avoids `Good` with uniform state mass at most `c`.
* `tableMonitorGame_winProbability_le_of_linear`, `tableMonitorGame_win_le_of_linear`, and
  `tableMonitorGame_dist_le_of_linear` sum linear per-step bounds `a · (n + 1) + b · n` into
  adaptive winning-probability and CC statistical distance (`Δ`, `|≡`, `≃[...]`) bounds [2].

## References

1. G. Bertoni, J. Daemen, M. Peeters, and G. Van Assche. *On the Indifferentiability of the
   Sponge Construction*. EUROCRYPT 2008, LNCS 4965, pp. 181–197.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Commons.StrongURP

open CategoryTheory SystemAlgebra Probability Probability.Distribution Probability.Counting
open Commons.Sponge
open scoped BigOperators NNReal SystemAlgebra

section TableBridge

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Map a `Bidirectional` port to the edge direction flag (`false` forward, `true` inverse). -/
def portIsInverse : Bidirectional.Port → Bool
  | .forward => false
  | .inverse => true

/-- Extract the underlying state value from a `Bidirectional` query. -/
def queryPoint (q : ℕ) (u : Σ i, (Bidirectional X q).X i) : X :=
  match u with
  | ⟨.forward, x⟩ => x
  | ⟨.inverse, y⟩ => y

/-- Reply function of `StrongURP X` on forward and inverse ports. -/
def permReply (q : ℕ) (π : Equiv.Perm X) :
    (i : (Bidirectional X q).I) → (Bidirectional X q).X i → (Bidirectional X q).Y i
  | .forward, x => π x
  | .inverse, y => π.symm y

/-- Tagged reply of `π` on a `Bidirectional` query. -/
def permEval (q : ℕ) (π : Equiv.Perm X) (u : Σ i, (Bidirectional X q).X i) :
    Σ i, (Bidirectional X q).Y i :=
  ⟨u.1, permReply q π u.1 u.2⟩

/-- Directed partial-permutation table induced by running `π` on a `Bidirectional` query list. -/
def queryHistoryTable (q : ℕ) (π : Equiv.Perm X)
    (xs : List (Σ i, (Bidirectional X q).X i)) : List (PermutationEdge X) :=
  xs.foldl (fun table u => insertEdge table (queryEdge π (portIsInverse u.1) (queryPoint q u))) []

/-- Directed edge represented by a single visible `Bidirectional` query/reply pair. -/
def transcriptEdge (q : ℕ)
    (z : (Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i) : PermutationEdge X :=
  match z with
  | (⟨.forward, x⟩, ⟨.forward, y⟩) => ⟨x, y, false⟩
  | (⟨.forward, x⟩, ⟨.inverse, y⟩) => ⟨x, y, false⟩
  | (⟨.inverse, y⟩, ⟨.forward, x⟩) => ⟨x, y, true⟩
  | (⟨.inverse, y⟩, ⟨.inverse, x⟩) => ⟨x, y, true⟩

/-- Directed partial-permutation table induced by a visible `Bidirectional` transcript. -/
def transcriptTable (q : ℕ)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)) :
    List (PermutationEdge X) :=
  h.foldl (fun table z => insertEdge table (transcriptEdge q z)) []

/-- Distinct permutation inputs recorded in `table`. -/
def recordedInputs (table : List (PermutationEdge X)) : Finset X :=
  (table.map PermutationEdge.input).toFinset

omit [Fintype X] in
/-- The number of recorded inputs is bounded by the table length. -/
lemma recordedInputs_card_le (table : List (PermutationEdge X)) :
    (recordedInputs table).card ≤ table.length :=
  (List.toFinset_card_le _).trans (by simp only [List.length_map, le_rfl])

/-- The induced transcript table has at most one edge per query/reply pair. -/
lemma length_transcriptTable_le (q : ℕ)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)) :
    (transcriptTable q h).length ≤ h.length := by
  induction h using List.reverseRecOn with
  | nil => simp only [transcriptTable, List.foldl_nil, List.length_nil, le_rfl]
  | append_singleton h z ih =>
    simp only [transcriptTable, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    exact (length_insertEdge_le _ _).trans (Nat.add_le_add_right ih 1)

lemma queryHistoryTable_append_singleton (q : ℕ) (π : Equiv.Perm X)
    (xs : List (Σ i, (Bidirectional X q).X i)) (u : Σ i, (Bidirectional X q).X i) :
    queryHistoryTable q π (xs ++ [u]) =
      insertEdge (queryHistoryTable q π xs)
        (queryEdge π (portIsInverse u.1) (queryPoint q u)) := by
  simp only [queryHistoryTable, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma transcriptTable_append_singleton (q : ℕ)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (z : (Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i) :
    transcriptTable q (h ++ [z]) = insertEdge (transcriptTable q h) (transcriptEdge q z) := by
  simp only [transcriptTable, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Prefix queries produce a subset of the recorded edges. -/
lemma queryHistoryTable_subset_of_prefix (q : ℕ) (π : Equiv.Perm X)
    {xs ys : List (Σ i, (Bidirectional X q).X i)} (hp : xs <+: ys) :
    ∀ e ∈ queryHistoryTable q π xs, e ∈ queryHistoryTable q π ys := by
  obtain ⟨rest, rfl⟩ := hp
  induction rest using List.reverseRecOn with
  | nil =>
    intro e he
    simpa only [List.append_nil] using he
  | append_singleton rest u ih =>
    intro e he
    rw [← List.append_assoc, queryHistoryTable_append_singleton]
    exact insertEdge_subset _ _ e (ih e he)

omit [DecidableEq X] in
lemma transcriptEdge_eq_queryEdge_of_permEval (q : ℕ) (π : Equiv.Perm X)
    (z : (Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)
    (hz : permEval q π z.1 = z.2) :
    transcriptEdge q z = queryEdge π (portIsInverse z.1.1) (queryPoint q z.1) := by
  rcases z with ⟨⟨p1, x⟩, ⟨p2, y⟩⟩
  cases p1 <;> cases p2
  · simp only [permEval, permReply, Sigma.mk.injEq, heq_eq_eq, true_and] at hz
    subst hz
    rfl
  · simp only [permEval, permReply, Sigma.mk.injEq, reduceCtorEq, false_and] at hz
  · simp only [permEval, permReply, Sigma.mk.injEq, reduceCtorEq, false_and] at hz
  · simp only [permEval, permReply, Sigma.mk.injEq, heq_eq_eq, true_and] at hz
    subst hz
    rfl

/-- Whenever `π` answers every pair in `h`, the query-history table agrees with `transcriptTable`
and satisfies `AgreesWith`. -/
lemma queryHistoryTable_eq_transcriptTable_of_replies (q : ℕ) (π : Equiv.Perm X)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (hr : ∀ z ∈ h, permEval q π z.1 = z.2) :
    queryHistoryTable q π (h.map Prod.fst) = transcriptTable q h ∧
      AgreesWith (transcriptTable q h) π := by
  induction h using List.reverseRecOn with
  | nil =>
    exact ⟨rfl, fun _ hm => by cases hm⟩
  | append_singleton h z ih =>
    have hprev : ∀ w ∈ h, permEval q π w.1 = w.2 :=
      fun w hw => hr w (List.mem_append_left _ hw)
    have hz : permEval q π z.1 = z.2 :=
      hr z (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨heq, hagr⟩ := ih hprev
    rw [List.map_append, List.map_singleton, queryHistoryTable_append_singleton,
      transcriptTable_append_singleton, heq, transcriptEdge_eq_queryEdge_of_permEval q π z hz]
    exact ⟨rfl, insertEdge_agrees _ _ π hagr (queryEdge_agrees π _ _)⟩

/-- A permutation `π` matches a consistent transcript `h` iff it agrees with `transcriptTable`. -/
lemma permEval_forall_iff_agreesWith (q : ℕ) (π₀ π : Equiv.Perm X)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (hr₀ : ∀ z ∈ h, permEval q π₀ z.1 = z.2) :
    (∀ z ∈ h, permEval q π z.1 = z.2) ↔ AgreesWith (transcriptTable q h) π := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [transcriptTable, List.foldl_nil, AgreesWith, List.not_mem_nil, false_implies,
      implies_true]
  | append_singleton h z ih =>
    have hprev : ∀ w ∈ h, permEval q π₀ w.1 = w.2 :=
      fun w hw => hr₀ w (List.mem_append_left _ hw)
    have hz₀ : permEval q π₀ z.1 = z.2 :=
      hr₀ z (List.mem_append_right _ (List.mem_singleton_self _))
    have hagr₀ := (queryHistoryTable_eq_transcriptTable_of_replies q π₀ h hprev).2
    rw [transcriptTable_append_singleton, transcriptEdge_eq_queryEdge_of_permEval q π₀ z hz₀,
      insertEdge_query_agrees_iff (transcriptTable q h) π₀ hagr₀ (portIsInverse z.1.1)
        (queryPoint q z.1) π,
      ← ih hprev, List.forall_mem_append, List.forall_mem_singleton]
    refine and_congr_right fun _ => ?_
    rcases z with ⟨⟨p1, x⟩, ⟨p2, y⟩⟩
    cases p1 <;> cases p2 <;>
      simp only [permEval, permReply, portIsInverse, queryPoint, Bool.false_eq_true, ↓reduceIte,
        Sigma.mk.injEq, heq_eq_eq, true_and, reduceCtorEq, false_and] at hz₀ ⊢
    · rw [← hz₀]
    · rw [← hz₀]

omit [Fintype X] in
/-- Agreement with a table satisfied by `π₀` is agreement with `π₀` on `recordedInputs`. -/
lemma agreesWith_iff_recordedInputs (π₀ π : Equiv.Perm X)
    (table : List (PermutationEdge X)) (hagr₀ : AgreesWith table π₀) :
    AgreesWith table π ↔ ∀ x ∈ recordedInputs table, π x = π₀ x := by
  constructor
  · intro hagr x hx
    obtain ⟨edge, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact (hagr edge hm).trans (hagr₀ edge hm).symm
  · intro hpts edge hm
    have hx : edge.input ∈ recordedInputs table :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨edge, hm, rfl⟩)
    exact (hpts edge.input hx).trans (hagr₀ edge hm)

omit [DecidableEq X] in
lemma replies_permReply_iff (q : ℕ) (π : Equiv.Perm X)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)) :
    Replies (filterDom (Bidirectional X q).domain
        (automatonSystem (fun π i x => (π, permReply q π i x)) π))
        (h.map Prod.fst) (h.map Prod.snd) ↔
      (h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst)) ∧
        ∀ z ∈ h, permEval q π z.1 = z.2 := by
  have heq : filterDom (Bidirectional X q).domain
        (automatonSystem (fun π i x => (π, permReply q π i x)) π) =
      (DDS.ofFunction (Bidirectional X q).domain (Bidirectional X q).nonempty_prefix
        (permEval q π)).1 :=
    Interface.automatonDDS_eq_ofFunction (Bidirectional X q) (permReply q) π
  rw [heq, DDS.replies_ofFunction_iff, List.map_eq_nil_iff, List.map_map, List.map_eq_map_iff]
  refine and_congr_right fun _ => ?_
  exact ⟨fun hf z hz => (hf z hz).symm, fun hf z hz => (hf z hz).symm⟩

end TableBridge

/-! ### Monotone table-monitoring game and one-step conditional bound -/

section MonotoneGame

noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X]

open Classical in
/-- Generic monotone table-monitoring game on `StrongURP X`: retains `π ∼ 𝒰[Equiv.Perm X]` and
sets the MBO as soon as `¬ Good (queryHistoryTable q π xs)`. -/
def tableMonitorGame (q : ℕ)
    -- `Good` is a downward-closed property of partial-permutation tables.
    (Good : List (PermutationEdge X) → Prop)
    (hGood_mono : ∀ {t₁ t₂ : List (PermutationEdge X)},
      (∀ e ∈ t₁, e ∈ t₂) → Good t₂ → Good t₁) :
    TypedGame (Bidirectional X q) :=
  TypedGame.ofAutomaton (Bidirectional X q) (fun π i x => (π, permReply q π i x))
    𝒰[Equiv.Perm X]
    (fun π => ⟨fun xs => ¬ Good (queryHistoryTable q π xs),
      fun _ _ hp hbad hgood =>
        hbad (hGood_mono (queryHistoryTable_subset_of_prefix q π hp) hgood)⟩)

open Classical in
/-- Hiding the MBO of `tableMonitorGame` recovers `StrongURP X`. -/
lemma tableMonitorGame_visible (q : ℕ)
    (Good : List (PermutationEdge X) → Prop)
    (hGood_mono : ∀ {t₁ t₂ : List (PermutationEdge X)},
      (∀ e ∈ t₁, e ∈ t₂) → Good t₂ → Good t₁) :
    (tableMonitorGame q Good hGood_mono).visible = StrongURP X (q := q) := by
  rw [tableMonitorGame, TypedGame.visible_ofAutomaton, TypedSystem.ofAutomaton_eq_sample]
  unfold StrongURP
  simp only [ProbDist.uniform]
  congr 1
  · exact congrFun (congrArg (@Distribution.uniform (Equiv.Perm X)) (Subsingleton.elim _ _)) _
  · funext π
    congr 1
    funext i x
    cases i <;> rfl

open Classical in
/-- Cumulative mass of `StrongURP X` on a transcript `h`. -/
lemma strongURP_mass_eq (q : ℕ)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)) :
    (StrongURP X (q := q)).1 h =
      (Distribution.uniform (Equiv.Perm X)).mass (fun π =>
        (h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst)) ∧
          ∀ z ∈ h, permEval q π z.1 = z.2) := by
  rw [StrongURP, TypedSystem.sample_ofFunction_mass, behaviorMass, mass_fTransform]
  convert mass_congr (Distribution.uniform (Equiv.Perm X)) (fun π => ?_)
  have hrep := replies_permReply_iff q π h
  have heq : filterDom (Bidirectional X q).domain
        (automatonSystem (fun π i x => (π, permReply q π i x)) π) =
      (DDS.ofFunction (Bidirectional X q).domain (Bidirectional X q).nonempty_prefix
        (permEval q π)).1 :=
    Interface.automatonDDS_eq_ofFunction (Bidirectional X q) (permReply q) π
  rw [heq] at hrep
  convert hrep using 2
  congr 2
  funext ⟨i, x⟩
  cases i <;> rfl

open Classical in
/-- The unset-MBO cumulative mass equals the `StrongURP` mass restricted to `Good` transcripts. -/
lemma tableMonitorGame_unsetMBOs_eq (q : ℕ)
    (Good : List (PermutationEdge X) → Prop) (hGood_nil : Good [])
    (hGood_mono : ∀ {t₁ t₂ : List (PermutationEdge X)},
      (∀ e ∈ t₁, e ∈ t₂) → Good t₂ → Good t₁)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i)) :
    (tableMonitorGame q Good hGood_mono).1.1 (unsetMBOs h) =
      if Good (transcriptTable q h) then (StrongURP X (q := q)).1 h else 0 := by
  classical
  rw [tableMonitorGame, TypedGame.ofAutomaton_mass_unsetMBOs]
  swap
  · intro _ _ hn
    exact hn hGood_nil
  simp only [ProbDist.uniform]
  by_cases hg : Good (transcriptTable q h)
  · rw [ite_eq_left hg, strongURP_mass_eq]
    convert mass_congr (Distribution.uniform (Equiv.Perm X)) (fun π => ?_)
    have hrep := replies_permReply_iff q π h
    constructor
    · exact fun ⟨hr, _⟩ => hrep.mp hr
    · intro hr
      refine ⟨hrep.mpr hr, ?_⟩
      rw [(queryHistoryTable_eq_transcriptTable_of_replies q π h hr.2).1]
      exact not_not.mpr hg
  · rw [ite_eq_right hg]
    apply mass_eq_zero_of_forall_not
    rintro π ⟨hr, hnot⟩
    have hr' := (replies_permReply_iff q π h).mp hr
    rw [(queryHistoryTable_eq_transcriptTable_of_replies q π h hr'.2).1] at hnot
    exact hnot hg

open Classical in
/-- One-step set-bit mass of `tableMonitorGame` from a consistent, `Good` transcript `h`. -/
lemma tableMonitorGame_set_mass_eq (q : ℕ)
    (Good : List (PermutationEdge X) → Prop) (hGood_nil : Good [])
    (hGood_mono : ∀ {t₁ t₂ : List (PermutationEdge X)},
      (∀ e ∈ t₁, e ∈ t₂) → Good t₂ → Good t₁)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (π₀ : Equiv.Perm X) (hr₀ : ∀ z ∈ h, permEval q π₀ z.1 = z.2)
    (hgood : Good (transcriptTable q h))
    (u : Σ i, (Bidirectional X q).X i)
    (hadm : (Bidirectional X q).domain (h.map Prod.fst ++ [u])) :
    (∑ y, (tableMonitorGame q Good hGood_mono).1.1 (unsetMBOs h ++ [(u, tagMBO true y)])) =
      (Distribution.uniform (Equiv.Perm X)).mass (fun π =>
        (∀ x ∈ recordedInputs (transcriptTable q h), π x = π₀ x) ∧
          ¬ Good (insertEdge (transcriptTable q h)
            (queryEdge π (portIsInverse u.1) (queryPoint q u)))) := by
  classical
  set G := (tableMonitorGame q Good hGood_mono).1.1
  have hagr₀ := (queryHistoryTable_eq_transcriptTable_of_replies q π₀ h hr₀).2
  have hadmH : h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst) := by
    by_cases hn : h = []
    · exact Or.inl hn
    · exact Or.inr ((Bidirectional X q).nonempty_prefix.2 (List.prefix_append _ _)
        (fun he => hn (List.map_eq_nil_iff.mp he)) hadm)
  have hmass : G (unsetMBOs h) =
      (Distribution.uniform (Equiv.Perm X)).mass
        (fun π => ∀ x ∈ recordedInputs (transcriptTable q h), π x = π₀ x) := by
    rw [tableMonitorGame_unsetMBOs_eq q Good hGood_nil hGood_mono h, ite_eq_left hgood,
      strongURP_mass_eq]
    apply mass_congr
    intro π
    simp only [hadmH, true_and, permEval_forall_iff_agreesWith q π₀ π h hr₀,
      agreesWith_iff_recordedInputs π₀ π (transcriptTable q h) hagr₀]
  have hsum : (∑ y : Σ i, (Bidirectional X q).Y i, G (unsetMBOs (h ++ [(u, y)]))) =
      (Distribution.uniform (Equiv.Perm X)).mass (fun π =>
        (∀ x ∈ recordedInputs (transcriptTable q h), π x = π₀ x) ∧
          Good (insertEdge (transcriptTable q h)
            (queryEdge π (portIsInverse u.1) (queryPoint q u)))) := by
    have hstep (y : Σ i, (Bidirectional X q).Y i) :
        G (unsetMBOs (h ++ [(u, y)])) =
          (Distribution.uniform (Equiv.Perm X)).mass (fun π =>
            ((∀ x ∈ recordedInputs (transcriptTable q h), π x = π₀ x) ∧
              Good (insertEdge (transcriptTable q h)
                (queryEdge π (portIsInverse u.1) (queryPoint q u)))) ∧
              permEval q π u = y) := by
      rw [tableMonitorGame_unsetMBOs_eq q Good hGood_nil hGood_mono (h ++ [(u, y)])]
      by_cases hgy : Good (transcriptTable q (h ++ [(u, y)]))
      · rw [ite_eq_left hgy, strongURP_mass_eq]
        apply mass_congr
        intro π
        have hadm' : h ++ [(u, y)] = [] ∨
            (Bidirectional X q).domain ((h ++ [(u, y)]).map Prod.fst) :=
          Or.inr (by simpa only [List.map_append, List.map_singleton] using hadm)
        simp only [hadm', true_and, List.forall_mem_append, List.forall_mem_singleton,
          permEval_forall_iff_agreesWith q π₀ π h hr₀,
          agreesWith_iff_recordedInputs π₀ π (transcriptTable q h) hagr₀]
        constructor
        · rintro ⟨hpts, hy⟩
          have hedge := transcriptEdge_eq_queryEdge_of_permEval q π (u, y) hy
          rw [transcriptTable_append_singleton, hedge] at hgy
          exact ⟨⟨hpts, hgy⟩, hy⟩
        · rintro ⟨⟨hpts, _⟩, hy⟩
          exact ⟨hpts, hy⟩
      · rw [ite_eq_right hgy]
        symm
        apply mass_eq_zero_of_forall_not
        rintro π ⟨⟨_, hgπ⟩, hy⟩
        have hedge := transcriptEdge_eq_queryEdge_of_permEval q π (u, y) hy
        rw [transcriptTable_append_singleton, hedge] at hgy
        exact hgy hgπ
    simp only [hstep]
    rw [mass_eq_sum_mass_fiber _ _ (fun π => permEval q π u) Finset.univ
      (fun _ _ => Finset.mem_univ _)]
  have norm := RandomSystem.sum_unsetMBOs_add_sum_tagMBO G hadm
  rw [hsum, hmass] at norm
  have split := mass_and_add_mass_not_and (Distribution.uniform (Equiv.Perm X))
    (fun π => Good (insertEdge (transcriptTable q h)
      (queryEdge π (portIsInverse u.1) (queryPoint q u))))
    (fun π => ∀ x ∈ recordedInputs (transcriptTable q h), π x = π₀ x)
  have hcomm1 := mass_congr (Distribution.uniform (Equiv.Perm X))
    (fun π => and_comm (a := ∀ x ∈ recordedInputs (transcriptTable q h), π x = π₀ x)
      (b := Good (insertEdge (transcriptTable q h)
        (queryEdge π (portIsInverse u.1) (queryPoint q u)))))
  have hcomm2 := mass_congr (Distribution.uniform (Equiv.Perm X))
    (fun π => and_comm (a := ∀ x ∈ recordedInputs (transcriptTable q h), π x = π₀ x)
      (b := ¬ Good (insertEdge (transcriptTable q h)
        (queryEdge π (portIsInverse u.1) (queryPoint q u)))))
  rw [hcomm1] at norm
  rw [hcomm2]
  linarith

open Classical in
/-- One-step conditional bad-event bound for `tableMonitorGame`: replays cost zero, and fresh
forward/inverse queries pay at most `(|X| / (|X| - q)) · c` whenever the per-step bad event has
uniform state mass at most `c`. -/
lemma tableMonitorGame_set_mass_le_of_badEvent [Nonempty X] (q : ℕ)
    (hq : q < Fintype.card X)
    (Good : List (PermutationEdge X) → Prop) (hGood_nil : Good [])
    (hGood_mono : ∀ {t₁ t₂ : List (PermutationEdge X)},
      (∀ e ∈ t₁, e ∈ t₂) → Good t₂ → Good t₁)
    -- `stepBound len` bounds the uniform state probability of triggering `¬ Good` after `len`
    -- queries.
    (stepBound : ℕ → ℝ) (hstep_nonneg : ∀ n, 0 ≤ stepBound n)
    (hbad : ∀ (table : List (PermutationEdge X)) (inverse : Bool),
      Good table →
      ∃ bad : X → Prop,
        (∀ edge : PermutationEdge X, edge.inverse = inverse →
          ¬ Good (table ++ [edge]) → bad edge.freshEndpoint) ∧
        (Distribution.uniform X).mass bad ≤ stepBound table.length)
    (hstep_mono : Monotone stepBound)
    (h : List ((Σ i, (Bidirectional X q).X i) × Σ i, (Bidirectional X q).Y i))
    (u : Σ i, (Bidirectional X q).X i)
    (hadm : (Bidirectional X q).domain (h.map Prod.fst ++ [u])) :
    (∑ y, (tableMonitorGame q Good hGood_mono).1.1 (unsetMBOs h ++ [(u, tagMBO true y)])) ≤
      ((Fintype.card X : ℝ) / (Fintype.card X - q : ℝ)) * stepBound h.length *
        (tableMonitorGame q Good hGood_mono).1.1 (unsetMBOs h) := by
  classical
  set G := (tableMonitorGame q Good hGood_mono).1.1
  by_cases hpos : G (unsetMBOs h) = 0
  · rw [hpos, mul_zero]
    exact le_of_eq (Finset.sum_eq_zero fun y _ =>
      RandomSystem.mass_eq_zero_of_prefix G (List.prefix_append _ _) hpos)
  · have hgood : Good (transcriptTable q h) := by
      by_contra hng
      apply hpos
      rw [tableMonitorGame_unsetMBOs_eq q Good hGood_nil hGood_mono h, ite_eq_right hng]
    have hEx : ∃ π₀ : Equiv.Perm X, ∀ z ∈ h, permEval q π₀ z.1 = z.2 := by
      by_contra hno
      push Not at hno
      apply hpos
      rw [tableMonitorGame_unsetMBOs_eq q Good hGood_nil hGood_mono h, ite_eq_left hgood,
        strongURP_mass_eq]
      apply mass_eq_zero_of_forall_not
      rintro π ⟨_, hr⟩
      obtain ⟨z, hz, hne⟩ := hno π
      exact hne (hr z hz)
    obtain ⟨π₀, hr₀⟩ := hEx
    have hagr₀ := (queryHistoryTable_eq_transcriptTable_of_replies q π₀ h hr₀).2
    have hsetEq := tableMonitorGame_set_mass_eq q Good hGood_nil hGood_mono h π₀ hr₀ hgood u hadm
    have hadmH : h = [] ∨ (Bidirectional X q).domain (h.map Prod.fst) := by
      by_cases hn : h = []
      · exact Or.inl hn
      · exact Or.inr ((Bidirectional X q).nonempty_prefix.2 (List.prefix_append _ _)
          (fun he => hn (List.map_eq_nil_iff.mp he)) hadm)
    have hmassEq : G (unsetMBOs h) =
        (Distribution.uniform (Equiv.Perm X)).mass
          (fun π => ∀ x ∈ recordedInputs (transcriptTable q h), π x = π₀ x) := by
      rw [tableMonitorGame_unsetMBOs_eq q Good hGood_nil hGood_mono h, ite_eq_left hgood,
        strongURP_mass_eq]
      apply mass_congr
      intro π
      simp only [hadmH, true_and, permEval_forall_iff_agreesWith q π₀ π h hr₀,
        agreesWith_iff_recordedInputs π₀ π (transcriptTable q h) hagr₀]
    rw [hsetEq, hmassEq]
    set table := transcriptTable q h
    set points := recordedInputs table
    have hlen_lt : h.length < q := by
      have hle := (Bidirectional X q).length_le _ hadm
      simp only [List.length_append, List.length_map, List.length_singleton] at hle
      omega
    have hpts_le : points.card ≤ q :=
      (recordedInputs_card_le table).trans
        ((length_transcriptTable_le q h).trans (Nat.le_of_lt hlen_lt))
    by_cases hfresh :
        if portIsInverse u.1 then queryPoint q u ∉ points.image π₀ else queryPoint q u ∉ points
    · -- Fresh query: apply `permutation_reply_event_mass_le`.
      obtain ⟨bad, hbadImpl, hbadMass⟩ := hbad table (portIsInverse u.1) hgood
      have hmono :
          (Distribution.uniform (Equiv.Perm X)).mass (fun π =>
            (∀ x ∈ points, π x = π₀ x) ∧
              ¬ Good (insertEdge table (queryEdge π (portIsInverse u.1) (queryPoint q u)))) ≤
          (Distribution.uniform (Equiv.Perm X)).mass (fun π =>
            (∀ x ∈ points, π x = π₀ x) ∧
              bad (if portIsInverse u.1 then π.symm (queryPoint q u) else π (queryPoint q u))) := by
        apply Distribution.mass_mono Distribution.uniform_nonNeg
        rintro π ⟨hpts, hng⟩
        refine ⟨hpts, ?_⟩
        have hnotdup : ¬ ∃ prev ∈ table,
            prev.input = (queryEdge π (portIsInverse u.1) (queryPoint q u)).input := by
          intro hdup
          unfold insertEdge at hng
          rw [ite_eq_left hdup] at hng
          exact hng hgood
        unfold insertEdge at hng
        rw [ite_eq_right hnotdup] at hng
        have hinvEq :
            (queryEdge π (portIsInverse u.1) (queryPoint q u)).inverse = portIsInverse u.1 := by
          rcases u with ⟨port, point⟩
          cases port <;> rfl
        have hfe : (queryEdge π (portIsInverse u.1) (queryPoint q u)).freshEndpoint =
            if portIsInverse u.1 then π.symm (queryPoint q u) else π (queryPoint q u) := by
          rcases u with ⟨port, point⟩
          cases port <;> rfl
        rw [← hfe]
        exact hbadImpl _ hinvEq hng
      have hreply := Counting.permutation_reply_event_mass_le π₀ points bad (portIsInverse u.1)
        (queryPoint q u) hfresh
      have hden_pos : (0 : ℝ) < (Fintype.card X : ℝ) - q := by
        have : (q : ℝ) < Fintype.card X := by exact_mod_cast hq
        linarith
      have hden_le : (Fintype.card X : ℝ) - q ≤ (Fintype.card X : ℝ) - points.card := by
        have : (points.card : ℝ) ≤ q := by exact_mod_cast hpts_le
        linarith
      have hratio : (Fintype.card X : ℝ) / ((Fintype.card X : ℝ) - points.card) ≤
          (Fintype.card X : ℝ) / ((Fintype.card X : ℝ) - q) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden_pos hden_le
      have hstep_le : (Distribution.uniform X).mass bad ≤ stepBound h.length :=
        hbadMass.trans (hstep_mono (length_transcriptTable_le q h))
      have hmul :
          ((Fintype.card X : ℝ) / (Fintype.card X - points.card : ℝ)) *
              (Distribution.uniform X).mass bad ≤
            ((Fintype.card X : ℝ) / (Fintype.card X - q : ℝ)) * stepBound h.length :=
        mul_le_mul hratio hstep_le (Distribution.uniform_nonNeg.mass_nonneg _)
          (div_nonneg (Nat.cast_nonneg _) (le_of_lt hden_pos))
      exact (hmono.trans hreply).trans
        (mul_le_mul_of_nonneg_right hmul (Distribution.uniform_nonNeg.mass_nonneg _))
    · -- Replay query: the input is already in `table`, so `insertEdge` is a no-op and mass is 0.
      have hzero :
          (Distribution.uniform (Equiv.Perm X)).mass (fun π =>
            (∀ x ∈ points, π x = π₀ x) ∧
              ¬ Good (insertEdge table (queryEdge π (portIsInverse u.1) (queryPoint q u)))) =
            0 := by
        apply mass_eq_zero_of_forall_not
        rintro π ⟨hpts, hng⟩
        have hdup : ∃ prev ∈ table,
            prev.input = (queryEdge π (portIsInverse u.1) (queryPoint q u)).input := by
          rcases u with ⟨port, point⟩
          cases port with
          | forward =>
            simp only [portIsInverse, queryPoint, Bool.false_eq_true, ↓reduceIte, not_not] at hfresh
            obtain ⟨prev, hp, hpi⟩ := List.mem_map.mp (List.mem_toFinset.mp hfresh)
            exact ⟨prev, hp, hpi⟩
          | inverse =>
            simp only [portIsInverse, queryPoint, ↓reduceIte, not_not, Finset.mem_image] at hfresh
            obtain ⟨x, hx, hπ₀x⟩ := hfresh
            obtain ⟨prev, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
            have hπx : π prev.input = point := (hpts prev.input hx).trans hπ₀x
            have hsym : π.symm point = prev.input := by
              rw [← hπx, π.symm_apply_apply]
            exact ⟨prev, hp, hsym.symm⟩
        unfold insertEdge at hng
        rw [ite_eq_left hdup] at hng
        exact hng hgood
      rw [hzero]
      have hden_pos : (0 : ℝ) < (Fintype.card X : ℝ) - q := by
        have : (q : ℝ) < Fintype.card X := by exact_mod_cast hq
        linarith
      exact mul_nonneg
        (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt hden_pos)) (hstep_nonneg h.length))
        (Distribution.uniform_nonNeg.mass_nonneg _)

end

end MonotoneGame

/-! ### Linear step-cost summation and CC distance bridge -/

section CostHelpers

/-- Closed form for summing a linear per-step cost `a · (n + 1) + b · n` along a transcript. -/
lemma transcriptCost_linear_sum {A B : Type} (a b : ℝ) (h : List (A × B)) :
    transcriptCost (fun p _ => a * (p.length + 1 : ℝ) + b * (p.length : ℝ)) h =
      a * ((h.length + 1).choose 2 : ℝ) + b * (h.length.choose 2 : ℝ) := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [transcriptCost, List.length_nil, Nat.zero_add, Nat.choose_zero_succ,
      Nat.cast_zero, mul_zero, add_zero]
    simp only [Nat.choose_eq_zero_of_lt (by omega : 1 < 2), Nat.cast_zero, mul_zero]
  | append_singleton h z ih =>
    rw [transcriptCost_snoc, ih, List.length_append, List.length_singleton]
    have h1 : ((h.length + 1 + 1).choose 2 : ℝ) =
        ((h.length + 1).choose 2 : ℝ) + (h.length + 1 : ℝ) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, Nat.cast_add, Nat.cast_one]
      ring
    have h2 : ((h.length + 1).choose 2 : ℝ) = (h.length.choose 2 : ℝ) + (h.length : ℝ) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
      ring
    rw [h1, h2]
    ring

variable {X : Type} [Fintype X] [DecidableEq X]

open Classical in
/-- Every compatible stopping distinguisher wins `tableMonitorGame` with probability at most
`(|X| / (|X| - q)) · (a · C(q + 1, 2) + b · C(q, 2))` when each step's bad event has uniform
state mass at most `a · (table.length + 1) + b · table.length`. -/
lemma tableMonitorGame_winProbability_le_of_linear [Nonempty X] (q : ℕ)
    (hq : q < Fintype.card X)
    (Good : List (PermutationEdge X) → Prop) (hGood_nil : Good [])
    (hGood_mono : ∀ {t₁ t₂ : List (PermutationEdge X)},
      (∀ e ∈ t₁, e ∈ t₂) → Good t₂ → Good t₁)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbad : ∀ (table : List (PermutationEdge X)) (inverse : Bool),
      Good table →
      ∃ bad : X → Prop,
        (∀ edge : PermutationEdge X, edge.inverse = inverse →
          ¬ Good (table ++ [edge]) → bad edge.freshEndpoint) ∧
        (Distribution.uniform X).mass bad ≤
          a * (table.length + 1 : ℝ) + b * (table.length : ℝ))
    (P : (Bidirectional X q).inputDomain.Distinguisher) :
    P.winProbability (tableMonitorGame q Good hGood_mono).1.1 ≤
      ((Fintype.card X : ℝ) / (Fintype.card X - q : ℝ)) *
        (a * ((q + 1).choose 2 : ℝ) + b * (q.choose 2 : ℝ)) := by
  let ratio : ℝ := (Fintype.card X : ℝ) / (Fintype.card X - q : ℝ)
  have hden_pos : (0 : ℝ) < (Fintype.card X : ℝ) - q := by
    have : (q : ℝ) < Fintype.card X := by exact_mod_cast hq
    linarith
  have hratio_nonneg : 0 ≤ ratio := div_nonneg (Nat.cast_nonneg _) (le_of_lt hden_pos)
  let stepBound : ℕ → ℝ := fun n => a * (n + 1 : ℝ) + b * (n : ℝ)
  have hset := tableMonitorGame_set_mass_le_of_badEvent q hq Good hGood_nil hGood_mono stepBound
    (fun n => by positivity) hbad
    (fun m n hmn => by
      have hm1 : (m + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hmn 1
      have hm2 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      exact add_le_add (mul_le_mul_of_nonneg_left hm1 ha) (mul_le_mul_of_nonneg_left hm2 hb))
  apply P.winProbability_le_of_transcriptCost_le (tableMonitorGame q Good hGood_mono).1.2
    (tableMonitorGame q Good hGood_mono).2
    (β := fun h _ => (ratio * a) * (h.length + 1 : ℝ) + (ratio * b) * (h.length : ℝ))
    (fun h _ => by positivity)
    (fun h u hu => by
      have hcoef : (ratio * a) * (h.length + 1 : ℝ) + (ratio * b) * (h.length : ℝ) =
          ratio * stepBound h.length := by
        dsimp only [stepBound]
        ring
      rw [hcoef]
      exact hset h u hu)
  intro h hh
  have hlen : h.length ≤ q := by
    rcases List.eq_nil_or_concat h with rfl | ⟨h', z, rfl⟩
    · simp only [List.length_nil, Nat.zero_le]
    · rw [List.concat_eq_append] at hh
      have hadm : (Bidirectional X q).domain ((h' ++ [z]).map Prod.fst) := by
        by_contra hd
        apply hh
        exact RandomSystem.mass_eq_zero_of_not_admitted
          (tableMonitorGame q Good hGood_mono).1.1.visible
          (by
            change ¬ (Bidirectional X q).domain (h'.map Prod.fst ++ [z.1])
            simpa only [List.map_append, List.map_singleton] using hd) z.2
      have hle := (Bidirectional X q).length_le _ hadm
      rw [List.length_map, List.length_append, List.length_singleton] at hle
      simpa only [List.length_concat] using hle
  rw [transcriptCost_linear_sum]
  have hc1 : ((h.length + 1).choose 2 : ℝ) ≤ ((q + 1).choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_le_choose 2 (Nat.add_le_add_right hlen 1)
  have hc2 : (h.length.choose 2 : ℝ) ≤ (q.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_le_choose 2 hlen
  have hsum_le :
      (ratio * a) * ((h.length + 1).choose 2 : ℝ) + (ratio * b) * (h.length.choose 2 : ℝ) ≤
        (ratio * a) * ((q + 1).choose 2 : ℝ) + (ratio * b) * (q.choose 2 : ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left hc1 (mul_nonneg hratio_nonneg ha))
      (mul_le_mul_of_nonneg_left hc2 (mul_nonneg hratio_nonneg hb))
  calc
    (ratio * a) * ((h.length + 1).choose 2 : ℝ) + (ratio * b) * (h.length.choose 2 : ℝ)
      ≤ (ratio * a) * ((q + 1).choose 2 : ℝ) + (ratio * b) * (q.choose 2 : ℝ) := hsum_le
    _ = ratio * (a * ((q + 1).choose 2 : ℝ) + b * (q.choose 2 : ℝ)) := by ring

open Classical in
/-- Every admitted winner on `Bidirectional X q` wins `tableMonitorGame` with probability at most
`(|X| / (|X| - q)) · (a · C(q + 1, 2) + b · C(q, 2))` under a linear per-step bad-event bound. -/
theorem tableMonitorGame_win_le_of_linear [Nonempty X] (q : ℕ)
    (hq : q < Fintype.card X)
    (Good : List (PermutationEdge X) → Prop) (hGood_nil : Good [])
    (hGood_mono : ∀ {t₁ t₂ : List (PermutationEdge X)},
      (∀ e ∈ t₁, e ∈ t₂) → Good t₂ → Good t₁)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbad : ∀ (table : List (PermutationEdge X)) (inverse : Bool),
      Good table →
      ∃ bad : X → Prop,
        (∀ edge : PermutationEdge X, edge.inverse = inverse →
          ¬ Good (table ++ [edge]) → bad edge.freshEndpoint) ∧
        (Distribution.uniform X).mass bad ≤
          a * (table.length + 1 : ℝ) + b * (table.length : ℝ))
    {winner : TypedGame (Bidirectional X q) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners (Bidirectional X q)) :
    winner (tableMonitorGame q Good hGood_mono) ≤
      ((Fintype.card X : ℝ) / (Fintype.card X - q : ℝ)) *
        (a * ((q + 1).choose 2 : ℝ) + b * (q.choose 2 : ℝ)) :=
  Interface.win_le
    (tableMonitorGame_winProbability_le_of_linear q hq Good hGood_nil hGood_mono a b ha hb hbad)
    hw

open Classical in
/-- Any system conditionally equivalent to `tableMonitorGame` is within the linear-step bound of
`StrongURP X` [2, Theorem 4.17]. -/
theorem tableMonitorGame_dist_le_of_linear [Nonempty X] (q : ℕ)
    (hq : q < Fintype.card X)
    (Good : List (PermutationEdge X) → Prop) (hGood_nil : Good [])
    (hGood_mono : ∀ {t₁ t₂ : List (PermutationEdge X)},
      (∀ e ∈ t₁, e ∈ t₂) → Good t₂ → Good t₁)
    (a b : ℝ≥0)
    (hbad : ∀ (table : List (PermutationEdge X)) (inverse : Bool),
      Good table →
      ∃ bad : X → Prop,
        (∀ edge : PermutationEdge X, edge.inverse = inverse →
          ¬ Good (table ++ [edge]) → bad edge.freshEndpoint) ∧
        (Distribution.uniform X).mass bad ≤
          (a : ℝ) * (table.length + 1 : ℝ) + (b : ℝ) * (table.length : ℝ))
    {T : TypedSystem (Bidirectional X q)}
    (hc : tableMonitorGame q Good hGood_mono |≡ T) :
    Δ (StrongURP X (q := q)) T ≤
      (((Fintype.card X : ℝ≥0) / (Fintype.card X - q : ℕ)) *
        (a * ((q + 1).choose 2 : ℝ≥0) + b * (q.choose 2 : ℝ≥0)) : ℝ≥0) := by
  rw [← tableMonitorGame_visible q Good hGood_mono]
  -- Conditional equivalence transports the uniform winner bound through the abstract game law.
  apply Interface.dist_visible_le_of_win hc
  intro P
  have hwin := tableMonitorGame_winProbability_le_of_linear q hq Good hGood_nil hGood_mono
    (a : ℝ) (b : ℝ) a.property b.property hbad P
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_div, NNReal.coe_natCast,
    Nat.cast_sub hq.le] using hwin

end CostHelpers

end Commons.StrongURP
