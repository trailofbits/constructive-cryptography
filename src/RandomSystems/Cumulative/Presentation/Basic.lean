module

public import RandomSystems.Cumulative.Cumulative
public import RandomSystems.Cumulative.Subprobability
public import RandomSystems.PDS.Conditional

/-!
# Finite conditional-choice tables

`realization` answers along the transcript determined by its reply choices.
`Presentation.Node` indexes the finitely many choices before a horizon;
`IsSubprobabilistic.choiceLaw` samples these choices independently.
`mass_replies` computes the realization's cumulative mass, while `realization_possible` and
`RandomSystem.hasDomain_realization` certify supported transcripts and exact query domains.
These facts supply the explicit finite-presentation constructor and its restriction laws.

Finite presentations express the interpretation "think of a probabilistic system as an
equivalence class of distributions over deterministic systems" [1, Abstract].

## References

1. D. Lanzenberger and U. Maurer. *Coupling of Random Systems*. In Theory of Cryptography
   (TCC 2020), Springer, 2020. Cryptology ePrint Archive, Paper 2020/1187.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

variable {A B : Type}

/-! ### Realizations of reply choices -/

/-- The deterministic system answering by the reply choice `g`: after each
transcript, a reply or no reply. -/
noncomputable def realization (g : List (A × B) → A → Option B) : DDS A B :=
  DDS.ofConditional fun h x => (g h x : Part B)

lemma realization_snoc (g : List (A × B) → A → Option B) {h : List (A × B)}
    (hr : Replies (realization g).1 (h.map Prod.fst) (h.map Prod.snd)) (x : A) :
    (realization g).1 (h.map Prod.fst ++ [x]) = (g h x : Part B) :=
  DDS.ofConditional_snoc _ hr x

lemma replies_realization_snoc (g : List (A × B) → A → Option B) (t : List (A × B))
    (x : A) (y : B) :
    Replies (realization g).1 ((t ++ [(x, y)]).map Prod.fst) ((t ++ [(x, y)]).map Prod.snd) ↔
      Replies (realization g).1 (t.map Prod.fst) (t.map Prod.snd) ∧ g t x = some y := by
  simp only [List.map_append, List.map_singleton]
  constructor
  · intro hr
    obtain ⟨hr, hs⟩ := replies_snoc.mp hr
    rw [realization_snoc g hr] at hs
    refine ⟨hr, ?_⟩
    cases hg : g t x with
    | none => rw [hg] at hs; exact absurd hs (by simp)
    | some z => rw [hg] at hs; simpa using hs
  · rintro ⟨hr, hg⟩
    exact replies_snoc.mpr ⟨hr, by rw [realization_snoc g hr, hg]; rfl⟩

/-- Reply events depend only on the choices at strictly shorter transcripts. -/
lemma replies_realization_congr (t : List (A × B)) (g g' : List (A × B) → A → Option B)
    (hg : ∀ h x, h.length < t.length → g h x = g' h x) :
    Replies (realization g).1 (t.map Prod.fst) (t.map Prod.snd) ↔
      Replies (realization g').1 (t.map Prod.fst) (t.map Prod.snd) := by
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t z ih =>
    obtain ⟨x, y⟩ := z
    rw [replies_realization_snoc, replies_realization_snoc,
      ih fun h x' hl => hg h x' (by simp; omega), hg t x (by simp)]

namespace Presentation

/-- Transcripts shorter than `n`: the finitely many places where a reply is chosen. -/
abbrev Hist (A B : Type) (n : ℕ) := {h : List (A × B) // h.length < n}

instance [_root_.Finite A] [_root_.Finite B] (n : ℕ) : _root_.Finite (Hist A B n) :=
  Finite.of_injective (fun h : Hist A B n => fun k : Fin n => h.1[k.1]?) (by
    intro a b hab
    apply Subtype.ext
    apply List.ext_getElem?
    intro k
    by_cases hk : k < n
    · exact congrFun hab ⟨k, hk⟩
    · rw [List.getElem?_eq_none (by have := a.2; omega),
        List.getElem?_eq_none (by have := b.2; omega)])

noncomputable instance [Fintype A] [Fintype B] (n : ℕ) : Fintype (Hist A B n) :=
  Fintype.ofFinite _

/-- A history node: a short transcript and the next query. -/
abbrev Node (A B : Type) (n : ℕ) := Hist A B n × A

/-- Include each shorter-horizon node as the same transcript and query at a longer horizon. -/
def nodeInclusion {m n : ℕ} (hmn : m ≤ n) : Node A B m ↪ Node A B n where
  toFun j := (⟨j.1.1, j.1.2.trans_le hmn⟩, j.2)
  inj' := by
    rintro ⟨h, x⟩ ⟨k, y⟩ same
    exact Prod.ext (Subtype.ext (congrArg (fun j => j.1.1) same))
      (congrArg (fun j : Node A B n => j.2) same)

/-- A choice at each node, extended by no reply beyond the bound. -/
noncomputable def choiceAt {n : ℕ} (c : Node A B n → Option B) (h : List (A × B)) (x : A) :
    Option B :=
  if hl : h.length < n then c (⟨h, hl⟩, x) else none

end Presentation

open Presentation

namespace IsSubprobabilistic

variable {p : List (A × B) → ℝ} (hp : IsSubprobabilistic p)

/-- A choice of replies all of positive probability, including no reply where
stopping is possible. -/
def PossibleChoice (g : List (A × B) → A → Option B) : Prop :=
  ∀ h x, g h x ∈ (hp.replyChoice h x).support

lemma replyChoice_none (h : List (A × B)) (x : A) :
    hp.replyChoice h x none = 1 - (hp.extensionLaw h x).weight / p h := by
  classical
  simp only [replyChoice, Finsupp.add_apply, Finsupp.single_apply, ite_true]
  have h0 : Distribution.fTransform some
      ((hp.extensionLaw h x).mapRange (fun w => w / p h) (zero_div _)) none = 0 :=
    Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨b, hb⟩; cases hb)
  rw [h0, zero_add, Distribution.weight_mapRange_div]

lemma replyChoice_support_nonempty (h : List (A × B)) (x : A) :
    (hp.replyChoice h x).support.Nonempty := by
  apply Finsupp.support_nonempty_iff.mpr
  intro hz
  have hw := (hp.replyChoice_isProbDist h x).2
  rw [hz] at hw
  norm_num [Distribution.weight] at hw

/-- Realizations of possible choices produce only possible transcripts. -/
lemma realization_possible (g : List (A × B) → A → Option B) (hg : hp.PossibleChoice g)
    {h : List (A × B)}
    (hr : Replies (realization g).1 (h.map Prod.fst) (h.map Prod.snd)) : p h ≠ 0 := by
  induction h using List.reverseRecOn with
  | nil => rw [hp.1]; exact one_ne_zero
  | append_singleton h z ih =>
    obtain ⟨x, y⟩ := z
    obtain ⟨hr, hy⟩ := (replies_realization_snoc g h x y).mp hr
    have hn := Finsupp.mem_support_iff.mp (hg h x)
    rw [hy, hp.replyChoice_some] at hn
    exact (div_ne_zero_iff.mp hn).1

variable [Fintype A] [Fintype B] (n : ℕ)

open Classical in
/-- The independent product of the reply-choice laws over all nodes. -/
noncomputable def choiceLaw : Distribution (Node A B n → Option B) :=
  pi fun j => hp.replyChoice j.1.1 j.2

lemma choiceLaw_isProbDist : (hp.choiceLaw n).isProbDist := by
  classical
  exact ⟨pi_nonNeg fun j => (hp.replyChoice_isProbDist j.1.1 j.2).1, by
    rw [choiceLaw, weight_pi]
    exact Finset.prod_eq_one fun j _ => (hp.replyChoice_isProbDist j.1.1 j.2).2⟩

/-- The normalized independent table law has a supported table for its default realization. -/
lemma choiceLaw_support_nonempty : (hp.choiceLaw n).support.Nonempty := by
  classical
  apply Finsupp.support_nonempty_iff.mpr
  intro hz
  have hw := (hp.choiceLaw_isProbDist n).2
  rw [hz] at hw
  norm_num [Distribution.weight] at hw

variable {n}

omit [Fintype A] [Fintype B] in
/-- Beyond the bound, no reply is the possible choice. -/
lemma none_mem_support {h : List (A × B)} (x : A) (hn : ∀ h, n < h.length → p h = 0)
    (hl : ¬ h.length < n) : none ∈ (hp.replyChoice h x).support := by
  classical
  rw [Finsupp.mem_support_iff, hp.replyChoice_none]
  have hw : (hp.extensionLaw h x).weight = 0 := by
    unfold Distribution.weight
    exact Finset.sum_eq_zero fun y _ => by
      rw [hp.extensionLaw_apply]
      exact hn _ (by simp; omega)
  rw [hw, zero_div, sub_zero]
  exact one_ne_zero

/-- Supported node choices are possible choices everywhere. -/
lemma choiceAt_supported (hn : ∀ h, n < h.length → p h = 0) {c : Node A B n → Option B}
    (hc : c ∈ (hp.choiceLaw n).support) : hp.PossibleChoice (choiceAt c) := by
  classical
  intro h x
  unfold choiceAt
  split_ifs with hl
  · have hsub : (pi fun j : Node A B n => hp.replyChoice j.1.1 j.2).support ⊆
        Fintype.piFinset fun j : Node A B n => (hp.replyChoice j.1.1 j.2).support :=
      Finsupp.support_onFinset_subset
    exact Fintype.mem_piFinset.mp (hsub hc) (⟨h, hl⟩, x)
  · exact hp.none_mem_support x hn hl

/-- The chain rule: the reply masses of the realizations are the cumulative masses. -/
lemma mass_replies (hn : ∀ h, n < h.length → p h = 0) (t : List (A × B)) :
    (hp.choiceLaw n).mass (fun c =>
      Replies (realization (choiceAt c)).1 (t.map Prod.fst) (t.map Prod.snd)) = p t := by
  classical
  induction t using List.reverseRecOn with
  | nil =>
    simp only [List.map_nil, replies_nil]
    rw [mass_true, (hp.choiceLaw_isProbDist n).2, hp.1]
  | append_singleton t z ih =>
    obtain ⟨x, y⟩ := z
    by_cases hl : t.length < n
    · let j : Node A B n := (⟨t, hl⟩, x)
      have hc : ∀ c : Node A B n → Option B, choiceAt c t x = c j := fun c => by
        simp only [choiceAt, dite_eq_left hl, j]
      rw [Distribution.mass_congr _ (fun c => (replies_realization_snoc (choiceAt c) t x y).trans
        (by rw [hc c]))]
      rw [choiceLaw, mass_pi_and_eq (fun j : Node A B n => hp.replyChoice j.1.1 j.2)
        (fun j => (hp.replyChoice_isProbDist j.1.1 j.2).2) j (some y)
        (fun c => Replies (realization (choiceAt c)).1 (t.map Prod.fst) (t.map Prod.snd)) ?hev]
      · rw [← choiceLaw, ih]
        change p t * hp.replyChoice t x (some y) = p (t ++ [(x, y)])
        rw [hp.replyChoice_some]
        by_cases h0 : p t = 0
        · rw [h0, zero_mul, hp.mass_eq_zero_of_prefix (List.prefix_append _ _) h0]
        · field_simp
      · -- The event before the step ignores the node of the step.
        intro c b'
        apply replies_realization_congr
        intro h x' hl'
        simp only [choiceAt]
        split_ifs with hh
        · rw [Function.update_of_ne]
          intro heq
          have := congrArg (fun q : Node A B n => q.1.1.length) heq
          simp only [j] at this
          omega
        · rfl
    · rw [Distribution.mass_eq_zero_of_forall_not _ (fun c hr => by
        have := ((replies_realization_snoc (choiceAt c) t x y).mp hr).2
        simp [choiceAt, hl] at this)]
      exact (hn _ (by simp; omega)).symm

end IsSubprobabilistic

namespace RandomSystem

variable [Fintype A] [Fintype B] {D : Domain A B}

/-- On a random system, realizations of possible choices answer exactly on its domain. -/
lemma hasDomain_realization (R : RandomSystem A B D) {g : List (A × B) → A → Option B}
    (hg : R.2.isSubprobabilistic.PossibleChoice g) :
    HasDomain D (realization g).1 := by
  classical
  have hp := R.2.isSubprobabilistic
  intro t x hr
  have hpos : R t ≠ 0 := hp.realization_possible g hg hr
  rw [realization_snoc g hr]
  have hext : hp.extensionLaw t x = R.extensionLaw t x :=
    Finsupp.ext fun y => by rw [hp.extensionLaw_apply, R.extensionLaw_apply]
  constructor
  · intro hd
    by_contra hn
    obtain ⟨y, hy⟩ : ∃ y, g t x = some y := by
      cases hgt : g t x with
      | none => rw [hgt] at hd; exact absurd hd (by simp)
      | some z => exact ⟨z, rfl⟩
    have hmem := Finsupp.mem_support_iff.mp (hg t x)
    rw [hy, hp.replyChoice_some, R.mass_eq_zero_of_not_admitted hn, zero_div] at hmem
    exact hmem rfl
  · intro hd
    cases hgt : g t x with
    | some z => trivial
    | none =>
      have hmem := Finsupp.mem_support_iff.mp (hg t x)
      rw [hgt, hp.replyChoice_none, hext, R.extensionLaw_weight, ite_eq_left hd,
        div_self hpos, sub_self] at hmem
      exact absurd rfl hmem

end RandomSystem

end SystemAlgebra
