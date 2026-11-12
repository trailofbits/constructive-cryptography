module

public import RandomSystems.Cumulative.Presentation.Basic
public import RandomSystems.Cumulative.FiniteCuts
public import RandomSystems.PDS.FiniteCuts

/-!
# Restricting conditional-choice presentations

`realization_choiceAt_finite` bounds every finite table's realization.
`replies_realization_choiceAt_nodeInclusion` preserves its retained prefixes, and
`cutSystem_realization_choiceAt` combines these facts into exact deterministic restriction.
`IsRandomSystem.replyChoice_cutMass` and `choiceLaw_cutMass` identify each finite cut's
conditional choices with the same global kernels, including zero-mass histories.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

variable {A B : Type}

namespace Presentation

/-- A table through horizon `n` never replies to a longer input history. -/
lemma realization_choiceAt_finite {n : ℕ} (c : Node A B n → Option B) :
    Finite n (realization (choiceAt c)).1 := by
  intro xs hd
  by_contra hn
  have hs := (realization (choiceAt c)).2
  have hne : xs ≠ [] := fun he => hs.1 (he ▸ hd)
  -- A defined answer supplies a completed transcript at this input history.
  obtain ⟨ys, hr⟩ := ((hs.reach_iff hne).mpr hd).exists_replies
  have first : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by rw [hr.length])
  have second : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by rw [hr.length])
  have length : (xs.zip ys).length = xs.length := by rw [List.length_zip, hr.length, Nat.min_self]
  have nonempty : xs.zip ys ≠ [] := by
    intro he
    rw [he, List.length_nil] at length
    exact hne (List.length_eq_zero_iff.mp length.symm)
  obtain ⟨t, z, ht⟩ := List.eq_nil_or_concat (xs.zip ys) |>.resolve_left nonempty
  rw [List.concat_eq_append] at ht
  have replies : Replies (realization (choiceAt c)).1
      ((t ++ [z]).map Prod.fst) ((t ++ [z]).map Prod.snd) := by
    rw [← ht, first, second]
    exact hr
  -- Its final answer would require a table choice beyond the horizon.
  have last := ((replies_realization_snoc (choiceAt c) t z.1 z.2).mp replies).2
  have beyond : ¬ t.length < n := by
    rw [ht, List.length_append, List.length_singleton] at length
    omega
  simp only [choiceAt, dite_eq_right beyond] at last
  cases last

/-- Restricting a choice table preserves every completed transcript within the shorter horizon. -/
lemma replies_realization_choiceAt_nodeInclusion {m n : ℕ} (hmn : m ≤ n)
    (c : Node A B n → Option B) (t : List (A × B)) (ht : t.length ≤ m) :
    Replies (realization (choiceAt (c ∘ nodeInclusion hmn))).1
        (t.map Prod.fst) (t.map Prod.snd) ↔
      Replies (realization (choiceAt c)).1 (t.map Prod.fst) (t.map Prod.snd) := by
  apply replies_realization_congr
  intro h x hh
  have hm := hh.trans_le ht
  rw [choiceAt, choiceAt, dite_eq_left hm, dite_eq_left (hm.trans_le hmn)]
  rfl

/-- Restricting the realized system equals realizing the restricted finite choice table. -/
lemma cutSystem_realization_choiceAt {m n : ℕ} (hmn : m ≤ n)
    (c : Node A B n → Option B) :
    cutSystem (realization (choiceAt c)).1 m =
      (realization (choiceAt (c ∘ nodeInclusion hmn))).1 := by
  -- DDS equality reduces to completed replies, retained or beyond the cut.
  apply IsDDS.eq_of_replies_iff ((realization (choiceAt c)).2.cutSystem m)
    (realization (choiceAt (c ∘ nodeInclusion hmn))).2
  intro xs ys
  by_cases sameLength : ys.length = xs.length
  · by_cases retained : xs.length ≤ m
    · rw [replies_cutSystem_iff _ _ retained]
      have first := List.map_fst_zip (show xs.length ≤ ys.length by rw [sameLength])
      have second := List.map_snd_zip (show ys.length ≤ xs.length by rw [sameLength])
      have congruent := replies_realization_choiceAt_nodeInclusion hmn c (xs.zip ys)
        (by simpa only [List.length_zip, sameLength, Nat.min_self] using retained)
      simpa only [first, second] using congruent.symm
    · have nonempty : xs ≠ [] := by rintro rfl; exact retained (Nat.zero_le m)
      constructor
      · intro hr
        exact (retained ((filterDom_dom _ _ _).mp (hr.dom nonempty)).1).elim
      · intro hr
        exact (retained (realization_choiceAt_finite _ xs (hr.dom nonempty))).elim
  · exact iff_of_false (fun hr => sameLength hr.length) (fun hr => sameLength hr.length)

end Presentation

namespace IsRandomSystem

variable {D : List (A × B) → A → Prop} {p : List (A × B) → ℝ} (hp : IsRandomSystem D p)

/-- Every node strictly before a cut uses the same conditional law as the global behavior. -/
lemma replyChoice_cutMass {n : ℕ} {h : List (A × B)} (hl : h.length < n) (x : A) :
    (IsRandomSystem.cutMass D p hp n).isSubprobabilistic.replyChoice h x =
      hp.isSubprobabilistic.replyChoice h x := by
  apply IsSubprobabilistic.replyChoice_congr
  · exact ite_eq_left (Nat.le_of_lt hl)
  · intro y
    exact ite_eq_left (by simpa only [List.length_append, List.length_singleton]
      using Nat.succ_le_of_lt hl)

/-- The finite cut and the global behavior have identical laws on all table nodes. -/
lemma choiceLaw_cutMass [Fintype A] [Fintype B] (n : ℕ) :
    (IsRandomSystem.cutMass D p hp n).isSubprobabilistic.choiceLaw n =
      hp.isSubprobabilistic.choiceLaw n := by
  classical
  exact congrArg Distribution.pi (funext fun j => hp.replyChoice_cutMass j.1.2 j.2)

end IsRandomSystem

end SystemAlgebra
