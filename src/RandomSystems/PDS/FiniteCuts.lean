module

public import RandomSystems.PDS.FiniteCuts.Defs

/-!
# Deterministic systems through finite horizons

`IsDDS.cutSystem` preserves the deterministic-system conditions by prefix-closed restriction.
`HasDomain.cutSystem` gives its exact transcript-dependent domain, `cutDomain D q`.
`cutSystem_cutSystem` combines two cuts by the smaller horizon, and `cutSystem_eq_self`
recovers any system already finite at that horizon. `replies_cutSystem_iff` preserves all
completed replies within the cut, for the finite-PDS pushforward correspondence.
-/

@[expose] public section

namespace SystemAlgebra

-- `A` carries queries, `B` replies, and `s` is the partial system being restricted.
variable {A B : Type} (s : System A B)

/-- Every input history within the horizon keeps its complete original partial reply. -/
lemma cutSystem_apply_of_length_le (q : ℕ) (xs : List A) (hq : xs.length ≤ q) :
    cutSystem s q xs = s xs := by
  rw [cutSystem, filterDom, ite_eq_left hq]

/-- Every input history beyond the horizon has no reply. -/
lemma cutSystem_apply_of_bound_lt (q : ℕ) (xs : List A) (hq : q < xs.length) :
    cutSystem s q xs = Part.none := by
  rw [cutSystem, filterDom, ite_eq_right (Nat.not_le_of_lt hq)]

/-- Restriction to a finite horizon preserves silence at the root and prefix closure. -/
lemma IsDDS.cutSystem {s : System A B} (hs : IsDDS s) (q : ℕ) :
    IsDDS (SystemAlgebra.cutSystem s q) :=
  hs.filterDom _ (fun hp _ hh => hp.length_le.trans hh)

/-- The cut answers exactly the old admitted queries before its horizon. -/
lemma HasDomain.cutSystem
    -- `hs` gives the exact domain of `s`; `q` imposes the new observation horizon.
    {D : Domain A B} {s : System A B} (hs : HasDomain D s) (q : ℕ) :
    HasDomain (cutDomain D q) (SystemAlgebra.cutSystem s q) := by
  intro h x hr
  have restricted := hs.filterDom (fun xs => xs.length ≤ q) h x hr
  simpa only [SystemAlgebra.cutSystem, Domain.restrict, cutDomain, List.length_append,
    List.length_map, List.length_singleton, Nat.add_one_le_iff, and_comm] using restricted

/-- Completed replies within the horizon agree with those of the original system. -/
lemma replies_cutSystem_iff (q : ℕ) {xs : List A} {ys : List B} (hq : xs.length ≤ q) :
    Replies (cutSystem s q) xs ys ↔ Replies s xs ys :=
  replies_filterDom_iff (fun hp _ hh => hp.length_le.trans hh) s (fun _ => hq)

/-- Two successive observation cuts retain exactly the smaller horizon. -/
lemma cutSystem_cutSystem (m n : ℕ) :
    cutSystem (cutSystem s n) m = cutSystem s (min m n) := by
  rw [cutSystem, cutSystem, filterDom_filterDom]
  congr 1
  funext xs
  exact propext le_min_iff.symm

/-- A system already finite at `q` is unchanged by its `q`-cut. -/
lemma cutSystem_eq_self
    -- `hs` bounds every defined partial reply, including all input histories.
    (q : ℕ) (hs : Finite q s) : cutSystem s q = s := by
  funext xs
  by_cases hq : xs.length ≤ q
  · exact cutSystem_apply_of_length_le s q xs hq
  · rw [cutSystem_apply_of_bound_lt s q xs (Nat.lt_of_not_ge hq)]
    exact (Part.eq_none_iff'.mpr (fun hd => hq (hs xs hd))).symm

end SystemAlgebra
