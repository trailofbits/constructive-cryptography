module

public import RandomSystems.Cumulative.FiniteCuts.Defs

/-!
# Cumulative behaviors and their finite cuts

`IsRandomSystem.cut` places a normalized cumulative behavior on each finite observation domain.
`RandomSystem.limitMass_isRandomSystem` reconstructs a behavior from adjacent coherent cuts.
`limitMass_cut` and `cut_limitMass` show that these operations recover both presentations.
-/

@[expose] public section

namespace SystemAlgebra

open Probability

-- `D h x` specifies which next queries are admitted, with no global horizon.
variable {A B : Type} (D : List (A × B) → A → Prop)

namespace IsRandomSystem

/-- The finite cut preserves normalization on its restricted observation domain. -/
lemma cutMass
    -- `hp` normalizes cumulative masses `p`; `q` limits the number of replies.
    (p : List (A × B) → ℝ) (hp : IsRandomSystem D p) (q : ℕ) :
    IsRandomSystem (cutDomain D q) (SystemAlgebra.cutMass p q) := by
  classical
  refine ⟨by simpa only [SystemAlgebra.cutMass, List.length_nil, Nat.zero_le, ite_true] using hp.1,
    fun h => ?_, fun h x => ?_⟩
  · unfold SystemAlgebra.cutMass
    split_ifs
    · exact hp.2.1 h
    · exact le_rfl
  · by_cases hq : h.length < q
    · obtain ⟨μ, hm, hw⟩ := hp.2.2 h x
      refine ⟨μ, fun y => ?_, ?_⟩
      · simpa only [SystemAlgebra.cutMass, List.length_append, List.length_singleton,
          ite_eq_left (Nat.succ_le_of_lt hq)] using hm y
      · simpa only [cutDomain, hq, and_true, SystemAlgebra.cutMass,
          ite_eq_left (Nat.le_of_lt hq)] using hw
    · refine ⟨0, fun y => ?_, ?_⟩
      · simp only [Finsupp.zero_apply, SystemAlgebra.cutMass, List.length_append,
          List.length_singleton, ite_eq_right (by omega : ¬ h.length + 1 ≤ q)]
      · simp only [cutDomain, hq, and_false, ite_false]
        rfl

-- Finite alphabets allow each cut to use the production `RandomSystem` wrapper.
variable [Fintype A] [Fintype B]

/-- `cut D p hp q` is `cutMass p q` in the existing carrier on `cutDomain D q`. -/
noncomputable def cut
    -- `p` is the cumulative behavior, `hp` its normalization, and `q` the horizon.
    (p : List (A × B) → ℝ) (hp : IsRandomSystem D p) (q : ℕ) :
    RandomSystem A B (cutDomain D q) :=
  ⟨SystemAlgebra.cutMass p q, cutMass D p hp q⟩

/-- The cut's cumulative mass is the original mass through `q`, and zero later. -/
lemma cut_apply (p : List (A × B) → ℝ) (hp : IsRandomSystem D p)
    (q : ℕ) (h : List (A × B)) :
    cut D p hp q h = if h.length ≤ q then p h else 0 := rfl

/-- Every transcript within the horizon retains its original mass. -/
lemma cut_apply_of_length_le (p : List (A × B) → ℝ) (hp : IsRandomSystem D p)
    (q : ℕ) (h : List (A × B)) (hq : h.length ≤ q) : cut D p hp q h = p h :=
  ite_eq_left hq

/-- Adjacent cuts agree on every earlier transcript. -/
lemma cut_coherent (p : List (A × B) → ℝ) (hp : IsRandomSystem D p)
    (q : ℕ) (h : List (A × B)) (hq : h.length ≤ q) :
    cut D p hp (q + 1) h = cut D p hp q h := by
  rw [cut_apply_of_length_le D p hp _ h (hq.trans (Nat.le_succ q)),
    cut_apply_of_length_le D p hp q h hq]

/-- A transcript beyond the horizon has zero mass. -/
lemma cut_apply_of_bound_lt (p : List (A × B) → ℝ) (hp : IsRandomSystem D p)
    (q : ℕ) (h : List (A × B)) (hq : q < h.length) : cut D p hp q h = 0 :=
  ite_eq_right (Nat.not_le_of_lt hq)

/-- Agreement of every finite cut determines the complete cumulative behavior. -/
lemma cut_ext (p : List (A × B) → ℝ) (hp : IsRandomSystem D p)
    (r : List (A × B) → ℝ) (hr : IsRandomSystem D r)
    (cuts : ∀ q, cut D p hp q = cut D r hr q) : p = r := by
  funext h
  have same := congrArg (fun R => R h) (cuts h.length)
  simpa only [cut_apply_of_length_le D _ _ _ _ le_rfl] using same

end IsRandomSystem

namespace RandomSystem

variable [Fintype A] [Fintype B]

/-- Cutting a bounded system at its declared bound preserves its cumulative function. -/
lemma cut_bound_val
    -- `R` is a bounded system on `E`; its declared bound includes every possible transcript.
    {E : Domain A B} (R : RandomSystem A B E) :
    (IsRandomSystem.cut E R R.2 E.bound : List (A × B) → ℝ) = R := by
  funext h
  by_cases hh : h.length ≤ E.bound
  · exact IsRandomSystem.cut_apply_of_length_le _ _ _ _ _ hh
  · rw [IsRandomSystem.cut_apply_of_bound_lt _ _ _ _ _ (Nat.lt_of_not_ge hh)]
    exact (R.mass_eq_zero_of_bound_lt (Nat.lt_of_not_ge hh)).symm

/-- Coherent finite behaviors determine an unbounded normalized cumulative behavior. -/
theorem limitMass_isRandomSystem
    -- `R q` is the behavior through `q` queries, on the cut of the same domain `D`.
    (R : (q : ℕ) → RandomSystem A B (cutDomain D q))
    -- `coherent` says that adding one observation level preserves every earlier mass.
    (coherent : ∀ q h, h.length ≤ q → R (q + 1) h = R q h) :
    IsRandomSystem D (limitMass D R) := by
  classical
  refine ⟨(R 0).mass_nil, fun h => (R h.length).mass_nonneg h, fun h x => ?_⟩
  -- The next level supplies the next-reply law; coherence identifies its incoming mass.
  obtain ⟨μ, hm, hw⟩ := (R (h.length + 1)).2.2.2 h x
  refine ⟨μ, fun y => ?_, ?_⟩
  · change μ y = (R (h ++ [(x, y)]).length).val (h ++ [(x, y)])
    rw [List.length_append, List.length_singleton]
    exact hm y
  · simpa only [cutDomain, Nat.lt_succ_self, and_true,
      coherent h.length h le_rfl, limitMass] using hw

/-- Cutting and then reconstructing a behavior recovers every original cumulative mass. -/
lemma limitMass_cut (p : List (A × B) → ℝ) (hp : IsRandomSystem D p) :
    limitMass D (IsRandomSystem.cut D p hp) = p := by
  funext h
  exact IsRandomSystem.cut_apply_of_length_le D p hp _ h le_rfl

/-- Reconstructing a coherent family and cutting at `q` recovers its original `q`-level. -/
theorem cut_limitMass
    (R : (q : ℕ) → RandomSystem A B (cutDomain D q))
    (coherent : ∀ q h, h.length ≤ q → R (q + 1) h = R q h) (q : ℕ) :
    IsRandomSystem.cut D (limitMass D R) (limitMass_isRandomSystem D R coherent) q = R q := by
  apply RandomSystem.ext
  intro h
  change cutMass (limitMass D R) q h = R q h
  by_cases hq : h.length ≤ q
  · rw [cutMass, ite_eq_left hq]
    -- Repeated coherence makes every level above `|h|` carry the same mass.
    have stable : ∀ m, h.length ≤ m → R m h = R h.length h := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => rfl
      | succ m hm ih => exact (coherent m h hm).trans ih
    exact (stable q hq).symm
  · rw [cutMass, ite_eq_right hq]
    exact ((R q).mass_eq_zero_of_bound_lt (Nat.lt_of_not_ge hq)).symm

end RandomSystem

end SystemAlgebra
