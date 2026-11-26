module

public import RandomSystems.Cumulative.ObservationKernel
public import Probability.Occupancy

/-!
# Occupancy in adaptive observations

A selector `pick h x y` assigns an exchange to a bin, or ignores it. The count map increases
by that selected bin. Stopped histories retain their counts at later observation horizons.

`sLaw_mass_occupancy_ge_le` applies the probability occupancy bound to `sLaw_succ_eq_bindK`.
The conditional mass bound is needed only for bins already occupied, and is stated as a
cumulative extension mass divided by the positive prefix mass.
-/

@[expose] public section

noncomputable section

namespace SystemAlgebra.RandomSystem

open Probability Probability.Distribution

-- `A`, `B` carry queries and replies; `C` carries bins and need not be finite.
variable {A B : Type} {C : Type*}

/-- Select the first exchange after prefix `h`; retaining `h` makes no draw. -/
def observationDraw
    (pick : List (A × B) → A → B → Option C) (h t : List (A × B)) : Option C :=
  (t.drop h.length).head?.bind (fun p => pick h p.1 p.2)

/-- Retaining a stopped transcript contributes no entry. -/
lemma observationDraw_self (pick : List (A × B) → A → B → Option C)
    (h : List (A × B)) : observationDraw pick h h = none := by
  simp only [observationDraw, List.drop_length, List.head?_nil, Option.bind_none]

/-- Appending one exchange selects precisely its bin. -/
lemma observationDraw_snoc (pick : List (A × B) → A → B → Option C)
    (h : List (A × B)) (x : A) (y : B) :
    observationDraw pick h (h ++ [(x, y)]) = pick h x y := by
  simp only [observationDraw, List.drop_left, List.head?_cons, Option.bind_some]

variable [Fintype A] [Fintype B] {D : Domain A B}

/-- A count recurrence on possible exchanges gives the corresponding kernel update. -/
lemma observationKernel_counts
    (R : RandomSystem A B D) (σ : List B →. A) (compatible : R.Compatible σ)
    (counts : List (A × B) → C →₀ ℕ) (pick : List (A × B) → A → B → Option C)
    (h : List (A × B)) (follows : FollowsStrategy σ h) (possible : R h ≠ 0)
    (increment : ∀ x ∈ σ (h.map Prod.snd), ∀ y, R (h ++ [(x, y)]) ≠ 0 →
      counts (h ++ [(x, y)]) = (counts h).addDraw (pick h x y))
    (t : List (A × B)) (supported : t ∈ (R.observationKernel σ h).1.support) :
    counts t = (counts h).addDraw (observationDraw pick h t) := by
  classical
  by_cases active : (σ (h.map Prod.snd)).Dom
  · let x := (σ (h.map Prod.snd)).get active
    have query : x ∈ σ (h.map Prod.snd) := Part.get_mem active
    have defined : (R.conditional h x).Dom :=
      ⟨compatible h x follows possible query, possible⟩
    rw [observationKernel_eq_map R σ h query defined, ProbDist.map_val] at supported
    obtain ⟨y, hy, rfl⟩ := mem_support_fTransform _ _ supported
    rw [observationDraw_snoc]
    apply increment x query y
    have positive := Finsupp.mem_support_iff.mp hy
    rw [conditional_apply] at positive
    exact (div_ne_zero_iff.mp positive).1
  · rw [observationKernel_eq_single_of_stopped R σ h active] at supported
    have equal : t = h := (Finsupp.mem_support_single t h (1 : ℝ)).mp supported |>.1
    subst t
    rw [observationDraw_self]
    rfl

/-- A cumulative fiber cap gives the selected bin's conditional probability bound. -/
lemma observationKernel_mass_observationDraw_le
    (R : RandomSystem A B D) (σ : List B →. A) (compatible : R.Compatible σ)
    (pick : List (A × B) → A → B → Option C)
    (h : List (A × B)) (follows : FollowsStrategy σ h) (possible : R h ≠ 0)
    (b : C) {δ : ℝ} (nonnegative : 0 ≤ δ)
    (cap : ∀ x ∈ σ (h.map Prod.snd),
      (R.extensionLaw h x).mass (fun y => pick h x y = some b) ≤ δ * R h) :
    (R.observationKernel σ h).1.mass (fun t => observationDraw pick h t = some b) ≤ δ := by
  classical
  by_cases active : (σ (h.map Prod.snd)).Dom
  · let x := (σ (h.map Prod.snd)).get active
    have query : x ∈ σ (h.map Prod.snd) := Part.get_mem active
    have defined : (R.conditional h x).Dom :=
      ⟨compatible h x follows possible query, possible⟩
    rw [observationKernel_eq_map R σ h query defined, ProbDist.map_val, mass_fTransform]
    simp only [observationDraw_snoc]
    rw [conditional_mass]
    exact (div_le_iff₀ (lt_of_le_of_ne (R.mass_nonneg h) (Ne.symm possible))).mpr (cap x query)
  · rw [observationKernel_eq_single_of_stopped R σ h active]
    simpa only [ProbDist.single, mass_single, observationDraw_self, reduceCtorEq, ite_false]
      using nonnegative

/-- Within `Q` observation rounds, a bin reaches `m` entries with probability at most
`choose(Q,m) δ^(m−1)`. -/
theorem sLaw_mass_occupancy_ge_le
    (R : RandomSystem A B D) (σ : List B →. A) (compatible : R.Compatible σ)
    -- `counts h` records bin occupancies; `pick h x y` selects the next optional bin.
    (counts : List (A × B) → C →₀ ℕ) (pick : List (A × B) → A → B → Option C)
    {Q : ℕ} (initial : counts [] = 0)
    -- Count updates hold on supported observations and possible next exchanges.
    (increment : ∀ i < Q, ∀ h ∈ (R.sLaw σ i).support,
      ∀ x ∈ σ (h.map Prod.snd), ∀ y, R (h ++ [(x, y)]) ≠ 0 →
        counts (h ++ [(x, y)]) = (counts h).addDraw (pick h x y))
    -- `δ ≥ 0` bounds the conditional mass of each occupied bin's entire selection fiber.
    {δ : ℝ} (nonnegative : 0 ≤ δ)
    (atom : ∀ i < Q, ∀ h ∈ (R.sLaw σ i).support, ∀ x ∈ σ (h.map Prod.snd),
      ∀ b ∈ (counts h).support,
        (R.extensionLaw h x).mass (fun y => pick h x y = some b) ≤ δ * R h)
    -- `m ≥ 1` is the occupancy threshold; `Q` includes opportunities after early stopping.
    {m : ℕ} (positive : 0 < m) :
    (R.sLaw σ Q).mass (fun h => ∃ b, m ≤ counts h b) ≤
      (Q.choose m : ℝ) * δ ^ (m - 1) := by
  classical
  let μ i : ProbDist (List (A × B)) := ⟨R.sLaw σ i, R.sLaw_isProbDist compatible i⟩
  have histories (i : ℕ) (h : List (A × B)) (hh : h ∈ (R.sLaw σ i).support) :
      FollowsStrategy σ h ∧ R h ≠ 0 := by
    have member : h ∈ R.tSupp σ i := Finsupp.support_onFinset_subset hh
    exact ⟨(tSupp_good member).1, tSupp_possible member⟩
  apply mass_occupancy_ge_le μ (fun _ => R.observationKernel σ)
    (fun _ => counts) (fun _ => observationDraw pick)
    (fun i _ => R.sLaw_succ_eq_bindK σ compatible i) ?_ ?_ nonnegative ?_ positive
  · intro h hh
    change h ∈ (R.sLaw σ 0).support at hh
    rw [sLaw_zero] at hh
    have equal : h = [] := (Finsupp.mem_support_single h [] (1 : ℝ)).mp hh |>.1
    simpa only [equal] using initial
  · intro i hi h hh t ht
    exact observationKernel_counts R σ compatible counts pick h
      (histories i h hh).1 (histories i h hh).2 (increment i hi h hh) t ht
  · intro i hi h hh b hb
    exact observationKernel_mass_observationDraw_le R σ compatible pick h
      (histories i h hh).1 (histories i h hh).2 b nonnegative
      (fun x hx => atom i hi h hh x hx b hb)

end SystemAlgebra.RandomSystem
