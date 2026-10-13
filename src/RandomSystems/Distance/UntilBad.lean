import RandomSystems.Distance.Decision

/-!
# Identical until bad

Two random systems whose transcript probabilities both lie above a common part `g`, whole at the
empty transcript, are within the probability of leaving the common part. This file bounds that
probability step by step. A step from a possible transcript `h` by an admitted query `x` loses
`g h - ∑ y, g (h ++ [(x, y)])` of the common part; if this is at most `β h x` times the
probability of `h`, and the cost of every possible transcript, the sum of `β` over its steps, is
at most `ε`, then every compatible environment stays in the common part with probability at least
`1 - ε`. This is the union bound over the steps, proved by a potential: the cost of the steps
taken, minus the probability lost, does not decrease in expectation from one round to the next.

## Main definitions

* `transcriptCost β h`: the cost of the transcript `h`, the sum of `β` over its steps

## Main results

* `RandomSystem.one_sub_le_sum_tSupp`: a compatible environment sees the common part with
  probability at least one minus the largest cost of a possible transcript
* `RandomSystem.transcriptDistance_le_of_transcriptCost_le`: two random systems above a common
  part are within the largest cost of a possible transcript
-/

namespace SystemAlgebra

open Probability
open scoped NNReal

section Cost

variable {A B : Type}

/-- **The cost of a transcript**: the sum, over the steps of `h`, of the cost `β p x` of the
query `x` after the transcript `p` before it, `∑ₖ β (h₁ ⋯ hₖ) xₖ₊₁`. -/
def transcriptCost (β : List (A × B) → A → ℝ) : List (A × B) → ℝ
  | [] => 0
  | z :: t => β [] z.1 + transcriptCost (fun p x => β (z :: p) x) t

/-- One more step adds its cost. -/
lemma transcriptCost_snoc (β : List (A × B) → A → ℝ) (h : List (A × B)) (x : A) (y : B) :
    transcriptCost β (h ++ [(x, y)]) = transcriptCost β h + β h x := by
  -- Induction on h, for every β: peel the first step off both sides.
  induction h generalizing β with
  | nil => simp [transcriptCost]
  | cons z t ih =>
    simp only [List.cons_append, transcriptCost, ih]
    ring

end Cost

namespace RandomSystem

section Potential

variable {A B : Type} [Fintype A] [Fintype B] {D : Domain A B}

/-- **A compatible environment stays in the common part**: if `g` lies below the random system
`R` and is whole at the empty transcript, each step from a possible transcript `h` by an admitted
query `x` loses at most `β h x · R h` of `g`, and every possible transcript costs at most `ε`,
then the transcripts of a compatible strategy `σ` within `n` rounds that `R` makes possible carry
at least `1 - ε` of `g`. This is the union bound over the steps. -/
lemma one_sub_le_sum_tSupp {R : RandomSystem A B D} {σ : List B →. A} (hC : R.Compatible σ)
    {g : List (A × B) → ℝ} (hg : ∀ h, g h ≤ R h) (hnil : g [] = 1)
    {β : List (A × B) → A → ℝ}
    (hloss : ∀ h x, R h ≠ 0 → D h x → g h - ∑ y, g (h ++ [(x, y)]) ≤ β h x * R h) {ε : ℝ}
    (hcost : ∀ h, R h ≠ 0 → transcriptCost β h ≤ ε) (n : ℕ) :
    1 - ε ≤ ∑ h ∈ tSupp R σ n, g h := by
  -- Plan. Write c(h) for the cost of h.
  -- 1. The potential of a transcript is Φ(h) = c(h)·R(h) − (R(h) − g(h)): the cost of the steps
  --    taken, minus the probability lost from g.
  -- 2. One step does not decrease it in total: for a possible h and an admitted query x,
  --    Φ(h) ≤ Σ_y Φ(h, x, y) over the possible replies y.
  -- 3. Round by round, Φ([]) ≤ Σ_h Φ(h) over the transcripts h of σ within n rounds.
  -- 4. Φ([]) = 0, c(h) ≤ ε and Σ_h R(h) = 1, so 0 ≤ ε − 1 + Σ_h g(h).
  classical
  set Φ : List (A × B) → ℝ := fun h => transcriptCost β h * R h - (R h - g h) with hΦ
  -- Step 2.
  have step : ∀ h x, R h ≠ 0 → D h x →
      Φ h ≤ ∑ y ∈ (R.extensionLaw h x).support, Φ (h ++ [(x, y)]) := by
    intro h x hp hx
    -- The possible replies to x weigh R(h).
    have hR := R.sum_extension h x hx
    -- Off the possible replies, g ≤ R = 0; so the possible replies carry at least Σ_y g(h, x, y).
    have hoff : ∑ y ∈ Finset.univ \ (R.extensionLaw h x).support, g (h ++ [(x, y)]) ≤ 0 :=
      Finset.sum_nonpos fun y hy => by
        have h0 : R (h ++ [(x, y)]) = 0 := by
          have := (Finset.mem_sdiff.mp hy).2
          rwa [Finsupp.notMem_support_iff, extensionLaw_apply] at this
        exact h0 ▸ hg _
    have hsplit := Finset.sum_sdiff (f := fun y => g (h ++ [(x, y)]))
      (Finset.subset_univ (R.extensionLaw h x).support)
    -- The step costs β h x: Σ_y Φ(h, x, y) = (c(h) + β h x)·R(h) − R(h) + Σ_y g(h, x, y).
    have e : ∑ y ∈ (R.extensionLaw h x).support, Φ (h ++ [(x, y)]) =
        (transcriptCost β h + β h x) * R h - R h +
          ∑ y ∈ (R.extensionLaw h x).support, g (h ++ [(x, y)]) := by
      simp only [hΦ, transcriptCost_snoc]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hR]
      ring
    -- With the loss g(h) − Σ_y g(h, x, y) ≤ β h x · R(h), this is at least Φ(h).
    rw [e, hΦ]
    linarith [hloss h x hp hx]
  -- Step 3.
  have grow : ∀ m, Φ [] ≤ ∑ h ∈ tSupp R σ m, Φ h := by
    intro m
    induction m with
    | zero => simp [tSupp]
    | succ m ih =>
      -- One more round: each transcript of σ within m rounds is extended by the possible
      -- replies to the next query of σ, admitted by compatibility, or kept if σ has stopped.
      rw [sum_tSupp_succ]
      refine ih.trans (Finset.sum_le_sum fun h hh => ?_)
      split_ifs with hd
      · exact step h _ (tSupp_possible hh)
          (hC h _ (tSupp_good hh).1 (tSupp_possible hh) (Part.get_mem hd))
      · exact le_rfl
  -- Step 4. Φ([]) = 0·1 − (1 − 1) = 0.
  have hΦnil : Φ [] = 0 := by simp [hΦ, transcriptCost, R.mass_nil, hnil]
  -- The transcript law of σ has weight one.
  have hone : ∑ h ∈ tSupp R σ n, R h = 1 := by
    rw [← sum_tSupp hC n]
    exact Finset.sum_congr rfl fun h hh => (if_pos (tSupp_good hh)).symm
  -- Σ_h c(h)·R(h) ≤ ε·Σ_h R(h) = ε.
  have hcR : ∑ h ∈ tSupp R σ n, transcriptCost β h * R h ≤ ε := by
    calc ∑ h ∈ tSupp R σ n, transcriptCost β h * R h ≤ ∑ h ∈ tSupp R σ n, ε * R h :=
          Finset.sum_le_sum fun h hh =>
            mul_le_mul_of_nonneg_right (hcost h (tSupp_possible hh)) (R.mass_nonneg h)
      _ = ε := by rw [← Finset.mul_sum, hone, mul_one]
  have hgrow := grow n
  rw [hΦnil, hΦ, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hgrow
  linarith

end Potential

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

/-- **Random systems identical until bad are within the cost of their steps**: if `g` lies below
the random systems `R₁` and `R₂` and is whole at the empty transcript, each step of `R₁` from a
possible transcript `h` by an admitted query `x` loses at most `β h x · R₁ h` of `g`, and every
possible transcript of `R₁` costs at most `ε`, then `R₁` is within `ε` of `R₂`. A bound `β x`
per query is the case `β h x = β x`, in which the cost of a transcript is the sum of the costs of
its queries. -/
theorem transcriptDistance_le_of_transcriptCost_le
    {R₁ R₂ : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟} (hR₁ : R₁.RepliesAtQueriedInterface)
    {g : List ((Σ i, X i) × (Σ i, Y i)) → ℝ} (hg₁ : ∀ h, g h ≤ R₁ h) (hg₂ : ∀ h, g h ≤ R₂ h)
    (hnil : g [] = 1) {β : List ((Σ i, X i) × (Σ i, Y i)) → (Σ i, X i) → ℝ}
    (hloss : ∀ h x, R₁ h ≠ 0 → 𝒟 h x → g h - ∑ y, g (h ++ [(x, y)]) ≤ β h x * R₁ h)
    {ε : ℝ≥0} (hcost : ∀ h, R₁ h ≠ 0 → transcriptCost β h ≤ ε) :
    R₁.transcriptDistance R₂ ≤ ε := by
  -- Plan. Under an environment E compatible with the domain, bounded to n queries:
  --
  --   E ──x──▶ R₁        E ──x──▶ R₂
  --     ◀──y──             ◀──y──
  --
  -- the transcript laws μ₁ and μ₂ both lie above ν, the part of g on the transcripts of E
  -- within n rounds that R₁ makes possible, and μ₁ has weight one. So
  --   δ(μ₁, μ₂) = μ₁(P) − μ₂(P)        (P: the transcripts more likely under R₁)
  --             ≤ 1 − |ν|              (Distribution.mass_sub_mass_le_of_le)
  --             ≤ ε                    (one_sub_le_sum_tSupp).
  classical
  refine transcriptDistance_le fun E n _ hc => ?_
  have hC := hc R₁ hR₁
  -- ν: g on the transcripts of E within n rounds that R₁ makes possible.
  let ν : Distribution (List ((Σ i, X i) × (Σ i, Y i))) :=
    Finsupp.onFinset (tSupp R₁ E.1 n) (fun h => if h ∈ tSupp R₁ E.1 n then g h else 0)
      fun h hh => by
        by_contra hn
        exact hh (if_neg hn)
  have hν : ∀ h, ν h = if h ∈ tSupp R₁ E.1 n then g h else 0 := fun _ => Finsupp.onFinset_apply
  -- ν lies below both transcript laws: on its transcripts both laws are the systems'
  -- probabilities, and elsewhere ν is zero.
  have below : ∀ R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟, (∀ h, g h ≤ R h) →
      ∀ h, ν h ≤ R.sLaw E.1 n h := by
    intro R hgR h
    rw [hν]
    split_ifs with hh
    · rw [sLaw_apply, if_pos (tSupp_good hh)]
      exact hgR h
    · exact sLaw_nonNeg n h
  -- |ν| ≥ 1 − ε, by the potential argument.
  have hw : 1 - (ε : ℝ) ≤ ν.weight := by
    rw [Distribution.weight_eq_sum_of_support_subset ν Finsupp.support_onFinset_subset]
    refine (one_sub_le_sum_tSupp hC hg₁ hnil hloss hcost n).trans_eq
      (Finset.sum_congr rfl fun h hh => ?_)
    rw [hν, if_pos hh]
  -- δ(μ₁, μ₂) = μ₁(P) − μ₂(P) ≤ 1 − |ν| ≤ ε.
  rw [statDist_eq_mass_sub_mass_pos]
  linarith [Distribution.mass_sub_mass_le_of_le (R₁.sLaw_isProbDist hC n).2 (below R₁ hg₁)
    (below R₂ hg₂) fun h => R₂.sLaw E.1 n h < R₁.sLaw E.1 n h]

end RandomSystem

end SystemAlgebra
