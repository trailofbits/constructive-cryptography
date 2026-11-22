module

public import RandomSystems.Typed.Filter
public import RandomSystems.Distance.RatioCost

/-!
# Ratio-and-cost bounds under a common filter

`filtered_distance_le_of_ratio_and_cost` compares `filter • R` and `filter • S` using a
ratio only on the filtered domain. It truncates the good submass there and applies
`transcriptDistance_le_add_of_ratio_and_transcriptCost` with the original cost function.
Prefix closure ensures every admitted next query stays in the retained histories.
-/

@[expose] public section

namespace SystemAlgebra.RandomSystem

open scoped NNReal

/-- A common input filter restricts the ratio hypothesis while keeping the original loss costs. -/
theorem filtered_distance_le_of_ratio_and_cost {A : Interface} (R S : TypedSystem A)
    -- `D` selects input histories of `A`; `hp` makes that selection prefix-closed.
    (D : List (Σ i, A.X i) → Prop) (hp : ∀ p h, p <+: h → D h → D p)
    -- `g h` is ideal good mass, whole at the empty transcript.
    (g : List ((Σ i, A.X i) × (Σ i, A.Y i)) → ℝ) (e₁ e₂ : ℝ≥0)
    (hn : ∀ h, 0 ≤ g h) (hs : ∀ h, g h ≤ S.1 h) (hz : g [] = 1)
    -- `ratio` is required only where the filtered interface admits the transcript.
    (ratio : ∀ h, Admitted (A.restrict D hp).inputDomain h →
      (1 - (e₁ : ℝ)) * g h ≤ R.1 h)
    -- `cost h x` is the original per-query loss; filtering keeps this function unchanged.
    (cost : List ((Σ i, A.X i) × (Σ i, A.Y i)) → (Σ i, A.X i) → ℝ)
    (loss : ∀ h x, S.1 h ≠ 0 → A.inputDomain h x →
      g h - ∑ y, g (h ++ [(x, y)]) ≤ cost h x * S.1 h)
    -- `budget` bounds its accumulated cost on possible ideal histories.
    (budget : ∀ h, S.1 h ≠ 0 → transcriptCost cost h ≤ e₂) :
    ((TypedConverter.filter A D hp • R).1.transcriptDistance
      (TypedConverter.filter A D hp • S).1) ≤ (e₁ : ENNReal) + e₂ := by
  classical
  let B := A.restrict D hp
  let keep := Admitted B.inputDomain
  let cut := TypedConverter.filter A D hp
  have mass (T : TypedSystem A) h : (cut • T).1 h = if keep h then T.1 h else 0 := by
    rw [TypedConverter.filter_smul]
    rfl
  -- On an admitted extension, the parent and every reply to this query survive together.
  apply transcriptDistance_le_add_of_ratio_and_transcriptCost
    (cut • R).2 (cut • S).2 (g := fun h => if keep h then g h else 0)
    (cost := cost)
  · intro h; split <;> first | exact hn h | exact le_rfl
  · intro h; rw [mass]; split <;> first | exact hs h | exact le_rfl
  · exact (ite_eq_left (admitted_nil _)).trans hz
  · intro h; rw [mass]; split <;> rename_i ha
    · exact ratio h ha
    · rw [mul_zero]
  · intro h x hpos hx
    rw [mass] at hpos ⊢
    by_cases ha : keep h
    · have ext (y : Σ i, A.Y i) : keep (h ++ [(x, y)]) := admitted_snoc.mpr ⟨ha, hx⟩
      simpa only [ite_eq_left ha, ite_eq_left (ext _)] using loss h x
        (by simpa only [ite_eq_left ha] using hpos) hx.1
    · exact (hpos (ite_eq_right ha)).elim
  · intro h hpos; apply budget; rw [mass] at hpos
    split at hpos
    · exact hpos
    · exact (hpos rfl).elim


end SystemAlgebra.RandomSystem
