module

public import ConstructiveCryptography.Instances.Algebra
public import ConstructiveCryptography.Notation.Basic
public import RandomSystems.Typed.FilterDistance

/-!
# Resource distance under an input filter

`distance_filter_le_of_ratio_and_cost` charges the original per-query loss while checking the
good-mass ratio on the admitted input histories. Both resources expose the same filtered
interface. The selected distance is the normalized transcript distance, bounded by one.
-/

@[expose] public section

namespace SystemAlgebra.Interface

open scoped SystemAlgebra NNReal

/-- Normalized transcript laws give advantage at most one on every typed interface. -/
lemma distance_le_one {A : Interface} (R S : TypedSystem A) : Δ R S ≤ 1 :=
  RandomSystem.transcriptDistance_le_one R.2 S.2

/-- A common input filter restricts the ratio hypothesis while keeping the original loss costs. -/
lemma distance_filter_le_of_ratio_and_cost {A : Interface} (R S : TypedSystem A)
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
    Δ (TypedConverter.filter A D hp • R) (TypedConverter.filter A D hp • S) ≤
      (e₁ : ENNReal) + e₂ :=
  RandomSystem.filtered_distance_le_of_ratio_and_cost R S D hp g e₁ e₂ hn hs hz ratio cost loss
    budget

end SystemAlgebra.Interface
