module

public import RandomSystems.Distance.UntilBad

/-!
# Transcript ratios with accumulated loss costs

A good submass `g` lies below the ideal cumulative law `S` and starts at mass one.
If `(1 − ε) g(h) ≤ R(h)` and each query loses at most `cost h x · S(h)` of `g`,
then a transcript cost bound `δ` gives `Δ(R,S) ≤ ε + δ`.

`transcriptDistance_le_add_of_ratio_and_transcriptCost` uses the existing cost potential
`one_sub_le_sum_tSupp` to retain mass `1 − δ`. Scaling that common mass by `1 − ε`
places it below both transcript laws; their statistical distance is at most the missing mass.
-/

@[expose] public section

namespace SystemAlgebra.RandomSystem

open Probability
open scoped NNReal BigOperators

/-- A multiplicative loss `error₁` and an accumulated good-mass loss `error₂` add. -/
theorem transcriptDistance_le_add_of_ratio_and_transcriptCost
    -- `I` indexes ports with queries `X i` and replies `Y i`; `𝒟` is their common domain.
    {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}
    {R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    -- `hR`, `hS` keep replies at the queried port.
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface)
    -- `g h` is nonnegative good mass below the ideal cumulative mass `S h`.
    {g : List ((Σ i, X i) × (Σ i, Y i)) → ℝ}
    {error₁ error₂ : ℝ≥0}
    (hgn : ∀ h, 0 ≤ g h) (hg : ∀ h, g h ≤ S h) (hnil : g [] = 1)
    -- `hratio` loses at most the multiplicative factor `1 − error₁`.
    (hratio : ∀ h, (1 - (error₁ : ℝ)) * g h ≤ R h)
    -- `cost h x` pays for the good mass lost at the next query `x`.
    {cost : List ((Σ i, X i) × (Σ i, Y i)) → (Σ i, X i) → ℝ}
    (hloss : ∀ h x, S h ≠ 0 → 𝒟 h x →
      g h - ∑ y, g (h ++ [(x, y)]) ≤ cost h x * S h)
    -- `hcost` bounds the sum of these costs on every possible ideal transcript.
    (hcost : ∀ h, S h ≠ 0 → transcriptCost cost h ≤ error₂) :
    R.transcriptDistance S ≤ (error₁ : ENNReal) + error₂ := by
  classical
  by_cases he : 1 ≤ error₁
  · refine (transcriptDistance_le_one hR hS).trans ?_
    have hh : (1 : ℝ≥0) ≤ error₁ + error₂ := he.trans (le_add_of_nonneg_right error₂.2)
    exact_mod_cast hh
  have he' : 0 ≤ 1 - (error₁ : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast (lt_of_not_ge he : error₁ < 1).le)
  rw [← ENNReal.coe_add]
  apply transcriptDistance_le
  intro E n _ hc
  -- Under any compatible observer, `(1 − error₁) · g` lies below both transcript laws.
  let common : Distribution (List ((Σ i, X i) × (Σ i, Y i))) :=
    Finsupp.onFinset (tSupp S E.1 n)
      (fun h => if h ∈ tSupp S E.1 n then (1 - (error₁ : ℝ)) * g h else 0)
      (fun h hh => by
        by_contra hn
        exact hh (ite_eq_right hn))
  have hcommon (h) : common h =
      if h ∈ tSupp S E.1 n then (1 - (error₁ : ℝ)) * g h else 0 :=
    Finsupp.onFinset_apply
  have below (T : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟)
      (ht : ∀ h, (1 - (error₁ : ℝ)) * g h ≤ T h) (h) : common h ≤ T.sLaw E.1 n h := by
    rw [hcommon]
    split_ifs with hh
    · rw [sLaw_apply, ite_eq_left (tSupp_good hh)]
      exact ht h
    · exact sLaw_nonNeg n h
  have hbelowS (h) : (1 - (error₁ : ℝ)) * g h ≤ S h := by
    have hm : (1 - (error₁ : ℝ)) * g h ≤ g h := by
      calc
        _ ≤ 1 * g h := mul_le_mul_of_nonneg_right (sub_le_self 1 error₁.2) (hgn h)
        _ = _ := one_mul _
    exact hm.trans (hg h)
  -- The existing cost potential retains mass at least `1 − error₂`.
  have hw : 1 - ((error₁ + error₂ : ℝ≥0) : ℝ) ≤ common.weight := by
    rw [Distribution.weight_eq_sum_of_support_subset common Finsupp.support_onFinset_subset]
    have hs := one_sub_le_sum_tSupp (hc S hS) hg hnil hloss hcost n
    have hc' : (∑ h ∈ tSupp S E.1 n, common h) =
        (1 - (error₁ : ℝ)) * ∑ h ∈ tSupp S E.1 n, g h := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun h hh => by rw [hcommon, ite_eq_left hh])
    rw [hc']
    have hm := mul_le_mul_of_nonneg_left hs he'
    push_cast
    calc
      1 - ((error₁ : ℝ) + (error₂ : ℝ)) ≤ (1 - (error₁ : ℝ)) * (1 - (error₂ : ℝ)) := by
        rw [show (1 - (error₁ : ℝ)) * (1 - (error₂ : ℝ)) =
          1 - ((error₁ : ℝ) + (error₂ : ℝ)) + (error₁ : ℝ) * (error₂ : ℝ) by ring]
        exact le_add_of_nonneg_right (mul_nonneg error₁.2 error₂.2)
      _ ≤ _ := hm
  -- The missing common mass bounds statistical distance.
  rw [statDist_eq_mass_sub_mass_pos]
  have hbound := Distribution.mass_sub_mass_le_of_le (R.sLaw_isProbDist (hc R hR) n).2
    (below R hratio) (below S hbelowS) (fun h => S.sLaw E.1 n h < R.sLaw E.1 n h)
  exact (hbound.trans (by linarith : 1 - common.weight ≤ ((error₁ + error₂ : ℝ≥0) : ℝ)))


end SystemAlgebra.RandomSystem
