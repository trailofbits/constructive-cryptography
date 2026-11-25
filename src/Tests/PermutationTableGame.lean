module

public import Commons.Definitions.PermutationTableGame
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Tests for `Commons.Definitions.PermutationTableGame`

Exercises `tableMonitorGame`, `tableMonitorGame_visible`,
`tableMonitorGame_set_mass_le_of_badEvent`, `tableMonitorGame_win_le_of_linear`,
`tableMonitorGame_dist_le_of_linear`, and the abstract distance-to-substitution law on a
finite permutation domain `Fin 8`, and verifies `cc_normalize` and `cc_calc statistical` with
CC custom notation (`Δ`, `|≡`, `•`, `≃[...]`), and audits `#print axioms`.
-/

@[expose] public section

namespace Tests.PermutationTableGame

open Commons Commons.Sponge Commons.StrongURP
open CategoryTheory SystemAlgebra Probability Probability.Distribution
open ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage
open scoped NNReal SystemAlgebra

/-- Concrete downward-closed predicate: no recorded edge lands on `0 : Fin 8`. -/
def NoZeroFresh (table : List (PermutationEdge (Fin 8))) : Prop :=
  ∀ e ∈ table, e.freshEndpoint ≠ 0

lemma noZeroFresh_nil : NoZeroFresh [] := fun _ he => by cases he

lemma noZeroFresh_mono {t₁ t₂ : List (PermutationEdge (Fin 8))}
    (hsub : ∀ e ∈ t₁, e ∈ t₂) (hg : NoZeroFresh t₂) : NoZeroFresh t₁ :=
  fun e he => hg e (hsub e he)

/-- Concrete table-monitoring game on `StrongURP (Fin 8)` with query budget `q = 3`. -/
noncomputable def noZeroGame : TypedGame (Bidirectional (Fin 8) 3) :=
  tableMonitorGame 3 NoZeroFresh noZeroFresh_mono

/-- Hiding the MBO recovers `StrongURP (Fin 8)`. -/
example : noZeroGame.visible = StrongURP (Fin 8) (q := 3) :=
  tableMonitorGame_visible 3 NoZeroFresh noZeroFresh_mono

lemma noZero_step_bad (table : List (PermutationEdge (Fin 8))) (inverse : Bool)
    (hg : NoZeroFresh table) :
    ∃ bad : Fin 8 → Prop,
      (∀ edge : PermutationEdge (Fin 8), edge.inverse = inverse →
        ¬ NoZeroFresh (table ++ [edge]) → bad edge.freshEndpoint) ∧
      (Distribution.uniform (Fin 8)).mass bad ≤ (1 / 8 : ℝ) := by
  refine ⟨fun x => x = 0, ?_, ?_⟩
  · intro edge _ hng
    by_contra hne
    apply hng
    intro e he
    rcases List.mem_append.mp he with hm | hs
    · exact hg e hm
    · rw [List.mem_singleton.mp hs]
      exact hne
  · classical
    rw [Distribution.uniform_mass_eq_card_filter, Finset.filter_eq',
      ite_eq_left (Finset.mem_univ (0 : Fin 8)), Finset.card_singleton, Nat.cast_one,
      Fintype.card_fin]
    norm_num

lemma card_fin8_gt_three : 3 < Fintype.card (Fin 8) := by
  rw [Fintype.card_fin]
  omega

/-- Direct one-step set-bit bound via `tableMonitorGame_set_mass_le_of_badEvent`. -/
example (h : List ((Σ i, (Bidirectional (Fin 8) 3).X i) × Σ i, (Bidirectional (Fin 8) 3).Y i))
    (u : Σ i, (Bidirectional (Fin 8) 3).X i)
    (hadm : (Bidirectional (Fin 8) 3).domain (h.map Prod.fst ++ [u])) :
    (∑ y, noZeroGame.1.1 (unsetMBOs h ++ [(u, tagMBO true y)])) ≤
      ((Fintype.card (Fin 8) : ℝ) / (Fintype.card (Fin 8) - 3 : ℝ)) * (1 / 8 : ℝ) *
        noZeroGame.1.1 (unsetMBOs h) :=
  tableMonitorGame_set_mass_le_of_badEvent 3 card_fin8_gt_three NoZeroFresh noZeroFresh_nil
    noZeroFresh_mono (fun _ => (1 / 8 : ℝ)) (fun _ => by norm_num) noZero_step_bad
    (fun _ _ _ => le_rfl) h u hadm

lemma noZero_linear_bad (table : List (PermutationEdge (Fin 8))) (inverse : Bool)
    (hg : NoZeroFresh table) :
    ∃ bad : Fin 8 → Prop,
      (∀ edge : PermutationEdge (Fin 8), edge.inverse = inverse →
        ¬ NoZeroFresh (table ++ [edge]) → bad edge.freshEndpoint) ∧
      (Distribution.uniform (Fin 8)).mass bad ≤
        (1 / 8 : ℝ) * (table.length + 1 : ℝ) + 0 * (table.length : ℝ) := by
  obtain ⟨bad, himpl, hmass⟩ := noZero_step_bad table inverse hg
  refine ⟨bad, himpl, hmass.trans ?_⟩
  have h1 : (1 : ℝ) ≤ (table.length + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  nlinarith

/-- Concrete winning-probability bound on `noZeroGame`. -/
example {winner : TypedGame (Bidirectional (Fin 8) 3) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners (Bidirectional (Fin 8) 3)) :
    winner noZeroGame ≤
      ((Fintype.card (Fin 8) : ℝ) / (Fintype.card (Fin 8) - 3 : ℝ)) *
        ((1 / 8 : ℝ) * (Nat.choose (3 + 1) 2 : ℝ) + 0 * (Nat.choose 3 2 : ℝ)) :=
  tableMonitorGame_win_le_of_linear 3 card_fin8_gt_three NoZeroFresh noZeroFresh_nil
    noZeroFresh_mono (1 / 8 : ℝ) 0 (by norm_num) le_rfl noZero_linear_bad hw

/-- Statistical distance, converter attachment, `cc_normalize`, and `cc_calc statistical`
compatibility under CC custom notation (`Δ`, `|≡`, `•`, `≫`). -/
example {A B : Interface} (α : A ⟶ B) (β : B ⟶ Bidirectional (Fin 8) 3)
    {T : TypedSystem (Bidirectional (Fin 8) 3)} {U : TypedSystem A} {δ : ENNReal}
    (hc : noZeroGame |≡ T) (hnext : Δ ((α ≫ β) • T) U ≤ δ) :
    Δ (α • (β • StrongURP (Fin 8) (q := 3))) U ≤
      (((Fintype.card (Fin 8) : ℝ≥0) / (Fintype.card (Fin 8) - 3 : ℕ)) *
        ((1 / 8 : ℝ≥0) * (Nat.choose (3 + 1) 2 : ℝ≥0) + 0 * (Nat.choose 3 2 : ℝ≥0)) : ℝ≥0) + δ := by
  have hnorm : α • (β • StrongURP (Fin 8) (q := 3)) =
      (α ≫ β) • StrongURP (Fin 8) (q := 3) := by
    cc_normalize
  rw [hnorm]
  have hbase := tableMonitorGame_dist_le_of_linear 3 card_fin8_gt_three NoZeroFresh noZeroFresh_nil
    noZeroFresh_mono (1 / 8 : ℝ≥0) 0 noZero_linear_bad hc
  cc_calc statistical
    (α ≫ β) • StrongURP (Fin 8) (q := 3)
      ≈[(((Fintype.card (Fin 8) : ℝ≥0) / (Fintype.card (Fin 8) - 3 : ℕ)) *
          ((1 / 8 : ℝ≥0) * (Nat.choose (3 + 1) 2 : ℝ≥0) + 0 * (Nat.choose 3 2 : ℝ≥0)) : ℝ≥0)]
        (α ≫ β) • T :=
        (ConstructiveCryptography.CryptographicAlgebra.distance_attach_le (α ≫ β) _ _).trans hbase
    _ ≈[δ] U := hnext

/-- Substitution-relation corollary (`≃[...]`) from `tableMonitorGame_dist_le_of_linear`. -/
example [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    {T : TypedSystem (Bidirectional (Fin 8) 3)} (hc : noZeroGame |≡ T) :
    StrongURP (Fin 8) (q := 3) ≃[fun _ =>
      (((Fintype.card (Fin 8) : ℝ≥0) / (Fintype.card (Fin 8) - 3 : ℕ)) *
        ((1 / 8 : ℝ≥0) * (Nat.choose (3 + 1) 2 : ℝ≥0) + 0 * (Nat.choose 3 2 : ℝ≥0)) : ℝ≥0)] T :=
  SubstitutesWithin.of_distance
    _ DominatedByDistance.advantage_le_distance
    (tableMonitorGame_dist_le_of_linear 3 card_fin8_gt_three NoZeroFresh noZeroFresh_nil
      noZeroFresh_mono (1 / 8 : ℝ≥0) 0 noZero_linear_bad hc)

#print axioms Commons.StrongURP.tableMonitorGame_visible
#print axioms Commons.StrongURP.tableMonitorGame_unsetMBOs_eq
#print axioms Commons.StrongURP.tableMonitorGame_set_mass_eq
#print axioms Commons.StrongURP.tableMonitorGame_set_mass_le_of_badEvent
#print axioms Commons.StrongURP.transcriptCost_linear_sum
#print axioms Commons.StrongURP.tableMonitorGame_win_le_of_linear
#print axioms Commons.StrongURP.tableMonitorGame_dist_le_of_linear

end Tests.PermutationTableGame
