import RandomSystems.Typed.Interface
import RandomSystems.Distance.Distinguisher
import Mathlib.Topology.EMetricSpace.Defs

/-! # Transcript distance on typed systems

`TypedSystem.transcriptPseudoEMetricSpace A` is the pseudo-metric
`edist R S = R.1.transcriptDistance S.1` on the cumulative behaviors `TypedSystem A`. Its three
laws follow from the characterization by compatible stopping distinguisher behaviors
(`RandomSystem.transcriptDistance_eq_iSup_behavior`), `Δ(R, S) = ⨆ d, Adv_d(R, S)`.
Zero distance is not equality: no separation is claimed. It is an explicit structure, not a
global instance; the CC instance on interfaces (`ConstructiveCryptography.InterfaceAlgebra`)
selects it as its metric.
-/

namespace SystemAlgebra.TypedSystem

/-- The transcript pseudo-metric on `A`: `edist R S = R.1.transcriptDistance S.1`.
Lanzenberger–Maurer, Definition 11, printed p. 15: “the supremum is over all compatible
(Y, X)-DDE.” Here those environments have an explicit query bound and stop; the underlying
systems are cumulative behaviors on `A.inputDomain`. -/
@[reducible] noncomputable def transcriptPseudoEMetricSpace (A : Interface) :
    PseudoEMetricSpace (TypedSystem A) where
  edist R S := R.1.transcriptDistance S.1
  -- Every advantage `|d R - d R|` is `0`, so their supremum is `0`.
  edist_self R := by
    rw [RandomSystem.transcriptDistance_eq_iSup_behavior R R]
    exact le_antisymm (iSup_le fun d => le_of_eq (d.advantage_self R)) bot_le
  -- The suprema agree term by term, since each advantage is symmetric.
  edist_comm R S := by
    rw [RandomSystem.transcriptDistance_eq_iSup_behavior R S,
      RandomSystem.transcriptDistance_eq_iSup_behavior S R]
    exact iSup_congr fun d => d.advantage_symm R S
  -- For each `d`: `Adv_d(R, T) ≤ Adv_d(R, S) + Adv_d(S, T) ≤ Δ(R, S) + Δ(S, T)`;
  -- the bound is uniform in `d`, so it bounds the supremum `Δ(R, T)`.
  edist_triangle R S T := by
    rw [RandomSystem.transcriptDistance_eq_iSup_behavior R T]
    exact iSup_le fun d => (d.advantage_triangle R S T).trans
      (add_le_add (d.advantage_le_transcriptDistance R S)
        (d.advantage_le_transcriptDistance S T))

end SystemAlgebra.TypedSystem
