import Rendering.Instances
import ConstructiveCryptography.Substitution.Quantitative

/-!
# Proof views for merged CC APIs

These optional registrations read the existing implication and H-coefficient witnesses.
An implication specifies uses of premises, not their validity. Only the registered theorems
supply conclusions and, where applicable, per-position errors and premises. No technique is
inferred from a declaration's name, and no pending upstream API is assumed.
-/

namespace CCWidget
open Lean Elab Command

run_cmd registerProofSchema (.chain {
  carrier := ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication
  systemsFromEnd := 2
  usesFromEnd := 0
  attach := ``ConstructiveCryptography.ResourceTheory.attach
  targetLeft :=
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.targetLeft
  targetRight :=
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.targetRight
  index := ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.index
  direction :=
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.direction
  transformation :=
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.transformation
  startEq :=
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.start_eq
  linkEq :=
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.link_eq
  endEq :=
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.end_eq
  reductions := #[
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.single,
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.append,
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.reverse,
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.map,
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.withEndpoints,
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.reindex] })

open SystemAlgebra.RandomSystem in
run_cmd registerProofSchema (.argument {
  carrier := ``HCoefficient
  title := "H-coefficient"
  parameters := #[("R", 2), ("S", 1), ("ε", 0), ("D", 3)]
  transcript? := some {
    sample := ``HCoefficient.sample
    component := ``HCoefficient.component
    presents := ``HCoefficient.presents
    revealed := ``HCoefficient.Revealed
    realReveal := ``HCoefficient.realReveal
    idealReveal := ``HCoefficient.idealReveal
    classes := ``HCoefficient.Class
    classify := ``HCoefficient.classOf
    error := ``HCoefficient.classError
    ratio := ``HCoefficient.ratio
    bound := ``HCoefficient.bound
    mixture := ``SystemAlgebra.RandomSystem.mix
    realMass := ``SystemAlgebra.RandomSystem.revealMass
    idealMass := ``SystemAlgebra.RandomSystem.kernelMass
    idealLaw := ``SystemAlgebra.RandomSystem.kernelLaw }
  groups := #[
    { label := "Sample", fields := #[
      ⟨"Ω", ``HCoefficient.Sample⟩, ⟨"μ", ``HCoefficient.sample⟩,
      ⟨"Rₖ", ``HCoefficient.component⟩, ⟨"R = mix μ Rₖ", ``HCoefficient.presents⟩,
      ⟨"Replies", ``HCoefficient.component_replies⟩] },
    { label := "Reveals", fields := #[
      ⟨"Z", ``HCoefficient.Revealed⟩, ⟨"real", ``HCoefficient.realReveal⟩,
      ⟨"ideal", ``HCoefficient.idealReveal⟩,
      ⟨"Normalization", ``HCoefficient.idealReveal_isProbDist⟩] },
    { label := "Classes", fields := #[
      ⟨"C", ``HCoefficient.Class⟩, ⟨"c(τ)", ``HCoefficient.classOf⟩,
      ⟨"η(a)", ``HCoefficient.classError⟩,
      ⟨"η(a) ≥ 0", ``HCoefficient.classError_nonneg⟩] },
    { label := "Ratio", fields := #[⟨"Ratio", ``HCoefficient.ratio⟩] },
    { label := "Bound", fields := #[⟨"Expected error", ``HCoefficient.bound⟩] }] })

run_cmd do
  registerProofBridge
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.distance_le
    2 (some 1) (some 0)
-- `substitutes` supplies premises indexed by assumption names, not by positions.
run_cmd do
  registerProofBridge
    ``ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.substitutes
    1 none (some 0) true
run_cmd registerProofBridge ``SystemAlgebra.Interface.distance_le_of_hCoefficient 0
run_cmd registerProofBridge ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le 1
run_cmd registerProofBridge ``SystemAlgebra.RandomSystem.HCoefficient.transcriptDistance_le_nnreal 1

end CCWidget
