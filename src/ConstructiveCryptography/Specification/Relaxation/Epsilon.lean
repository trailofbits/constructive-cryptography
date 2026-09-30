import ConstructiveCryptography.Specification.Relaxation.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Scalar-error relaxation

The ε-relaxation is the union of closed balls around a specification.
It uses the chosen `PseudoEMetricSpace` on its carrier. Non-expansion of a
map is `LipschitzWith 1`; it supplies compatibility across measured carriers.
Error bounds are `ENNReal` and add without truncation.
-/

namespace ConstructiveCryptography.Specification

universe u v

variable {X : Type u} {Y : Type v} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- The closed ε-relaxation of a resource specification.

Liu, Definition 3.4.2 (printed p. 25): “Let d be a pseudo-metric on Φ.”
The definition is “R^{ε,d} := {S ∈ Φ | d(R,S) ≤ ε}”. Symmetry permits
the resource-center order used here. The extended codomain includes infinite
budgets; no separation property is required. -/
noncomputable def epsilonRelaxation (error : ENNReal) : Relaxation X :=
  Relaxation.ofPointwise (fun center => {resource | edist resource center ≤ error})
    (fun resource => (le_of_eq (edist_self resource)).trans bot_le)

/-- Membership is witnessed by an admitted center within the error bound. -/
@[simp] theorem mem_epsilonRelaxation_iff {error : ENNReal}
    {source : Specification X} {resource : X} :
    resource ∈ epsilonRelaxation error source ↔
      ∃ center ∈ source, edist resource center ≤ error :=
  Relaxation.mem_ofPointwise_iff

/-- Successive relaxations add their error bounds.

Jost, Theorem 2.2.10 (printed p. 22): “This follows directly from the triangle
inequality”. This is that calculation for any chosen pseudo-emetric. -/
theorem epsilonRelaxation_epsilonRelaxation_subset (firstError secondError : ENNReal)
    (source : Specification X) :
    epsilonRelaxation secondError (epsilonRelaxation firstError source) ⊆
      epsilonRelaxation (firstError + secondError) source := by
  intro resource admitted
  obtain ⟨middle, middleAdmitted, close⟩ := mem_epsilonRelaxation_iff.mp admitted
  obtain ⟨center, centerAdmitted, middleClose⟩ :=
    mem_epsilonRelaxation_iff.mp middleAdmitted
  -- Join the two witnesses by the triangle inequality.
  apply mem_epsilonRelaxation_iff.mpr
  exact ⟨center, centerAdmitted, (edist_triangle resource middle center).trans
    ((add_le_add close middleClose).trans_eq (add_comm secondError firstError))⟩

/-- A non-expanding map preserves scalar-error bounds on specification images.

MR16, Definition 2 and Lemma 2 (printed p. 11): “d(αR, αS) ≤ d(R, S)”.
Jost's general relaxation calculus needs a compatibility hypothesis; the
non-expanding map supplies it for this scalar specialization. -/
theorem image_epsilonRelaxation_subset {f : X → Y} (nonexpanding : LipschitzWith 1 f)
    (error : ENNReal) (source : Specification X) :
    f '' epsilonRelaxation error source ⊆ epsilonRelaxation error (f '' source) := by
  rintro _ ⟨resource, admitted, rfl⟩
  obtain ⟨center, centerAdmitted, close⟩ := mem_epsilonRelaxation_iff.mp admitted
  -- Map the center and preserve its error bound by non-expansion.
  exact mem_epsilonRelaxation_iff.mpr ⟨f center, ⟨center, centerAdmitted, rfl⟩,
    by simpa only [ENNReal.coe_one, one_mul] using nonexpanding.edist_le_mul_of_le close⟩

/-- Relaxing both endpoints preserves construction under a non-expanding map.

MR16, Lemma 2 (printed p. 11): “R —π→ S implies R^ε —π→ S^ε”.
The proof applies also at zero error. -/
theorem Constructs.epsilonRelaxation {f : X → Y}
    {source : Specification X} {target : Specification Y}
    (construction : Constructs f source target) (nonexpanding : LipschitzWith 1 f)
    (error : ENNReal) :
    Constructs f (epsilonRelaxation error source) (epsilonRelaxation error target) :=
  construction.map (Specification.epsilonRelaxation error) (Specification.epsilonRelaxation error)
    (Specification.epsilonRelaxation error).mono
    (image_epsilonRelaxation_subset nonexpanding error)

end ConstructiveCryptography.Specification
