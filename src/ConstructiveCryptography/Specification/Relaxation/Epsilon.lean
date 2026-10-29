import ConstructiveCryptography.Specification.Relaxation.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Scalar-error relaxation

The ε-relaxation is the union of closed balls around a specification.
It uses the chosen `PseudoEMetricSpace` on its carrier. Non-expansion of a
map is `LipschitzWith 1`; it supplies compatibility across measured carriers.
Error bounds are `ENNReal` and add without truncation; they are distinct from bounded test
outputs such as probabilities in `[0, 1]`.

```text
epsilonRelaxation error source = {R | ∃ center ∈ source, edist R center ≤ error}
```
-/

namespace ConstructiveCryptography.Specification

universe u v

variable
    -- `X` and `Y` are types of resources with chosen distances `edist`, zero on the diagonal,
    -- symmetric and satisfying the triangle inequality; distance `⊤` is allowed and
    -- separation is not assumed. Each distance is a parameter, not derived from a test class.
    {X : Type u} {Y : Type v} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- The closed ε-relaxation: the pointwise relaxation of a center is
`{resource | edist resource center ≤ error}`, reflexive by `edist_self`. At `error = 0` it
admits the resources at distance zero from the center, which need not be the center itself.

Liu, Definition 3.4.2 (printed p. 25): “Let d be a pseudo-metric on Φ.”
The definition is “R^{ε,d} := {S ∈ Φ | d(R,S) ≤ ε}”. Symmetry permits
the resource-center order used here. In the quotation d is `edist`, R the center and S the
admitted resource. -/
noncomputable def epsilonRelaxation
    -- `error`, the quotation's ε (epsilon), is a budget in `[0, ⊤]`. `⊤` admits every
    -- resource around any center, yet relaxing the empty specification still gives it back.
    (error : ENNReal) : Relaxation X :=
  Relaxation.ofPointwise (fun center => {resource | edist resource center ≤ error})
    (fun resource => (le_of_eq (edist_self resource)).trans bot_le)

/-- Membership is witnessed by an admitted center within the error bound:
`resource ∈ epsilonRelaxation error source` iff some `center ∈ source` has
`edist resource center ≤ error`. -/
@[simp] lemma mem_epsilonRelaxation_iff {error : ENNReal}
    {source : Specification X} {resource : X} :
    resource ∈ epsilonRelaxation error source ↔
      ∃ center ∈ source, edist resource center ≤ error :=
  Relaxation.mem_ofPointwise_iff

/-- Successive relaxations add their error bounds.

Jost, Theorem 2.2.10 (printed p. 22): “This follows directly from the triangle
inequality”. This is that calculation for any chosen pseudo-emetric. Only inclusion is
asserted. -/
theorem epsilonRelaxation_epsilonRelaxation_subset
    -- `firstError` and `secondError` budget the first and second relaxation; their sum is
    -- taken in `ENNReal`.
    (firstError secondError : ENNReal)
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
non-expanding map supplies it for this scalar specialization: the conclusion is the
`compatible` hypothesis of `Constructs.map`. -/
theorem image_epsilonRelaxation_subset
    -- `f : X → Y` replaces the quotation's converter α (alpha); `nonexpanding` says
    -- `edist (f R) (f S) ≤ edist R S`.
    {f : X → Y} (nonexpanding : LipschitzWith 1 f)
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
theorem Constructs.epsilonRelaxation
    -- `f : X → Y` is the quotation's π (pi).
    {f : X → Y}
    -- `source : Specification X` is R and `target : Specification Y` is S.
    {source : Specification X} {target : Specification Y}
    -- `construction` says `f '' source ⊆ target`; `nonexpanding` says `f` does not expand
    -- distances.
    (construction : Constructs f source target) (nonexpanding : LipschitzWith 1 f)
    -- `error` is the superscript ε, the same budget on both sides.
    (error : ENNReal) :
    Constructs f (epsilonRelaxation error source) (epsilonRelaxation error target) :=
  construction.map (Specification.epsilonRelaxation error) (Specification.epsilonRelaxation error)
    (Specification.epsilonRelaxation error).mono
    (image_epsilonRelaxation_subset nonexpanding error)

end ConstructiveCryptography.Specification
