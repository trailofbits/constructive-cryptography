import ConstructiveCryptography.Specification.Parallel
import ConstructiveCryptography.Specification.Relaxation.Epsilon

/-!
# Construction within scalar error

`ConstructsWithin f source target ε` compares `f x` to an ideal element in
the target carrier. Its definition needs only that carrier's distance.
Serial composition uses non-expansion of the second map and the triangle
inequality. Parallel composition uses the supplied locality and distance laws.
-/

namespace ConstructiveCryptography.Specification

universe u v w u' v' w'

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Every mapped source resource is within ε of an admitted target resource.

MR16, Section 2.3 (printed p. 5): “R^ε = {R′ | ∃R ∈ R : R′ ≈ε R}”.
Construction into this specification compares resources in the target carrier. -/
def ConstructsWithin [EDist Y] (f : X → Y)
    (source : Specification X) (target : Specification Y) (error : ENNReal) : Prop :=
  ∀ resource ∈ source, ∃ ideal ∈ target, edist (f resource) ideal ≤ error

/-- Exact construction into ε-relaxation is scalar approximate construction. -/
theorem constructs_epsilonRelaxation_iff [PseudoEMetricSpace Y]
    {f : X → Y} {source : Specification X} {target : Specification Y} {error : ENNReal} :
    Constructs f source (epsilonRelaxation error target) ↔
      ConstructsWithin f source target error := by
  -- Expand only target membership into its center and distance witness.
  simp only [Constructs, Set.MapsTo, mem_epsilonRelaxation_iff, ConstructsWithin]

/-- Scalar-error bounds may be weakened. -/
theorem ConstructsWithin.weaken [EDist Y] {f : X → Y}
    {source : Specification X} {target : Specification Y} {ε δ : ENNReal}
    (construction : ConstructsWithin f source target ε) (bound : ε ≤ δ) :
    ConstructsWithin f source target δ := by
  intro resource admitted
  obtain ⟨ideal, idealAdmitted, close⟩ := construction resource admitted
  exact ⟨ideal, idealAdmitted, close.trans bound⟩

/-- Serial construction adds the error bounds when the outer map is non-expanding.

MR16, Lemmas 1–2 (printed p. 11), give serial construction and compatibility
with scalar relaxation. Jost, Theorem 2.2.10 (printed p. 22), adds errors
by the triangle inequality. No distance on the source carrier is used. -/
theorem ConstructsWithin.serial [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    {f : X → Y} {g : Y → Z}
    {source : Specification X} {middle : Specification Y} {target : Specification Z}
    {ε δ : ENNReal} (inner : ConstructsWithin f source middle ε)
    (outer : ConstructsWithin g middle target δ) (nonexpanding : LipschitzWith 1 g) :
    ConstructsWithin (g ∘ f) source target (ε + δ) := by
  intro resource admitted
  obtain ⟨middleResource, middleAdmitted, innerClose⟩ := inner resource admitted
  obtain ⟨ideal, idealAdmitted, outerClose⟩ := outer middleResource middleAdmitted
  refine ⟨ideal, idealAdmitted, ?_⟩
  -- Non-expansion preserves the first error after applying the outer map.
  have mappedClose : edist (g (f resource)) (g middleResource) ≤ ε := by
    simpa only [ENNReal.coe_one, one_mul] using nonexpanding.edist_le_mul_of_le innerClose
  -- The triangle inequality adds the outer error.
  exact (edist_triangle _ _ _).trans (add_le_add mappedClose outerClose)

/-- Separate non-expansion in both arguments gives an additive parallel bound.

MR16, Definition 2 (printed p. 11), expresses non-expansion of resource maps.
Applying it to the two fixed-argument maps and using the triangle inequality
gives this bound for the chosen ordered parallel operation. -/
theorem edist_parallel_le [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace Z] (parallel : X → Y → Z)
    (leftNonexpanding : ∀ y, LipschitzWith 1 (fun x => parallel x y))
    (rightNonexpanding : ∀ x, LipschitzWith 1 (parallel x))
    (x x' : X) (y y' : Y) :
    edist (parallel x y) (parallel x' y') ≤ edist x x' + edist y y' := by
  -- Change the left component, then the right component.
  apply (edist_triangle _ (parallel x' y) _).trans
  simpa only [ENNReal.coe_one, one_mul] using
    add_le_add ((leftNonexpanding y).edist_le_mul x x')
      ((rightNonexpanding x').edist_le_mul y y')

/-- Locality and the parallel distance bound compose approximate constructions.

Jost, Theorem 2.2.5.2 (printed p. 19), supplies the exact locality calculation;
the supplied distance bound adds the two approximation errors. -/
theorem ConstructsWithin.parallel
    {X' : Type u'} {Y' : Type v'} {Z' : Type w'}
    [EDist X'] [EDist Y'] [EDist Z']
    {f : X → X'} {g : Y → Y'}
    {source : Specification X} {target : Specification X'}
    {context : Specification Y} {context' : Specification Y'} {ε δ : ENNReal}
    (left : ConstructsWithin f source target ε)
    (right : ConstructsWithin g context context' δ)
    (parallel : X → Y → Z) (parallel' : X' → Y' → Z') (combined : Z → Z')
    (locality : ∀ x y, combined (parallel x y) = parallel' (f x) (g y))
    (nonexpanding : ∀ x x' y y',
      edist (parallel' x y) (parallel' x' y') ≤ edist x x' + edist y y') :
    ConstructsWithin combined (Set.image2 parallel source context)
      (Set.image2 parallel' target context') (ε + δ) := by
  rintro _ ⟨x, xAdmitted, y, yAdmitted, rfl⟩
  obtain ⟨x', x'Admitted, xClose⟩ := left x xAdmitted
  obtain ⟨y', y'Admitted, yClose⟩ := right y yAdmitted
  -- Combine the ideal witnesses using locality and the supplied distance law.
  refine ⟨parallel' x' y', ⟨x', x'Admitted, y', y'Admitted, rfl⟩, ?_⟩
  rw [locality]
  exact (nonexpanding _ _ _ _).trans (add_le_add xClose yClose)

/-- An unchanged right context preserves the error under a non-expanding context map.
Jost, Theorem 2.2.5.2 (printed p. 19): “R —π→ S ⇒ [R,T] —π→ [S,T]”.
The scalar bound uses only the supplied context distance inequality. -/
theorem ConstructsWithin.left_context
    {X' : Type u'} {Z' : Type w'} [EDist X'] [EDist Z']
    {f : X → X'} {source : Specification X} {target : Specification X'} {ε : ENNReal}
    (construction : ConstructsWithin f source target ε) (context : Specification Y)
    (parallel : X → Y → Z) (parallel' : X' → Y → Z') (combined : Z → Z')
    (locality : ∀ x y, combined (parallel x y) = parallel' (f x) y)
    (nonexpanding : ∀ x x' y, edist (parallel' x y) (parallel' x' y) ≤ edist x x') :
    ConstructsWithin combined (Set.image2 parallel source context)
      (Set.image2 parallel' target context) ε := by
  rintro _ ⟨x, admitted, y, contextAdmitted, rfl⟩
  obtain ⟨ideal, idealAdmitted, close⟩ := construction x admitted
  -- Keep the context and replace only the constructed component.
  refine ⟨parallel' ideal y, ⟨ideal, idealAdmitted, y, contextAdmitted, rfl⟩, ?_⟩
  rw [locality]
  exact (nonexpanding _ _ _).trans close

/-- An unchanged left context preserves the error with its supplied locality law.
Jost, Proposition 2.2.3 (printed p. 18): “[π_P^{γ_P} R,S] = π_P^{γ_P}[R,S]”.
The argument order here places the context on the left. -/
theorem ConstructsWithin.right_context
    {Y' : Type v'} {Z' : Type w'} [EDist Y'] [EDist Z']
    {g : Y → Y'} {source : Specification Y} {target : Specification Y'} {ε : ENNReal}
    (context : Specification X) (construction : ConstructsWithin g source target ε)
    (parallel : X → Y → Z) (parallel' : X → Y' → Z') (combined : Z → Z')
    (locality : ∀ x y, combined (parallel x y) = parallel' x (g y))
    (nonexpanding : ∀ x y y', edist (parallel' x y) (parallel' x y') ≤ edist y y') :
    ConstructsWithin combined (Set.image2 parallel context source)
      (Set.image2 parallel' context target) ε := by
  -- Exchange the arguments of the supplied functions, retaining resource order.
  rw [Set.image2_swap parallel context source, Set.image2_swap parallel' context target]
  exact construction.left_context context (fun y x => parallel x y)
      (fun y x => parallel' x y) combined (fun y x => locality x y)
      (fun y y' x => nonexpanding x y y')

/-- Two non-expanding maps agreeing on an ideal object give a two-replacement bound.

MR16, Definition 2 (printed p. 11): “d(αR, αS) ≤ d(R, S)”.
Jost, Proposition 2.2.17 (printed pp. 29–30), uses equality of ideal
attachments. The conclusion follows from these hypotheses and the triangle inequality. -/
theorem edist_apply_le_add_of_eq {X : Type u} {Y : Type v}
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (f g : X → Y) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (real ideal : X) (equal : f ideal = g ideal) :
    edist (f real) (g real) ≤ edist real ideal + edist real ideal := by
  -- Insert the common ideal output and bound each replacement separately.
  apply (edist_triangle _ (f ideal) _).trans
  have left : edist (f real) (f ideal) ≤ edist real ideal := by
    simpa only [ENNReal.coe_one, one_mul] using hf.edist_le_mul real ideal
  have right : edist (f ideal) (g real) ≤ edist real ideal := by
    rw [equal, edist_comm (g ideal) (g real)]
    simpa only [ENNReal.coe_one, one_mul] using hg.edist_le_mul real ideal
  exact add_le_add left right

/-- Paper notation for construction with a scalar error. -/
scoped notation:50 source " —[" f "; " error "]→ " target:51 =>
  ConstructsWithin f source target error

end ConstructiveCryptography.Specification
