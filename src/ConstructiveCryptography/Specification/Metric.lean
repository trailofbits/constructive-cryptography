import ConstructiveCryptography.Specification.Parallel
import ConstructiveCryptography.Specification.Relaxation.Epsilon

/-!
# Construction within scalar error

`ConstructsWithin f source target ε` compares `f x` to an ideal element in
the target carrier. Its definition needs only that carrier's distance.
Serial composition uses non-expansion of the second map and the triangle
inequality. Parallel composition uses the supplied locality and distance laws. Budgets are
in `ENNReal`, possibly `⊤`, and add without truncation.

```text
ConstructsWithin f source target ε :
  ∀ resource ∈ source, ∃ ideal ∈ target, edist (f resource) ideal ≤ ε
```

The ideal witness may depend on the resource. Only the target carrier is measured; no
distance on `X` is used. With `[PseudoEMetricSpace Y]` this is exact construction into
`epsilonRelaxation ε target` (`constructs_epsilonRelaxation_iff`).

Serial composition (`ConstructsWithin.serial`):

```text
resource ── f ──▶ f resource  ≈ε  middleResource ∈ middle
                  g (f resource) ≈ε g middleResource       (g non-expanding)
                                   g middleResource ≈δ ideal ∈ target
          ⇒ edist (g (f resource)) ideal ≤ ε + δ           (triangle inequality)
```
-/

namespace ConstructiveCryptography.Specification

universe u v w u' v' w'

-- `X`, `Y` and `Z` are arbitrary types of resources; each declaration states which of them
-- carry a distance.
variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Every mapped source resource is within ε of an admitted target resource, the ideal chosen
per resource.

MR16, Section 2.3 (printed p. 5): “R^ε = {R′ | ∃R ∈ R : R′ ≈ε R}”.
In the quotation R is `target`, R′ is `f resource` and `≈ε` is `edist · · ≤ error` on `Y`. -/
def ConstructsWithin
    -- `EDist Y` gives only a distance function `edist : Y → Y → ENNReal`, with no laws;
    -- nothing is assumed on `X`.
    [EDist Y]
    -- `f : X → Y` is an arbitrary function, not necessarily a converter attachment.
    (f : X → Y)
    -- `source : Specification X` is the assumed specification and `target : Specification Y` the
    -- ideal specification R.
    (source : Specification X) (target : Specification Y)
    -- `error : ENNReal` is the scalar budget ε, possibly `⊤`.
    (error : ENNReal) : Prop :=
  ∀ resource ∈ source, ∃ ideal ∈ target, edist (f resource) ideal ≤ error

/-- Exact construction into ε-relaxation is scalar approximate construction, for a
pseudo-emetric on the target carrier `Y`:

```text
Constructs f source (epsilonRelaxation error target)
  ↔ ConstructsWithin f source target error
``` -/
lemma constructs_epsilonRelaxation_iff [PseudoEMetricSpace Y]
    {f : X → Y} {source : Specification X} {target : Specification Y} {error : ENNReal} :
    Constructs f source (epsilonRelaxation error target) ↔
      ConstructsWithin f source target error := by
  -- Expand only target membership into its center and distance witness.
  simp only [Constructs, Set.MapsTo, mem_epsilonRelaxation_iff, ConstructsWithin]

/-- Scalar-error bounds may be weakened: a construction within `ε` is one within every
`δ ≥ ε`, with the same ideal witnesses. -/
lemma ConstructsWithin.weaken [EDist Y] {f : X → Y}
    {source : Specification X} {target : Specification Y} {ε δ : ENNReal}
    (construction : ConstructsWithin f source target ε) (bound : ε ≤ δ) :
    ConstructsWithin f source target δ := by
  intro resource admitted
  obtain ⟨ideal, idealAdmitted, close⟩ := construction resource admitted
  exact ⟨ideal, idealAdmitted, close.trans bound⟩

/-- Serial construction adds the error bounds when the outer map is non-expanding.

MR16, Lemmas 1–2 (printed p. 11), give serial construction and compatibility
with scalar relaxation. Jost, Theorem 2.2.10 (printed p. 22), adds errors
by the triangle inequality; see the module diagram. -/
theorem ConstructsWithin.serial
    -- `Y` and `Z` have zero self-distance, symmetry and the triangle inequality; separation
    -- is not assumed, and no distance on `X` is used.
    [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    -- `f : X → Y` is the first construction and `g : Y → Z` the second, composed as `g ∘ f`.
    {f : X → Y} {g : Y → Z}
    -- `source : Specification X`, `middle : Specification Y` and `target : Specification Z` are the
    -- three stages.
    {source : Specification X} {middle : Specification Y} {target : Specification Z}
    -- ε (epsilon) and δ (delta) are the budgets of `f` and `g`; `inner` says `f` constructs
    -- `middle` from `source` within ε.
    {ε δ : ENNReal} (inner : ConstructsWithin f source middle ε)
    -- `outer` says `g` constructs `target` from `middle` within δ.
    (outer : ConstructsWithin g middle target δ)
    -- `nonexpanding` says `edist (g y) (g y') ≤ edist y y'`, so ε survives `g`.
    (nonexpanding : LipschitzWith 1 g) :
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
gives this bound for the chosen ordered parallel operation:

```text
edist (parallel x y) (parallel x' y')
  ≤ edist (parallel x y) (parallel x' y) + edist (parallel x' y) (parallel x' y')
  ≤ edist x x' + edist y y'
```

This is the `nonexpanding` hypothesis of `ConstructsWithin.parallel`. -/
lemma edist_parallel_le [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    [PseudoEMetricSpace Z]
    -- `parallel x y : Z` places `x : X` and `y : Y` side by side.
    (parallel : X → Y → Z)
    -- `leftNonexpanding`: for each fixed `y`, `x ↦ parallel x y` is non-expanding.
    (leftNonexpanding : ∀ y, LipschitzWith 1 (fun x => parallel x y))
    -- `rightNonexpanding`: for each fixed `x`, `y ↦ parallel x y` is non-expanding.
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
the supplied distance bound adds the two approximation errors. The ideal witness is
`parallel'` of the two component witnesses. -/
theorem ConstructsWithin.parallel
    -- `X'`, `Y'` and `Z'` are the left, right and combined types after construction; they
    -- carry only distance functions, no metric laws.
    {X' : Type u'} {Y' : Type v'} {Z' : Type w'}
    [EDist X'] [EDist Y'] [EDist Z']
    -- `f : X → X'` constructs left components and `g : Y → Y'` right components.
    {f : X → X'} {g : Y → Y'}
    -- `source : Specification X` and `target : Specification X'` are the left specifications.
    {source : Specification X} {target : Specification X'}
    -- `context : Specification Y` and `context' : Specification Y'` are the right specifications; ε
    -- and δ the budgets.
    {context : Specification Y} {context' : Specification Y'} {ε δ : ENNReal}
    -- `left`: `f` constructs `target` from `source` within ε.
    (left : ConstructsWithin f source target ε)
    -- `right`: `g` constructs `context'` from `context` within δ.
    (right : ConstructsWithin g context context' δ)
    -- `parallel` and `parallel'` place pairs side by side before and after construction;
    -- `combined : Z → Z'` maps combined resources, as in `Specification.Parallel`.
    (parallel : X → Y → Z) (parallel' : X' → Y' → Z') (combined : Z → Z')
    -- `locality`: `combined` on a placed pair places the components constructed by `f`, `g`.
    (locality : ∀ x y, combined (parallel x y) = parallel' (f x) (g y))
    -- `nonexpanding` bounds distances of pairs placed by `parallel'` by the sum of component
    -- distances, assumed directly; `edist_parallel_le` derives it from separate non-expansion.
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
The scalar bound uses only the supplied context distance inequality; the error stays `ε`. -/
theorem ConstructsWithin.left_context
    -- `X'` and `Z'` are the left and combined types after construction, with distances.
    {X' : Type u'} {Z' : Type w'} [EDist X'] [EDist Z']
    -- `f : X → X'` constructs left components from `source` into `target` within ε.
    {f : X → X'} {source : Specification X} {target : Specification X'} {ε : ENNReal}
    -- `construction` is the bound for `f`; `context : Specification Y` is unchanged on the right.
    (construction : ConstructsWithin f source target ε) (context : Specification Y)
    -- `parallel` and `parallel'` place pairs before and after; `parallel'` keeps `Y`.
    (parallel : X → Y → Z) (parallel' : X' → Y → Z') (combined : Z → Z')
    -- `locality`: `combined` applies `f` to the left component and keeps `y`.
    (locality : ∀ x y, combined (parallel x y) = parallel' (f x) y)
    -- `nonexpanding`: for each fixed `y`, `x ↦ parallel' x y` does not expand distances.
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
The argument order here places the context on the left. The proof swaps arguments and applies
`ConstructsWithin.left_context`. -/
theorem ConstructsWithin.right_context
    -- `Y'` and `Z'` are the right and combined types after construction, with distances.
    {Y' : Type v'} {Z' : Type w'} [EDist Y'] [EDist Z']
    -- `g : Y → Y'` constructs right components from `source` into `target` within ε.
    {g : Y → Y'} {source : Specification Y} {target : Specification Y'} {ε : ENNReal}
    -- `context : Specification X` is unchanged on the left; `construction` is the bound for `g`.
    (context : Specification X) (construction : ConstructsWithin g source target ε)
    -- `parallel` and `parallel'` place pairs before and after; `parallel'` keeps `X`.
    (parallel : X → Y → Z) (parallel' : X → Y' → Z') (combined : Z → Z')
    -- `locality`: `combined` keeps `x` and applies `g` to the right component.
    (locality : ∀ x y, combined (parallel x y) = parallel' x (g y))
    -- `nonexpanding`: for each fixed `x`, `y ↦ parallel' x y` does not expand distances.
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
attachments. By the triangle inequality, `f` and `g` differ on `real` by at most twice its
distance to `ideal`:

```text
edist (f real) (g real) ≤ edist (f real) (f ideal) + edist (g ideal) (g real)
                        ≤ edist real ideal + edist real ideal
``` -/
theorem edist_apply_le_add_of_eq {X : Type u} {Y : Type v}
    [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    -- `f g : X → Y`, e.g. attachments of two different converters; `hf` and `hg` say both
    -- are non-expanding.
    (f g : X → Y) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    -- `real ideal : X`; `equal` says `f` and `g` agree on `ideal`, nothing about `real`.
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

/-- Paper notation `source —[f; error]→ target` for
`ConstructsWithin f source target error`. -/
scoped notation:50 source " —[" f "; " error "]→ " target:51 =>
  ConstructsWithin f source target error

end ConstructiveCryptography.Specification
