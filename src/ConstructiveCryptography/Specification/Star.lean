import ConstructiveCryptography.Specification.Action
import ConstructiveCryptography.Specification.Relaxation.Closure
import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Converter-class closure

`star Γ S` is the image of `S` under converters in the chosen submonoid `Γ`.
The identity gives extensivity and multiplication gives idempotence.
`starClosure Γ` packages the same operation as a Mathlib `ClosureOperator`.
Maps commuting with the admitted action preserve exact construction between
star-closed specifications, by `image_star_subset` and `Constructs.star`.
The simulator rules establish membership in the target closure from an explicit
equation; the constructing map may start from a different carrier. Γ (Gamma) below is the
`converters` argument, MR16's Σ (Sigma).

```text
S ⊆ star Γ S                          (subset_star, using 1 ∈ Γ)
star Γ (star Γ S) = star Γ S          (star_idem, using Γ * Γ ⊆ Γ)
∃ σ ∈ Γ, f real = σ • ideal   ⇒   f real ∈ star Γ {ideal}     (simulator rules)
```
-/

namespace ConstructiveCryptography.Specification

universe u v w

-- `C` is a monoid of converters acting on the type `X` of resources, as in
-- `Specification.Action`; `σ • R` attaches `σ : C` (sigma) to `R : X`.
variable {C : Type u} {X : Type v} [Monoid C] [MulAction C X]

/-- Closure under a selected class of converters:
`star converters source = {σ • R | σ ∈ converters, R ∈ source}`, the source's `R*`.

MR16, Section 3.4 (printed p. 8): “R* := RΣ = {Rβ | R ∈ R, β ∈ Σ}”.
The chosen action includes the attachment position; the class is explicit. Rβ is `β • R`. -/
def star
    -- `converters`, the source's Σ (Sigma), is the admitted class, e.g. simulators. As a
    -- submonoid of `C` it contains `1` and is closed under `*`; no efficiency, inverses or
    -- commutativity are assumed.
    (converters : Submonoid C)
    -- `source : Specification X` is the specification R being closed.
    (source : Specification X) : Specification X :=
  Set.image2 (· • ·) (converters : Set C) source

/-- The identity converter admits each original resource.

MR16, Equation (1) (printed p. 8): “R ⊆ R* = (R*)*”.

This is the first inclusion `R ⊆ R*`, with R `source`: each `R ∈ source` equals
`1 • R`, and `1 ∈ converters` holds for every submonoid. -/
lemma subset_star (converters : Submonoid C) (source : Specification X) :
    source ⊆ star converters source := by
  intro resource admitted
  exact ⟨1, converters.one_mem, resource, admitted, one_smul C resource⟩

/-- Closure under converters is idempotent.

MR16, Equation (1) (printed p. 8): “R ⊆ R* = (R*)*”.
Jost, Section 2.2.5 (printed pp. 23–24), uses a specified converter class;
the submonoid here supplies its identity and composition closure.

This is the equation `R* = (R*)*`. A resource `outer • (inner • R)` with both converters
admitted equals `(outer * inner) • R`, and `outer * inner ∈ converters` by closure under
multiplication; `subset_star` gives the reverse inclusion. -/
lemma star_idem (converters : Submonoid C) (source : Specification X) :
    star converters (star converters source) = star converters source := by
  apply Set.Subset.antisymm
  · -- Replace two admitted converters by their admitted product.
    rintro resource ⟨outer, outerAdmitted, _, ⟨inner, innerAdmitted,
      original, sourceAdmitted, rfl⟩, rfl⟩
    exact ⟨outer * inner, converters.mul_mem outerAdmitted innerAdmitted,
      original, sourceAdmitted, mul_smul outer inner original⟩
  · -- The identity converter gives the reverse inclusion.
    exact subset_star converters _

/-- The converter-class closure as a Mathlib closure operator on specifications ordered by
inclusion: `starClosure converters S = star converters S`, monotone in `S`, extensive by
`subset_star` and idempotent by `star_idem`. -/
def starClosure (converters : Submonoid C) : ClosureOperator (Specification X) :=
  ClosureOperator.mk' (star converters)
    (fun _ _ included => Set.image2_subset Set.Subset.rfl included)
    (subset_star converters) (fun source => (star_idem converters source).le)

/-- A commuting map carries converter-class closure into the closure of its image.

MR16, Section 3.3 (printed p. 8): “(αR)β = α(Rβ)”.
The commutation equation is required only for the admitted converters.

The conclusion is the `compatible` hypothesis of `Constructs.map` for `starClosure`. -/
lemma image_star_subset
    -- `f : X → X` is the quotation's construction α (alpha), an arbitrary endomap, not
    -- necessarily a converter attachment; members of `converters` play the role of β.
    {f : X → X} {converters : Submonoid C}
    -- `commutes` says `f (σ • R) = σ • f R` for every `σ ∈ converters` and every `R : X`.
    (commutes : ∀ converter ∈ converters, ∀ resource,
      f (converter • resource) = converter • f resource)
    (source : Specification X) :
    f '' star converters source ⊆ star converters (f '' source) := by
  -- Decompose the image and its admitted converter witness.
  rintro resource ⟨_, ⟨converter, admitted, original, sourceAdmitted, rfl⟩, rfl⟩
  -- Commute the map past that converter, retaining the same witness.
  exact ⟨converter, admitted, f original, ⟨original, sourceAdmitted, rfl⟩,
    (commutes converter admitted original).symm⟩

/-- Exact construction is compatible with converter-class closure.

MR16, Lemma 3 (printed p. 11): “R —π→ S ⟹ R* —π→ S*”.
Jost, Section 2.2.5 and Corollary 2.2.13 (printed pp. 23–24), treats
simulation-based specifications as a specialization and derives composition
from commutation and inclusion. Here the map and its commutation law are explicit:
construction at another interface, as in the source's `(αR)β = α(Rβ)`, must be supplied as such
a map `f` with its commutation law; the single action of `C` does not provide it. -/
theorem Constructs.star
    -- `f : X → X` is the quotation's π (pi); `converters` is the admitted class.
    {f : X → X} {converters : Submonoid C}
    -- `source` and `target` are the quotation's R and S, both on `X`.
    {source target : Specification X}
    -- `construction` says `f '' source ⊆ target`.
    (construction : Constructs f source target)
    -- `commutes` says `f` commutes with attaching every `σ ∈ converters`, as in
    -- `image_star_subset`.
    (commutes : ∀ converter ∈ converters, ∀ resource,
      f (converter • resource) = converter • f resource) :
    Constructs f (star converters source) (star converters target) := by
  -- Apply specification-map compatibility using monotonicity of star closure.
  exact construction.map (starClosure converters) (starClosure converters)
    (starClosure converters).monotone (image_star_subset commutes)

/-- An admitted simulator equation establishes construction into star closure.

MR16, Lemma 5, proof (printed p. 12): “Sσ ∈ SΣ = S*”. Jost, Section 2.2.5
(printed p. 23), treats simulation-based specifications as a specialization.
The constructing map may have a different source carrier.

In the quotation S is the ideal specification, here `{ideal}`, and Σ is `converters`. -/
theorem constructs_star_of_simulator
    -- `Y` is a type of real resources with no assumed structure; `f : Y → X` maps them into
    -- `X`, where converters act.
    {Y : Type w} {f : Y → X}
    -- `real : Y` is one real resource and `ideal : X` one ideal resource.
    {converters : Submonoid C} {real : Y} {ideal : X}
    -- `simulator`, the quotation's σ (sigma), is a converter; `admitted` puts it in
    -- `converters`.
    (simulator : C) (admitted : simulator ∈ converters)
    -- `equation` is an exact equality between `f real` and the simulated ideal.
    (equation : f real = simulator • ideal) :
    Constructs f {real} (star converters {ideal}) := by
  rintro resource rfl
  -- The selected simulator witnesses membership in the ideal closure.
  exact ⟨simulator, admitted, ideal, rfl, equation.symm⟩

/-- A simulator for each source resource establishes the corresponding specification.

MR16, Lemma 5, proof (printed p. 12): “Sσ ∈ SΣ = S*”.
At exact equality the same witnesses establish image inclusion. -/
theorem constructs_star_of_simulators
    -- `f : Y → X` maps real resources of type `Y`, with no assumed structure, into `X`.
    {Y : Type w} {f : Y → X}
    -- `real : Specification Y` is a set of real resources and `ideal : X` one fixed ideal resource.
    {converters : Submonoid C} {real : Specification Y} {ideal : X}
    -- `simulates`: the simulator is chosen after the resource, so different members of
    -- `real` may use different simulators in `converters`.
    (simulates : ∀ resource ∈ real, ∃ simulator ∈ converters,
      f resource = simulator • ideal) :
    Constructs f real (star converters {ideal}) := by
  intro resource sourceAdmitted
  -- Keep the simulator chosen for this particular source resource.
  obtain ⟨simulator, admitted, equation⟩ := simulates resource sourceAdmitted
  exact ⟨simulator, admitted, ideal, rfl, equation.symm⟩

end ConstructiveCryptography.Specification
