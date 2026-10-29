import ConstructiveCryptography.Specification.Star
import ConstructiveCryptography.Specification.Metric

/-!
# Scalar comparison and converter-class closure

Admitted converter actions preserve distance bounds when they are non-expanding.
Simulator witnesses use the distance on the target resource carrier. Notation follows
`Specification.Star` and `Specification.Metric`. Approximate simulator rule, for a fixed
`ideal`:

```text
∀ resource ∈ real, ∃ σ ∈ converters, edist (f resource) (σ • ideal) ≤ error
  ⇒ ConstructsWithin f real (star converters {ideal}) error
```

The simulator σ (sigma) is chosen after the real resource and may depend on it.
-/

namespace ConstructiveCryptography.Specification

universe u v w

variable
    -- `C` is a monoid of converters acting on the type `X` of resources by `σ • R`, as in
    -- `Specification.Star`.
    {C : Type u} {X : Type v} [Monoid C] [MulAction C X]
    -- `EDist X` gives only `edist : X → X → ENNReal`; no symmetry, triangle inequality or
    -- separation is assumed, and each result states the distance facts it uses.
    [EDist X]

/-- Non-expanding admitted actions preserve construction after star closure, within the same
`error`. For `σ • R` with `R ∈ source` and ideal witness `ideal ∈ target`,

```text
edist (f (σ • R)) (σ • ideal) = edist (σ • f R) (σ • ideal)    (commutes)
                              ≤ edist (f R) ideal ≤ error       (nonexpanding, construction)
```

MR16, Definition 2 and Lemma 3 (printed p. 11), supply non-expansion and
“R —π→ S ⟹ R* —π→ S*”. Jost, Corollary 2.2.13 (printed p. 24),
uses commutation and comparison compatibility for simulation specifications. -/
theorem ConstructsWithin.star
    -- `f : X → X` is the construction π (pi), an arbitrary endomap; `converters` is the
    -- admitted class.
    {f : X → X} {converters : Submonoid C}
    -- `source : Specification X` and `target : Specification X` are R and S; `error` is a budget,
    -- possibly `⊤`.
    {source target : Specification X} {error : ENNReal}
    -- `construction`: `f` constructs `target` from `source` within `error`.
    (construction : ConstructsWithin f source target error)
    -- `commutes` says `f (σ • R) = σ • f R` for every `σ ∈ converters` and every `R : X`.
    (commutes : ∀ converter ∈ converters, ∀ resource,
      f (converter • resource) = converter • f resource)
    -- `nonexpanding`: attaching any `σ ∈ converters` does not expand distances; converters
    -- outside the class are unconstrained.
    (nonexpanding : ∀ converter ∈ converters, ∀ R S : X,
      edist (converter • R) (converter • S) ≤ edist R S) :
    ConstructsWithin f (star converters source) (star converters target) error := by
  -- Apply the original construction to the source center.
  rintro resource ⟨converter, admitted, original, sourceAdmitted, rfl⟩
  obtain ⟨ideal, idealAdmitted, close⟩ := construction original sourceAdmitted
  -- Apply the same admitted converter to the ideal center.
  refine ⟨converter • ideal, ⟨converter, admitted, ideal, idealAdmitted, rfl⟩, ?_⟩
  -- Commutation and non-expansion preserve the original error.
  rw [commutes converter admitted original]
  exact (nonexpanding converter admitted (f original) ideal).trans close

/-- One simulator distance bound proves construction into a star-relaxed ideal.

MR16, Equation (3) (printed p. 12): “πR ≈ε Sσ”. The simulator remains
an explicit witness; no distance on the real resource carrier is required.

In the quotation `≈ε` is `edist · · ≤ error` on `X`. -/
lemma constructsWithin_star_of_simulator
    -- `f : Y → X` is the quotation's π (pi), from real resources of type `Y` with no
    -- assumed structure.
    {Y : Type w} {f : Y → X}
    -- `real : Y` is R and `ideal : X` is S; `error` is the budget ε.
    {converters : Submonoid C} {real : Y} {ideal : X} {error : ENNReal}
    -- `simulator`, the quotation's σ (sigma), lies in `converters` by `admitted`.
    (simulator : C) (admitted : simulator ∈ converters)
    -- `close` is the distance bound `πR ≈ε Sσ` on `X`.
    (close : edist (f real) (simulator • ideal) ≤ error) :
    ConstructsWithin f {real} (star converters {ideal}) error := by
  rintro resource rfl
  -- Retain the simulator witness and its supplied distance bound.
  exact ⟨simulator • ideal, ⟨simulator, admitted, ideal, rfl, rfl⟩, close⟩

/-- Pointwise simulator bounds establish the source specification.

MR16, Lemma 5, proof (printed p. 12): “Sσ ∈ SΣ = S*”.
The ideal center is fixed here and the simulator may depend on the real resource. -/
theorem constructsWithin_star_of_simulators
    -- `f : Y → X` maps real resources of type `Y`, with no assumed structure, into `X`.
    {Y : Type w} {f : Y → X}
    -- `real : Specification Y` contains the real resources; `ideal : X` is one fixed ideal.
    -- `error` is a uniform budget for every resource in `real`.
    {converters : Submonoid C} {real : Specification Y} {ideal : X} {error : ENNReal}
    -- `simulates`: the simulator in `converters` is chosen after the real resource.
    (simulates : ∀ resource ∈ real, ∃ simulator ∈ converters,
      edist (f resource) (simulator • ideal) ≤ error) :
    ConstructsWithin f real (star converters {ideal}) error := by
  intro resource sourceAdmitted
  -- Keep the simulator and bound supplied for this source resource.
  obtain ⟨simulator, admitted, close⟩ := simulates resource sourceAdmitted
  exact ⟨simulator • ideal, ⟨simulator, admitted, ideal, rfl, rfl⟩, close⟩

end ConstructiveCryptography.Specification
