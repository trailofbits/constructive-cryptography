/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Metric.Epsilon

/-!
# Parameterized resources and constructions (CR18 §5.5)

CR18 §5.5 (printed p. 122): "Often, a resource `R` is parameterized by a
parameter `r`, for example the allowed number of queries, and the parameter `ǫ`
in an `ǫ`-relaxation or the function `f` in a reduction-based relaxation depend
on `r`.  The parameterized restriction of an *a priori* unbounded resource `R`
is modeled by filters `φ_r` (see Section 3.4.3)."

**Definition 5.11.** "A *parameterized* discrete single-interface resource with
parameter set `𝒵` is a family `{φ_r R}_{r∈𝒵}` of finite resources, where `R` is
a (generally infinite) resource system and `{φ_r}_{r∈𝒵}` is a parameterized
family of filter converters."

**Example 5.2.** "Recall that `[r]` is the special case of a filter restricting
access to `r` queries.  Hence `[r]R_{n,n}` is a uniform random function (URF)
parameterized by the number `r` of queries it allows."  The carrier-level `[r]`
is `RandomSystems.filterQueries` (`RandomSystems/System/FilterPhi.lean`); this
module is carrier-free and names no filter.

**Equation (5.6)**, the statement form:

  `φ_r R —^{ψ_r α}→ ψ_r S^{f_r}   ⟺   ψ_r α φ_r R ⊆ ψ_r S^{f_r}`

"The constructing converter `α` does not depend on `r`, i.e., it works for any
`r`, but `α` will be such that for each `r`, `ψ_r α φ_r = ψ_r α`, i.e., when
accessed through `ψ_r` it makes only `φ_r`-restricted access to the attached
system.  For a specific `r`, (5.6) states that if one uses a `φ_r`-restricted
version of `R` (i.e., `φ_r R`), then `α` constructs a resource that is
`f_r`-close to an `ψ_r`-restricted version of `S` (i.e., `ψ_r S`), as long as
access (of a distinguisher) is `ψ_r`-restricted."

Two things in that paragraph are the whole content of this module, and both are
visible in the definition below.  First, `π` (the paper's `α`) is a **single**
quantified converter, outside the family: one protocol serves every parameter,
which is what distinguishes Definition 5.11's statement from a family of
unrelated construction statements.  Second, the coherence equation is what
makes the parameterized statement worth making: under it the `φ_r`-restriction
of the assumed resource is free (`parameterizedConstruction_iff_of_coherence`),
so the family collapses to one statement about the unrestricted `R` read
through `ψ_r`.

Both collapses are the landed protocol-congruences applied to the composite
label — `constructs_congr_protocol` (`Specification.Basic`) in the exact form
and `approximately_constructs_congr_protocol` (`Metric.Epsilon`) in the
relaxed one.  No new relation is introduced: `ApproximatelyConstructs` is the
reducible wrapper of `Constructs` into the `ε`-ball.

## References

* [U. Maurer, *Cryptography Foundations* lecture notes][CR18], §5.5,
  Definition 5.11, Example 5.2, equation (5.6).
-/

namespace AbstractCryptography

open Pointwise
open scoped ENNReal

variable {Z Sigma Φ : Type*} [Monoid Sigma] [MulAction Sigma Φ]

section Exact

/-- Attaching a converter to a resource, or to the protocol, is the same
construction statement: the composite label carries the attachment. -/
theorem constructs_smul_singleton_iff {π α : Sigma} {R : Φ} {𝒮 : Specification Φ} :
    ({α • R} : Specification Φ) —[π]→ 𝒮 ↔ ({R} : Specification Φ) —[π * α]→ 𝒮 := by
  rw [constructs_iff, constructs_iff, ← Set.smul_set_singleton, mul_smul]

/-- **CR18 §5.5's coherence equation, as a collapse.**  "`α` will be such that
for each `r`, `ψ_r α φ_r = ψ_r α`, i.e., when accessed through `ψ_r` it makes
only `φ_r`-restricted access to the attached system."  Under that equation the
`φ`-restriction of the assumed resource costs nothing: the same protocol
constructs the same specification from the unrestricted resource. -/
theorem constructs_smul_singleton_iff_of_coherence {π φ ψ : Sigma} {R : Φ}
    {𝒮 : Specification Φ} (coherence : ψ * π * φ = ψ * π) :
    ({φ • R} : Specification Φ) —[ψ * π]→ 𝒮 ↔ ({R} : Specification Φ) —[ψ * π]→ 𝒮 :=
  constructs_smul_singleton_iff.trans (constructs_congr_protocol coherence)

end Exact

section Parameterized

variable [PseudoEMetricSpace Φ]

/-- **CR18 §5.5, equation (5.6)**: `φ_r R —^{ψ_r α}→ ψ_r S^{f_r}`, for every
parameter `r`.

Definition 5.11's parameterized resource is the family `{φ r • R}` appearing on
the left, cut from the single (generally infinite) resource `R` by the family of
filter converters `φ`; `ψ` is the family through which the distinguisher's
access is restricted, and `f` is the parameter-dependent error budget the
section's opening paragraph asks for.

`π` is the paper's `α` and is quantified **once**, outside the family: "the
constructing converter `α` does not depend on `r`, i.e., it works for any
`r`". -/
def ParameterizedConstruction (φ ψ : Z → Sigma) (π : Sigma) (f : Z → ℝ≥0∞) (R S : Φ) :
    Prop :=
  ∀ r : Z, ({φ r • R} : Specification Φ) —[ψ r * π; f r]→ ({ψ r • S} : Specification Φ)

/-- Equation (5.6)'s right-hand side, verbatim: `ψ_r α φ_r R ⊆ ψ_r S^{f_r}`.
The parameterized statement is the composite label applied to the unrestricted
resource — no relaxation, no equation on `π` is used. -/
theorem parameterizedConstruction_iff {φ ψ : Z → Sigma} {π : Sigma} {f : Z → ℝ≥0∞}
    {R S : Φ} :
    ParameterizedConstruction φ ψ π f R S ↔
      ∀ r : Z, ({R} : Specification Φ) —[ψ r * π * φ r; f r]→
        ({ψ r • S} : Specification Φ) :=
  forall_congr' fun _ => constructs_smul_singleton_iff

/-- **The coherence equation collapses the family.**  With
`ψ_r α φ_r = ψ_r α` for every `r`, equation (5.6) says exactly that the one
protocol `π` constructs the `ψ_r`-restricted `S`, to within `f_r`, from the
*unrestricted* `R` — the filters `φ_r` have dropped out of the statement, which
is what "it makes only `φ_r`-restricted access to the attached system"
buys. -/
theorem parameterizedConstruction_iff_of_coherence {φ ψ : Z → Sigma} {π : Sigma}
    {f : Z → ℝ≥0∞} {R S : Φ} (coherence : ∀ r : Z, ψ r * π * φ r = ψ r * π) :
    ParameterizedConstruction φ ψ π f R S ↔
      ∀ r : Z, ({R} : Specification Φ) —[ψ r * π; f r]→ ({ψ r • S} : Specification Φ) :=
  parameterizedConstruction_iff.trans
    (forall_congr' fun r => approximately_constructs_congr_protocol (coherence r))

/-- The collapsed form is a construction statement about the unrestricted
resource, so it composes with the landed error-budget calculus at each fixed
parameter.  Stated in the direction the section uses it: from the collapsed
statement back to equation (5.6). -/
theorem parameterizedConstruction_of_coherence {φ ψ : Z → Sigma} {π : Sigma}
    {f : Z → ℝ≥0∞} {R S : Φ} (coherence : ∀ r : Z, ψ r * π * φ r = ψ r * π)
    (h : ∀ r : Z, ({R} : Specification Φ) —[ψ r * π; f r]→
      ({ψ r • S} : Specification Φ)) :
    ParameterizedConstruction φ ψ π f R S :=
  (parameterizedConstruction_iff_of_coherence coherence).mpr h

end Parameterized

end AbstractCryptography
