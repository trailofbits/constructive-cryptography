/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Topology.EMetricSpace.Lipschitz
import AbstractCryptography.Algebra.Attachment
import AbstractCryptography.Algebra.Star

/-!
# Proving abstraction using local simulators (MauRen11 §7.2–7.4)

"We can now state a central theorem in our abstract theory of
cryptography which allows to prove statements of the form `Rφ ⊑ε^π Sψ`.
What is crucial is that the simulation can be performed **locally**
(rather than jointly) and, in contrast to [1], the simulation must be
ongoing, not only for the final transcript (or view)." (§7.4)

**Theorem 2.** "Let `⟨Φ, Σ, ≈⟩` be a cryptographic algebra and, for any
`i ∈ I`, let `φᵢ, ψᵢ, πᵢ, σᵢ ∈ Σ` be converters.  Then

  `∀P ⊆ I : πᴾφᴾR ≈ σ^P̄ψᴾS   ⟹   Rφ ⊑π Sψ`."

§7.2's filters: "Here `φᵢ` can be seen as a filter restricting access to
`R`.  A guaranteed choice `αᵢφᵢ ∈ Σφᵢ` is specified by the converter
`αᵢ`.  Similarly, the possible choices are those potentially (but not
guaranteed to be) available to a party behaving dishonestly.  Such a
party can be thought of as removing the filter `φᵢ` and therefore having
possibly more powerful access to `R` than an honest party."

The carrier is taken up to `≈`, so Theorem 2's hypothesis is an equation;
`filteredAt_constructs_epsilonRelaxation_of_edist_le` is the `≈ε` variant that `⊑ε^π`
needs.  The converter monoids may differ per interface (`Γ : I → Type*`);
the paper's single `Σ` is the constant-family case.
-/

open scoped ENNReal

namespace AbstractCryptography

variable {I : Type*} {Γ : I → Type*} {Φ : Type*}
  [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]

open Classical in
/-- A choice-free endpoint-pattern specification, after MauRen11 §7.2,
Definition 18, and LiuMau20 §§2.4--2.5.

`P` is the honest endpoint: `φ` is attached there, while the complementary
interfaces are closed under converter tuples from `supportedOn Pᶜ H`, so `H`
bounds the converters admitted at the dishonest endpoint.

This is not MauRen11's literal Definition 18, which retains an actual choice
domain `Aᵢ` at every interface satisfying `Σφᵢ ⊆ Aᵢ ⊆ Σ` and reasons through
complete factorizable relations; neither is represented here. -/
def filteredAt (P : Set I)
    (H : ∀ i, Submonoid (Γ i)) (φ : ∀ i, Γ i) (R : Φ) : Specification Φ :=
  (Relaxation.star (supportedOn Pᶜ H)) {patternAttach P φ • R}

open Classical in
theorem mem_filteredAt_iff {P : Set I}
    {H : ∀ i, Submonoid (Γ i)} {φ : ∀ i, Γ i} {R x : Φ} :
    x ∈ filteredAt P H φ R
      ↔ ∃ γ ∈ supportedOn Pᶜ H, γ • (patternAttach P φ • R) = x := by
  simp [filteredAt, Relaxation.mem_star_iff]

open Classical in
/-- "**Proof.** For fixed `P ⊆ I`, the equation `πᴾφᴾR ≈ σ^P̄ψᴾS` means
that `αR ≈ βS` for all `α = (α₁, …, αₙ)` and `β = (β₁, …, βₙ)` such that

  `(αᵢ, βᵢ) ∈ {(γπᵢφᵢ, γψᵢ) : γ ∈ Σ}`   if `i ∈ P`
  `(αᵢ, βᵢ) ∈ {(γ, γσᵢ) : γ ∈ Σ}`        if `i ∈ P̄`." -/
theorem filteredAt_constructs_of_eq {P : Set I}
    {H : ∀ i, Submonoid (Γ i)} {π φ ψ σ : ∀ i, Γ i} {R S : Φ}
    (hσ : ∀ i ∈ Pᶜ, σ i ∈ H i)
    (h : patternAttach P π • patternAttach P φ • R
       = patternAttach Pᶜ σ • patternAttach P ψ • S) :
    filteredAt P H φ R —[patternAttach P π]→ filteredAt P H ψ S := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ := mem_filteredAt_iff.mp hy
  refine mem_filteredAt_iff.mpr
    ⟨γ * patternAttach Pᶜ σ, mul_mem hγ (patternAttach_mem_supportedOn hσ), ?_⟩
  calc (γ * patternAttach Pᶜ σ) • (patternAttach P ψ • S)
      = γ • (patternAttach Pᶜ σ • patternAttach P ψ • S) := mul_smul ..
    _ = γ • (patternAttach P π • patternAttach P φ • R) := by rw [h]
    _ = (γ * patternAttach P π) • (patternAttach P φ • R) := (mul_smul ..).symm
    _ = (patternAttach P π * γ) • (patternAttach P φ • R) := by
        rw [(commute_patternAttach_supportedOn hγ π).eq]
    _ = patternAttach P π • (γ • (patternAttach P φ • R)) := mul_smul ..

open Classical in
/-- A choice-free endpoint-pattern analogue of MauRen11 Theorem 2.

One simulator tuple `σ` is fixed before the quantification over `P`: the same
per-interface simulator therefore serves every honesty pattern.  For each `P`,
the displayed exact equality yields the corresponding construction between
`filteredAt P` endpoints.

This is not the paper's literal conclusion `Rφ ⊑π Sψ`: actual choice domains
and the complete factorizable relation are not represented here. -/
theorem filteredAt_constructs_of_local_simulators {H : ∀ i, Submonoid (Γ i)}
    {π φ ψ σ : ∀ i, Γ i} {R S : Φ} (hσ : ∀ i, σ i ∈ H i)
    (h : ∀ P : Set I,
      patternAttach P π • patternAttach P φ • R
        = patternAttach Pᶜ σ • patternAttach P ψ • S) :
    ∀ P : Set I, filteredAt P H φ R —[patternAttach P π]→ filteredAt P H ψ S :=
  fun P => filteredAt_constructs_of_eq (fun i _ => hσ i) (h P)

open Classical in
/-- A scalar, choice-free endpoint-pattern analogue of the approximate
construction statements announced in MauRen11 §7.4.

MauRen11 Theorem 2 itself assumes exact behavioral equivalences; here one
per-pattern `edist` bound is propagated to the `ε`-ball of the ideal
`filteredAt` endpoint, using MauRen16 Definition 2's converter
non-expansion. -/
theorem filteredAt_constructs_epsilonRelaxation_of_edist_le [PseudoEMetricSpace Φ]
    [IsNonexpandingSMul (∀ i, Γ i) Φ] {P : Set I}
    {H : ∀ i, Submonoid (Γ i)} {π φ ψ σ : ∀ i, Γ i} {R S : Φ} {ε : ℝ≥0∞}
    (hσ : ∀ i ∈ Pᶜ, σ i ∈ H i)
    (h : edist (patternAttach P π • patternAttach P φ • R)
               (patternAttach Pᶜ σ • patternAttach P ψ • S) ≤ ε) :
    filteredAt P H φ R —[patternAttach P π]→ Relaxation.epsilonRelaxation ε (filteredAt P H ψ S) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨γ, hγ, rfl⟩ := mem_filteredAt_iff.mp hy
  refine Relaxation.mem_epsilonRelaxation_iff.mpr
    ⟨(γ * patternAttach Pᶜ σ) • (patternAttach P ψ • S),
     mem_filteredAt_iff.mpr
       ⟨γ * patternAttach Pᶜ σ, mul_mem hγ (patternAttach_mem_supportedOn hσ), rfl⟩, ?_⟩
  calc edist (patternAttach P π • γ • patternAttach P φ • R)
        ((γ * patternAttach Pᶜ σ) • patternAttach P ψ • S)
      = edist (γ • patternAttach P π • patternAttach P φ • R)
              (γ • patternAttach Pᶜ σ • patternAttach P ψ • S) := by
        rw [← mul_smul, (commute_patternAttach_supportedOn hγ π).eq, mul_smul, mul_smul]
    _ ≤ edist (patternAttach P π • patternAttach P φ • R)
              (patternAttach Pᶜ σ • patternAttach P ψ • S) := edist_smul_le γ _ _
    _ ≤ ε := h

end AbstractCryptography

