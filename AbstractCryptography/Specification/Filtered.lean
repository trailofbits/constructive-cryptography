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
    (H : ∀ i, Submonoid (Γ i)) (φ : ∀ i, Γ i) (R : Φ) : Set Φ :=
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

/-!
# The two-party case (MauRen11 App. C)

"In this section we look at the special case of two parties (`n = 2`)
and where only unfiltered resources (i.e., singleton sets) `R` and `S`
are considered, i.e., where the guaranteed and the possible choice space
are both `Σ`."

"For `n = 2`, one can write the algebraic expressions involving systems
in a simple form, by considering the left and the right side of a
resource `R` as the two interfaces.  For example, if converter `α` (`β`)
is attached to the first (second) interface of `R`, then we can write
simply `αRβ` instead of `α¹β²R`." (C.1)  "Note that in the 2-party case,
a resource can also be considered as a converter (as in the expression
`SγS` below)." (C.3)

Taken literally: one monoid `M` holding resources and converters alike, with
`αRβ := α * R * β`, and the carrier up to `≈`, so the paper's `≈` is `=`.
The two interfaces are the two commuting actions of `M` (left multiplication)
and `Mᵐᵒᵖ` (right multiplication) on `M`, their commutation being Def 14 (i).

Fn. 27 marks the limit: "For `n ≥ 3` interfaces, putting the interface
index as a superscripts is necessary to maintain linear expressions for
composed systems.  An alternative would be to use formulas that are not
linear but make use of the two-dimensional plain."  At `n ≥ 3` it is
`AbstractCryptography.Algebra.Attachment`'s indexed attachment that applies.
-/

namespace AbstractCryptography.TwoParty

variable {M : Type*} [Monoid M]

/-- Eq. (5): "For a protocol `π = (π₁, π₂)` we have

  `∃σ₁, σ₂ :  π₁Rπ₂ ≈ S`
              `π₁R  ≈ Sσ₂`
              `Rπ₂  ≈ σ₁S`
              `R    ≈ σ₁Sσ₂`     `⟺  R ⊑π S`.

The direction `⟹` follows from Theorem 2." — so these are Theorem 2's
`2² = 4` patterns at `n = 2`, and the `σ₁, σ₂` are common to all four,
which is the locality.

"If the UC framework for two parties is phrased abstractly, then one
arrives at the first three equations of (5).  Since in the UC framework,
the case where both parties are corrupted is not considered, the fourth
equation is not present.  For `n ≥ 3`, the UC framework is in a strict
sense a special case since it involves only a single simulator." -/
def Abstraction (π₁ π₂ R S : M) : Prop :=
  ∃ σ₁ σ₂ : M,
    π₁ * R * π₂ = S           -- both parties honest
    ∧ π₁ * R = S * σ₂         -- right party dishonest
    ∧ R * π₂ = σ₁ * S         -- left party dishonest
    ∧ R = σ₁ * S * σ₂         -- both parties dishonest

/-- Definition 20: "A **plain communication channel** is the 2-party
resource `C` for which `αCβ = αβ` for all `α, β ∈ Σ`."

"We now consider a further special case where `R` is a communication
channel `C`, which is a neutral resource.  For example, `π₁Cπ₂ = π₁π₂`
since `C` only connects `π₁` and `π₂`." -/
def IsPlainChannel (C : M) : Prop :=
  ∀ α β : M, α * C * β = α * β

theorem isPlainChannel_one : IsPlainChannel (1 : M) := fun α β => by
  rw [mul_one]

/-- In the monoid model "a neutral resource" is literally the neutral
element. -/
theorem isPlainChannel_iff_eq_one {C : M} : IsPlainChannel C ↔ C = 1 :=
  ⟨fun h => by simpa using h 1 1, fun h => h ▸ isPlainChannel_one⟩

theorem IsPlainChannel.mul_left {C : M} (hC : IsPlainChannel C) (α : M) : α * C = α := by
  simpa using hC α 1

theorem IsPlainChannel.mul_right {C : M} (hC : IsPlainChannel C) (β : M) : C * β = β := by
  simpa using hC 1 β

/-- **Theorem 4.** "If `SγS ≉ S` for all `γ ∈ Σ`, then there exists no
protocol `π = (π₁, π₂)` such that `C ⊑π S`."

"**Proof.** `C ⊑π S` means that `π₁π₂ ≈ S` and `π₁ ≈ Sσ₂` and
`π₂ ≈ σ₁S` for some `σ₁` and `σ₂`.  Replacing `π₁` in `π₁π₂ ≈ S` using
`π₁ ≈ Sσ₂` yields `Sσ₁π₂ ≈ S`.  Now replacing `π₂` using `π₂ ≈ σ₁S`
yields `Sσ₁σ₂S ≈ S`, which contradicts `∀γ : SγS ≉ S` (one can choose
`γ = σ₁σ₂`)."

(The printed proof's subscripts slip: substituting `π₁ ≈ Sσ₂` gives
`Sσ₂π₂ ≈ S`, then `Sσ₂σ₁S ≈ S`, so the `γ` to choose is `σ₂σ₁`.  The
argument is unaffected.)

"We now prove a general impossibility result which implies, as a special
case, the impossibility of realizing universally composable commitments
from a communication channel proved originally in [5]." -/
theorem not_abstraction_plainChannel {C S : M} (hC : IsPlainChannel C)
    (h : ∀ γ : M, S * γ * S ≠ S) (π₁ π₂ : M) :
    ¬ Abstraction π₁ π₂ C S := by
  rintro ⟨σ₁, σ₂, h1, h2, h3, -⟩
  rw [hC π₁ π₂] at h1
  rw [hC.mul_left π₁] at h2
  rw [hC.mul_right π₂] at h3
  -- "one can choose `γ = σ₁σ₂`" — as `σ₂σ₁`, per the note above.
  refine h (σ₂ * σ₁) ?_
  calc S * (σ₂ * σ₁) * S = (S * σ₂) * (σ₁ * S) := by
        simp only [mul_assoc]
    _ = π₁ * π₂ := by rw [← h2, ← h3]
    _ = S := h1

section Quantitative

open scoped ENNReal

/-- Theorem 4 with `≈` read as `≈ε` throughout; the paper states Theorem 4
only for `≈`.  Under MauRen16 Definition 2's non-expansion on both sides —
"`d(αR, αS) ≤ d(R, S)` for all `α` and `d(Rβ, Sβ) ≤ d(R, S)` for all `β`" —
if every `γ` leaves `SγS` at distance at least `δ` from `S`, then any
`π₁, π₂, σ₁, σ₂` meeting the first three conditions of eq. (5) against a
plain channel within `ε₀, ε₁, ε₂` obey `δ ≤ ε₀ + ε₁ + ε₂`.

This is what Corollary 1 consumes, with `δ = 1 − 1/k`: "For the resource
`Com γ Com`, either no message is committed to in the second copy of `Com`,
or the message output at the opening phase is independent of the committed
message.  The distinguishing advantage is at least `1 − 1/k`, where `k` is
the cardinality of the message space of `Com`". -/
theorem not_abstraction_plainChannel_quantitative {M : Type*} [Monoid M]
    [PseudoEMetricSpace M]
    (hl : ∀ a : M, LipschitzWith 1 (a * ·))
    (hr : ∀ b : M, LipschitzWith 1 (· * b))
    {C S : M} (hC : IsPlainChannel C)
    {δ : ℝ≥0∞} (h : ∀ γ : M, δ ≤ edist (S * γ * S) S)
    (π₁ π₂ σ₁ σ₂ : M) {ε₀ ε₁ ε₂ : ℝ≥0∞}
    (h0 : edist (π₁ * C * π₂) S ≤ ε₀)
    (h1 : edist (π₁ * C) (S * σ₂) ≤ ε₁)
    (h2 : edist (C * π₂) (σ₁ * S) ≤ ε₂) :
    δ ≤ ε₀ + ε₁ + ε₂ := by
  rw [hC π₁ π₂] at h0
  rw [hC.mul_left π₁] at h1
  rw [hC.mul_right π₂] at h2
  have step1 : edist (π₁ * π₂) (S * σ₂ * π₂) ≤ ε₁ := by
    calc edist (π₁ * π₂) (S * σ₂ * π₂)
        ≤ 1 * edist π₁ (S * σ₂) := hr π₂ π₁ (S * σ₂)
      _ = edist π₁ (S * σ₂) := one_mul _
      _ ≤ ε₁ := h1
  have step2 : edist (S * σ₂ * π₂) (S * σ₂ * (σ₁ * S)) ≤ ε₂ := by
    calc edist (S * σ₂ * π₂) (S * σ₂ * (σ₁ * S))
        ≤ 1 * edist π₂ (σ₁ * S) := hl (S * σ₂) π₂ (σ₁ * S)
      _ = edist π₂ (σ₁ * S) := one_mul _
      _ ≤ ε₂ := h2
  have hEq : S * σ₂ * (σ₁ * S) = S * (σ₂ * σ₁) * S := by
    simp only [mul_assoc]
  calc δ ≤ edist (S * (σ₂ * σ₁) * S) S := h (σ₂ * σ₁)
    _ ≤ edist (S * (σ₂ * σ₁) * S) (π₁ * π₂) + edist (π₁ * π₂) S := edist_triangle ..
    _ ≤ (edist (S * (σ₂ * σ₁) * S) (S * σ₂ * π₂) + edist (S * σ₂ * π₂) (π₁ * π₂))
          + edist (π₁ * π₂) S := by
        gcongr
        exact edist_triangle ..
    _ ≤ (ε₂ + ε₁) + ε₀ := by
        refine add_le_add (add_le_add ?_ ?_) h0
        · rw [← hEq, edist_comm]; exact step2
        · rw [edist_comm]; exact step1
    _ = ε₀ + ε₁ + ε₂ := by ring

end Quantitative

end AbstractCryptography.TwoParty
