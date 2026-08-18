/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Metric.ReductionRelaxation
import AbstractCryptography.Specification.Parallel

/-!
# Simulation-based construction (Jost, *Thesis*, §2.2.5)

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

"For most parts of this thesis we are also interested in computational
security, i.e., consider an ideal specification with an `ε`-relaxation
applied.  In short, we primarily focus on specifications of the form
`(σ𝒮)^ε`, combining those two aspects."

**Definition 2.2.12**: "Let `ℛ` and `𝒮` be arbitrary specifications, let `π` be
an arbitrary protocol for `ℛ`, `σ` an arbitrary simulator for `𝒮`, and let `ε`
be a function that maps distinguishers to a value in `[0,1]`.  Then, we define

`ℛ ⊢—π,σ,ε→_sim 𝒮 :⟺ π ℛ ⊆ (σ𝒮)^ε`,

and say that the protocol `π` constructs `𝒮` from `ℛ` within `ε` and with
respect to the simulator `σ`."

This is the shape every concrete construction statement takes, and it is the
combination that neither `AbstractCryptography.Specification.Basic`'s
`Constructs.simulator_trans` (a simulator, no relaxation) nor
`AbstractCryptography.Metric.ReductionRelaxation`'s
`Constructs.reductionRelaxation_trans`
(a relaxation, no simulator) provides on its own.

Note what is *not* required.  Composition here needs no non-expansion
hypothesis: the budget transforms of Theorem 2.2.11 absorb a converter into the
distinguisher rather than asking a bound to be preserved, so `attachBudget`
does the work that `IsNonexpandingSMul` does on the scalar track.  The one
structural input is MauRen11 Definition 16's emulation closure, which is a
field of `DistinguisherClass`.

The paper's "the set of interfaces controlled by the simulators are disjoint
from the ones controlled by the protocols" — its licence for the
composition-order invariance step `π'σ𝒮 = σπ'𝒮` — enters as the explicit
`Commute` hypothesis it is used through, exactly as in
`Constructs.simulator_trans`.
-/

namespace AbstractCryptography

open Pointwise
open scoped ENNReal

variable {Sigma Φ : Type*}

namespace DistinguisherClass

section Definition

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- Jost, *Thesis*, **Definition 2.2.12**: `ℛ ⊢—π,σ,ε→_sim 𝒮 :⟺ πℛ ⊆ (σ𝒮)^ε`. -/
def SimulationConstructs (D : DistinguisherClass Sigma Φ) (π σ : Sigma)
    (ε : D.tests → ℝ≥0∞) (R S : Specification Φ) : Prop :=
  π • R ⊆ D.reductionRelaxation ε (σ • S)

/-- Definition 2.2.12 as a construction into the relaxed ideal specification,
so that the plain calculus of `AbstractCryptography.Specification.Basic`
applies to it. -/
theorem simulationConstructs_iff (D : DistinguisherClass Sigma Φ) {π σ : Sigma}
    {ε : D.tests → ℝ≥0∞} {R S : Specification Φ} :
    D.SimulationConstructs π σ ε R S ↔ R —[π]→ D.reductionRelaxation ε (σ • S) :=
  Iff.rfl

/-- Dropping the simulator and the budget recovers the plain construction
relation: with `σ = 1` and the zero budget, `(1·𝒮)^0` is `𝒮` relaxed by
nothing, so Definition 2.2.12 refines Definition 2.2.4. -/
theorem constructs_of_simulationConstructs (D : DistinguisherClass Sigma Φ)
    {π σ : Sigma} {ε : D.tests → ℝ≥0∞} {R S : Specification Φ}
    (h : D.SimulationConstructs π σ ε R S) :
    R —[π]→ D.reductionRelaxation ε (σ • S) := h

end Definition

section Composition

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- Jost, *Thesis*, **Corollary 2.2.13.1**:

`ℛ ⊢—π,σ,ε→ 𝒮 ∧ 𝒮 ⊢—π',σ',ε'→ 𝒯 ⟹ ℛ ⊢—π'∘π, σσ', ε'_σ + ε_π'→ 𝒯`.

The paper's proof, step for step:

`π'(σ𝒮)^ε ⊆ (π'σ𝒮)^{ε_π'} = (σπ'𝒮)^{ε_π'} ⊆ (σ(σ'𝒯)^{ε'})^{ε_π'}`
`         ⊆ ((σσ'𝒯)^{ε'_σ})^{ε_π'} ⊆ (σσ'𝒯)^{ε'_σ + ε_π'}`

— Theorem 2.2.11, composition-order invariance, the assumption with
Proposition 2.2.7.2, Theorem 2.2.11 again, then Theorem 2.2.10; closed off by
`(π' ∘ π)ℛ = π'(πℛ)`. -/
theorem SimulationConstructs.trans (D : DistinguisherClass Sigma Φ)
    {π π' σ σ' : Sigma} {ε ε' : D.tests → ℝ≥0∞} {R S T : Specification Φ}
    (h : D.SimulationConstructs π σ ε R S)
    (h' : D.SimulationConstructs π' σ' ε' S T)
    (hc : ActCommute Φ π' σ) :
    D.SimulationConstructs (π' * π) (σ * σ')
      (D.attachBudget σ ε' + D.attachBudget π' ε) R T := by
  show (π' * π) • R ⊆ _
  rw [mul_smul]
  calc π' • π • R
      ⊆ π' • D.reductionRelaxation ε (σ • S) := Set.smul_set_mono h
    _ ⊆ D.reductionRelaxation (D.attachBudget π' ε) (π' • σ • S) :=
        D.smul_reductionRelaxation_subset π' ε _
    _ = D.reductionRelaxation (D.attachBudget π' ε) (σ • π' • S) := by
        rw [hc.smul_set S]
    _ ⊆ D.reductionRelaxation (D.attachBudget π' ε)
          (σ • D.reductionRelaxation ε' (σ' • T)) :=
        (D.reductionRelaxation (D.attachBudget π' ε)).mono
          (Set.smul_set_mono h')
    _ ⊆ D.reductionRelaxation (D.attachBudget π' ε)
          (D.reductionRelaxation (D.attachBudget σ ε') (σ • σ' • T)) :=
        (D.reductionRelaxation (D.attachBudget π' ε)).mono
          (D.smul_reductionRelaxation_subset σ ε' _)
    _ ⊆ D.reductionRelaxation
          (D.attachBudget σ ε' + D.attachBudget π' ε) (σ • σ' • T) :=
        D.reductionRelaxation_reductionRelaxation_subset _
    _ = D.reductionRelaxation
          (D.attachBudget σ ε' + D.attachBudget π' ε) ((σ * σ') • T) := by
        rw [mul_smul]

/-- Jost, *Thesis*, **Corollary 2.2.13.2**:
`ℛ ⊢—π,σ,ε→ 𝒮 ⟹ [ℛ,𝒯] ⊢—π,σ,ε_𝒯→ [𝒮,𝒯]`.

"`π[ℛ,𝒯] = [πℛ,𝒯] ⊆ [(σ𝒮)^ε,𝒯] ⊆ [σ𝒮,𝒯]^{ε_𝒯} = (σ[𝒮,𝒯])^{ε_𝒯}`, where the
third step follows from Theorem 2.2.11."

As in `Constructs.reductionRelaxation_par`, the paper's implicit "leave the
context alone" is the explicit neutral component: the protocol is `π ∥ 1` and
the simulator `σ ∥ 1`, which is what makes the closing equality
`σ[𝒮,𝒯] = [σ𝒮,𝒯]` an instance of MauRen11 §6.2's `SMulParClass`. -/
theorem SimulationConstructs.par [Par Φ] [Par Sigma] [SMulParClass Sigma Φ]
    (D : DistinguisherClass Sigma Φ) [D.IsClosedUnderPar]
    {π σ : Sigma} {ε : D.tests → ℝ≥0∞} {R S : Specification Φ}
    (h : D.SimulationConstructs π σ ε R S) (T : Specification Φ) :
    D.SimulationConstructs (π ∥ (1 : Sigma)) (σ ∥ (1 : Sigma))
      (D.parRightBudget T ε) (R ∥ T) (S ∥ T) := by
  have hpar : (σ ∥ (1 : Sigma)) • (S ∥ T) = (σ • S) ∥ T := by
    rw [smul_par, one_smul]
  rw [SimulationConstructs, hpar]
  intro x hx
  exact D.reductionRelaxation_par_subset ε (σ • S) T (Constructs.par_left T h hx)

end Composition

end DistinguisherClass

end AbstractCryptography
