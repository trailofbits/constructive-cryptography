/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography
import AbstractCryptography.MR11

/-!
# Selected abstract-cryptography surface smoke test

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

This non-default test checks that the public root alone composes an exact
filtered-pattern construction with its scalar metric relaxation.  The carrier
and interface type remain abstract; in particular, the test performs no finite
interface enumeration.
-/

namespace AbstractCryptography.SelectedSurface.Tests

universe u v w

variable {I : Type u} {Γ : I → Type v} {Φ : Type w}
variable [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]
variable [PseudoEMetricSpace Φ] [IsNonexpandingSMul (∀ i, Γ i) Φ]

example {pi : ∀ i, Γ i} {real ideal : Set Φ} {eps : ENNReal}
    (h : ∀ R ∈ real, ∃ S ∈ ideal, edist (pi • R) S ≤ eps) :
    real —[pi]→ Relaxation.epsilonRelaxation eps ideal :=
  constructs_epsilonRelaxation_iff.mpr h

example (D : DistinguisherClass (∀ i, Γ i) Φ) {t : Φ → ENNReal}
    (ht : t ∈ D.tests) (R S : Φ) :
    DistinguisherClass.adv t R S ≤ D.edistD R S :=
  D.adv_le_edistD ht R S

example {P : Set I} {H : ∀ i, Submonoid (Γ i)}
    {pi1 pi2 phi psi chi sigma1 sigma2 : ∀ i, Γ i} {R S T : Φ} {eps : ENNReal}
    (hsigma1 : ∀ i ∈ Pᶜ, sigma1 i ∈ H i)
    (h1 : patternAttach P pi1 • patternAttach P phi • R =
      patternAttach Pᶜ sigma1 • patternAttach P psi • S)
    (hsigma2 : ∀ i ∈ Pᶜ, sigma2 i ∈ H i)
    (h2 : edist (patternAttach P pi2 • patternAttach P psi • S)
      (patternAttach Pᶜ sigma2 • patternAttach P chi • T) ≤ eps) :
    filteredAt P H phi R
      —[patternAttach P pi2 * patternAttach P pi1]→
        Relaxation.epsilonRelaxation eps (filteredAt P H chi T) := by
  exact Constructs.trans
    (filteredAt_constructs_of_eq hsigma1 h1)
    (filteredAt_constructs_epsilonRelaxation_of_edist_le hsigma2 h2)

end AbstractCryptography.SelectedSurface.Tests
