/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography
import ConstructiveCryptography.Multiparty.Basic

/-!
# Construction chains as `calc`

This non-default test is the firing evidence for the `Trans` instances of the
construction layer.  Each example below is a chain the papers write as one
calculation — JM20 Theorem 1.1 / CR18 Lemma 5.1 for the exact arrow, JM20
Corollary 1.1 for the budgeted one — and each was previously expressible only
as a nest of explicit `.trans` applications, with the composite constructor
label and the summed budget written out by the reader at every intermediate
step.

The carrier, the interface type and the converter monoid stay abstract; no
finite enumeration and no heartbeat override is used.
-/

namespace AbstractCryptography.CalcChain.Tests

universe u v w

open scoped AbstractCryptography

variable {I : Type u} {Γ : I → Type v} {Φ : Type w}
variable [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]

/-- **JM20 Theorem 1.1 / CR18 Lemma 5.1, three legs.**  Written with
`Constructs.trans` this is
`((first.trans second).trans third : _ —[π₃ * (π₂ * π₁)]→ _)`, and the reader
supplies the intermediate label `π₂ * π₁` by hand.  As a `calc` the labels are
produced by `instTransRed` and only the resource line is written. -/
example {π₁ π₂ π₃ : ∀ i, Γ i} {key insecure auth secure : Specification Φ}
    (first : key —[π₁]→ insecure) (second : insecure —[π₂]→ auth)
    (third : auth —[π₃]→ secure) :
    key —[π₃ * (π₂ * π₁)]→ secure :=
  calc key —[π₁]→ insecure := first
    _ —[π₂]→ auth := second
    _ —[π₃]→ secure := third

section Metric

variable [PseudoEMetricSpace Φ] [IsNonexpandingSMul (∀ i, Γ i) Φ]

/-- **JM20 Corollary 1.1 item 1, three legs** — the MauRen11 §1.7
secure-channel composition with one more stage.  Written with
`Constructs.epsilonRelaxation_trans` the reader carries both the composite
protocol and the partial sum `ε₁ + ε₂` through the middle step; as a `calc`
the budget is added by `instTransApproximatelyConstructs`. -/
example {π₁ π₂ π₃ : ∀ i, Γ i} {ε₁ ε₂ ε₃ : ENNReal}
    {key insecure auth secure : Specification Φ}
    (first : key —[π₁; ε₁]→ insecure) (second : insecure —[π₂; ε₂]→ auth)
    (third : auth —[π₃; ε₃]→ secure) :
    key —[π₃ * (π₂ * π₁); ε₁ + ε₂ + ε₃]→ secure :=
  calc key —[π₁; ε₁]→ insecure := first
    _ —[π₂; ε₂]→ auth := second
    _ —[π₃; ε₃]→ secure := third

/-- **MauRen16 §4.2's hybrid step** at the resource level: the triangle
inequality in ball form, chained. -/
example {ε₁ ε₂ : ENNReal} {R S T : Φ} (first : R ≈[ε₁] S) (second : S ≈[ε₂] T) :
    R ≈[ε₁ + ε₂] T :=
  calc R ≈[ε₁] S := first
    _ ≈[ε₂] T := second

end Metric

/-- **MauRen16 §4.1 Lemma 1 relativized to `Γ`**: the label is forgotten, so
the whole chain stays inside one relation and footnote 6's closure is carried
by the `Submonoid`. -/
example {Sigma : Type v} [Monoid Sigma] [MulAction Sigma Φ] {G : Submonoid Sigma}
    {R S T : Specification Φ}
    (first : R —[∈ (G : Set Sigma)]→ S) (second : S —[∈ (G : Set Sigma)]→ T) :
    R —[∈ (G : Set Sigma)]→ T :=
  calc R —[∈ (G : Set Sigma)]→ S := first
    _ —[∈ (G : Set Sigma)]→ T := second

/-- **LiuMau20 §2.2's composability** of the per-dishonest-set family. -/
example {π π' : ∀ i, Γ i} {R S T : Set I → Set Φ}
    (first : ConstructsForAll π R S) (second : ConstructsForAll π' S T) :
    ConstructsForAll (π' * π) R T :=
  calc ConstructsForAll π R S := first
    ConstructsForAll π' _ T := second

end AbstractCryptography.CalcChain.Tests
