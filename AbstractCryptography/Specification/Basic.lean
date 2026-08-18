/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Commute.Defs
import AbstractCryptography.Refinement.Basic
import AbstractCryptography.SemanticRegistry

/-!
# Specifications and constructions (JM20 §2.2, CR18 §5.2, MauRen16)

A specification is a set of resources, and the construction relation is
JM20 Definition 1 / CR18 Definition 5.4:

`Constructs π R S :⇔ π • R ⊆ S`.

The resource carrier has already absorbed behavioral equivalence, so target
membership is exact.  This is the `HasReduction (Specification Φ) Sigma` instance.

It instantiates `Refinement.Basic` with `Ω := Specification Φ` and `Γ :=` a monoid
acting on `Φ` (CR18 §5.2 takes `Γ` to be the functions `Φ → Φ`).

* A **specification** is a set `ℛ : Specification Φ` of resources.  CR18 §5.2.1,
  **Definition 5.3**: "A resource specification is a subset of `Φ`.  If
  `R ∈ Φ` satisfies `R ∈ ℛ` we say that `R` satisfies specification `ℛ`.
  For two specifications `ℛ` and `𝒮`, if `ℛ ⊆ 𝒮` we say that `ℛ` is (at
  least) as specific as `𝒮`."  And: "it is often useful to replace a
  given specification `ℛ` by a weaker specification `𝒮` if `𝒮` is easier
  to understand and analyse.  We can call `𝒮` an *abstraction* of `ℛ`."
* A **construction** is `ℛ —π→ 𝒮 :⟺ πℛ ⊆ 𝒮` (JM20 Def 1, CR18 Def 5.4),
  written with `Refinement.Basic`'s reduction notation `ℛ —[π]→ 𝒮`.
* **Composition is transitivity of `⊆`** plus the action laws (CR18
  Lemma 5.1, JM20 Theorem 1).  Per JM20 §2.2, sequential and parallel
  composition "form the equivalence of the universal composition theorem
  of the UC-framework".
* **Simulators are a proof device, not part of the definition.**  JM20
  §2.2, "The (in)existence of a simulator": "While the initial version of
  the Constructive Cryptography framework also hard-coded the existence
  of a simulator (with respect to the dummy adversary), starting from
  [18], the simulator is no longer an integral part of the construction
  notion.  Rather, employing a simulator is just one way of defining an
  ideal specification, `σ𝒮` that makes the achieved security properties
  obvious."  JM20 Proposition 2 is proved abstractly, with the paper's
  "disjoint interfaces" side condition abstracted to explicit `Commute`
  hypotheses.

JM20 §2.2 requires `π` to be a protocol *for* the assumed specification;
here `π` acts totally on one ambient carrier `Φ`, following MauRen16 §3.3's
fixed-interface, total-function specialization (fn. 3 sets aside partial
application).

The interaction between the action and `∥` is postulated by `SMulParClass`,
`(α ∥ β) • (R ∥ S) = α•R ∥ β•S`, which is MauRen11 §6.2's definition of
parallel converter composition, `(α|β)^i(R‖S) := α^iR ‖ β^iS`.

## References

* [D. Jost, U. Maurer, *Overcoming Impossibility Results in Composable
  Security using Interval-Wise Guarantees*, CRYPTO 2020][JM20], §2.2.
* [U. Maurer, *Cryptography Foundations* lecture notes][CR18], §5.2.
* [U. Maurer, R. Renner, *From Indifferentiability to Constructive
  Cryptography (and Back)*, TCC 2016-B][MauRen16].
-/

namespace AbstractCryptography

universe u v w

open Pointwise

/-- MR16 §2.3: a **specification** is a set of resources, `𝓡 ⊆ Φ`. -/
abbrev Specification (Φ : Type*) := Set Φ

variable {Sigma Φ : Type*}

section Constructs

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- JM20 §2.2, **Definition 1**: "Let `ℛ` and `𝒮` be specifications, and
let `π` be a protocol for `ℛ`.  Then, we say that `π` constructs `𝒮` from
`ℛ`, denoted `ℛ —π→ 𝒮`, if and only if `πℛ ⊆ 𝒮`, i.e.,

  `ℛ —π→ 𝒮 :⟺ πℛ ⊆ 𝒮`."

CR18 §5.2.2, **Definition 5.4**, the same notion: "A specification `𝒮`
is constructed by `γ` from specification `ℛ`, denoted `ℛ —γ→ 𝒮`, if
`γ(ℛ)` satisfies specification `𝒮`, i.e., `ℛ —γ→ 𝒮 :⟺ γ(ℛ) ⊆ 𝒮`.  `ℛ`
and `𝒮` are called the assumed and the constructed resource
specification, respectively."

`πℛ` is the pointwise image — CR18 §5.2.2: "Such functions naturally
extend to specifications: For `γ ∈ Γ` we have `γ(ℛ) = {γ(R) | R ∈ ℛ}`." -/
@[crypto_rule "ac.constructs" ac_spec_construction abstract_crypto]
def Constructs (π : Sigma) (R S : Specification Φ) : Prop := π • R ⊆ S

/-- Specifications with pointwise protocol application form a reduction in
the sense of MauRen11 Definition 6. -/
instance : HasReduction (Specification Φ) Sigma where
  Red R π S := Constructs π R S

theorem constructs_iff {π : Sigma} {R S : Specification Φ} : R —[π]→ S ↔ π • R ⊆ S := Iff.rfl

/-- Transport a construction across an equality of protocols. -/
theorem constructs_congr_protocol {π π' : Sigma} {R S : Specification Φ}
    (same : π = π') :
    (R —[π]→ S) ↔ R —[π']→ S := by
  subst π'
  rfl

theorem Constructs.mono {π : Sigma} {R R' S S' : Specification Φ} (hR : R' ⊆ R) (hS : S ⊆ S')
    (h : R —[π]→ S) : R' —[π]→ S' :=
  fun _ hx => hS (h (Set.smul_set_mono hR hx))

/-- CR18 §5.2.2, immediately after Def 5.4: "For the identity
construction `id ∈ Γ` we have

  `ℛ ⊆ 𝒮 ⟹ ℛ —id→ 𝒮`." -/
theorem constructs_one_of_subset {R S : Specification Φ} (h : R ⊆ S) : R —[(1 : Sigma)]→ S := by
  rw [constructs_iff, one_smul]
  exact h

/-- JM20 Definition 1's closing sentence writes `R —π→ S` for the
singleton-specification judgment `{R} —π→ {S}`; `⟪R⟫` is notation for
`Set.singleton`, not a second point-level construction relation. -/
scoped[AbstractCryptography] notation:max "⟪" resource "⟫" => Set.singleton resource

/-- JM20 §2.2, Definition 1's closing sentence: "In slight abuse of
notation, we write `R —π→ S` in lieu of `{R} —π→ {S}` for singleton
specifications." -/
theorem constructs_singleton_iff {π : Sigma} {R S : Φ} :
    ({R} : Specification Φ) —[π]→ ({S} : Specification Φ) ↔ π • R = S := by
  simp [constructs_iff, Set.smul_set_singleton]

/-- JM20 §2.2, **Theorem 1.1**: "Let `ℛ`, `𝒮`, and `𝒯` be arbitrary
specifications, and let `π` and `π′` be arbitrary protocols for `ℛ` and
`𝒮`, respectively.  Then, we have

  1. `ℛ —π→ 𝒮 ∧ 𝒮 —π′→ 𝒯 ⟹ ℛ —π′∘π→ 𝒯`"

"*Proof.* The first property follows directly from the transitivity of
the subset relation".

CR18 §5.2.2, **Lemma 5.1**, the same: "The construction notion of
Definition 5.4 is composable: `ℛ —γ→ 𝒮 ∧ 𝒮 —γ′→ 𝒯 ⟹ ℛ —γ′∘γ→ 𝒯`."
(Also MauRen16 §4.1 Lemma 1.)  `red_one` is CR18's identity
construction. -/
instance : IsSeriallyComposable (Specification Φ) Sigma where
  red_mul {R S T π π'} h h' := by
    rw [constructs_iff, mul_smul]
    exact (Set.smul_set_mono h).trans h'
  red_one R := constructs_one_of_subset le_rfl

/-- MauRen11 Definition 7(i), JM20 Theorem 1.1, and CR18 Lemma 5.1:
construction statements compose serially. The right factor acts first, so a
construction by `π` followed by one by `π'` is labelled `π' * π`. -/
@[crypto_rule "ac.constructs.serial" ac_spec_construction abstract_crypto]
theorem Constructs.trans {π π' : Sigma} {R S T : Specification Φ}
    (h : R —[π]→ S) (h' : S —[π']→ T) :
    R —[π' * π]→ T :=
  red_mul h h'
end Constructs

section ActCommute

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- Composition order invariance for one pair, as commuting **actions** —
the form that survives free converter monoids, where distinct words never
commute as monoid elements. -/
def ActCommute (Φ : Type*) (a b : Sigma) [MulAction Sigma Φ] : Prop :=
  ∀ R : Φ, a • b • R = b • a • R

theorem ActCommute.symm {a b : Sigma} (h : ActCommute Φ a b) : ActCommute Φ b a :=
  fun R => (h R).symm

/-- Monoid-level commutation gives action-level commutation (never
conversely). -/
theorem _root_.Commute.actCommute {a b : Sigma} (h : Commute a b) :
    ActCommute Φ a b :=
  fun R => by rw [← mul_smul, h.eq, mul_smul]

/-- The pointwise equation, at specification level. -/
theorem ActCommute.smul_set {a b : Sigma} (h : ActCommute Φ a b)
    (S : Specification Φ) : a • b • S = b • a • S := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨a • z, ⟨z, hz, rfl⟩, (h z).symm⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨b • z, ⟨z, hz, rfl⟩, h z⟩

end ActCommute

section Simulator

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- JM20 §2.2, **Proposition 2.1**: "Let `ℛ`, `𝒮`, and `𝒯` be
specifications, and let `π` and `π′` be protocols for `ℛ` and `𝒮`,
respectively.  For any simulators `σ` (for `𝒮`) and `σ′` (for `𝒯`), such
that the set of interfaces controlled by the simulators are disjoint from
the ones controlled by the protocols, we have

  1. `ℛ —π→ σ𝒮 ∧ 𝒮 —π′→ σ′𝒯 ⟹ ℛ —π′∘π→ σσ′𝒯`"

"*Proof.* By composition order invariance we have `π′σ𝒮 = σπ′𝒮 ⊆ σσ′𝒯`,
implying `𝒮 —π′→ σ′𝒯 ⟹ σ𝒮 —π′→ σσ′𝒯`.  The first property then follows
directly from combining this with Theorem 1."

The paper's disjoint-interface premise enters only as `ActCommute Φ π' σ` —
action-level, which the free converter monoid can satisfy — and that is all
the proof consumes. -/
theorem Constructs.simulator_trans {π π' σ σ' : Sigma} {R S T : Specification Φ}
    (h : R —[π]→ σ • S) (h' : S —[π']→ σ' • T) (hc : ActCommute Φ π' σ) :
    R —[π' * π]→ (σ * σ') • T := by
  rw [constructs_iff, mul_smul]
  calc π' • π • R ⊆ π' • σ • S := Set.smul_set_mono h
    _ = σ • π' • S := hc.smul_set S
    _ ⊆ σ • σ' • T := Set.smul_set_mono h'
    _ = (σ * σ') • T := (mul_smul ..).symm

end Simulator

end AbstractCryptography
