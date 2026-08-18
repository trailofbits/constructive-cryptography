/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Metric.Nonexpansion
import AbstractCryptography.Specification.Relaxation

/-!
# The scalar `ε`-relaxation

**Scalar** (CR18 §5.2.1) — `Relaxation.epsilonRelaxation`, the closed `ε`-ball of a
`PseudoEMetricSpace`, together with JM20 Theorem 2/3 and Corollary 1.  Nothing
here mentions a distinguisher class: `PseudoEMetricSpace` plus the two
non-expansion mixins of `AbstractCryptography.Metric.Nonexpansion` (MauRen16
Definition 2, the MR16-track grounding) is the whole structural input, and that
is what `RandomSystems.System.MetricFullyDefined` instantiates.

The distinguisher-**indexed** budget (Jost Definition 2.2.9 / JM20 Definition 3)
and its bridge to this scalar ball were split out to
`AbstractCryptography.Metric.ReductionRelaxation` on 2026-08-17: they are
indexed by a `DistinguisherClass`, which carries MauRen11 Definition 15/16
provenance and is behind the provenance fence.  See `LEDGER.md` PROVENANCE
FENCE.

The generic calculus this specializes lives in
`AbstractCryptography.Specification.Relaxation`; the `∗`-relaxation, which needs a
converter submonoid rather than a metric, lives in
`AbstractCryptography.Algebra.Star`.
-/

namespace AbstractCryptography

open Pointwise
open scoped ENNReal

variable {Sigma Φ : Type*}

/-! ### The ε-relaxation (CR18 §5.2.3, JM20 Def 3) -/

namespace Relaxation

section EBall

variable [PseudoEMetricSpace Φ]

/-- CR18 §5.2.1: "If a (pseudo-)metric `d` is defined on `Φ`, a natural
type of relaxation is the so-called `ǫ`-relaxation: For `ǫ > 0` we have

  `Rᵋ = {R′ | d(R, R′) ≤ ǫ}`

and hence

  `ℛᵋ = {R′ | ∃R ∈ ℛ : d(R, R′) ≤ ǫ}`."

Built as the `ofPointwise` (JM20 Definition 2) lift of the closed `ε`-ball. -/
@[crypto_rule "ac.relaxation.epsilonRelaxation" ac_specification abstract_crypto]
noncomputable def epsilonRelaxation (ε : ℝ≥0∞) : Relaxation Φ :=
  ofPointwise (fun R => Metric.closedEBall R ε) fun _ => Metric.mem_closedEBall_self

/-- Paper-order form of the scalar `ε`-relaxation. -/
@[reducible] def epsilonRelaxed (R : Specification Φ) (ε : ℝ≥0∞) : Specification Φ :=
  Relaxation.epsilonRelaxation ε R

/-- `R ^ε[ε]` expands to `Relaxation.epsilonRelaxed R ε`.  This denotes
a relaxed specification, not metric equality. -/
scoped[AbstractCryptography] notation:max R:max " ^ε[" ε "]" =>
  Relaxation.epsilonRelaxed R ε

theorem mem_epsilonRelaxation_iff {ε : ℝ≥0∞} {R : Specification Φ} {x : Φ} :
    x ∈ epsilonRelaxation ε R ↔ ∃ r ∈ R, edist x r ≤ ε := by
  simp [epsilonRelaxation, Metric.mem_closedEBall]

/-- JM20 §2.3: "First, the errors just add up, as expressed by the
following theorem."

**Theorem 2**: "Let `ℛ` be an arbitrary specification, and let `ε₁` and
`ε₂` be arbitrary `ε`-relaxations.  Then we have `(ℛ^{ε₁})^{ε₂} ⊆
ℛ^{ε₁+ε₂}`."

"*Proof.* This follows directly from the triangle inequality of the
distinguishing advantage." -/
theorem epsilonRelaxation_epsilonRelaxation_subset {ε₁ ε₂ : ℝ≥0∞} (R : Specification Φ) :
    epsilonRelaxation ε₂ (epsilonRelaxation ε₁ R) ⊆ epsilonRelaxation (ε₁ + ε₂) R := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_epsilonRelaxation_iff.mp hx
  obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
  exact mem_epsilonRelaxation_iff.mpr
    ⟨r, hr, (edist_triangle x y r).trans <| (add_le_add hxy hyr).trans_eq (add_comm _ _)⟩

/-- JM20 §2.3, **Theorem 3**, first half: "The `ε`-relaxation is
compatible with protocol application in the following sense that
`π(ℛ^ε) ⊆ (πℛ)^{ε_π}`, for `ε_π(D) := ε(Dπ(·))`, where `Dπ(·)` denotes
the distinguisher that first attaches `π` to the given resource and then
executes `D`."

Here at a fixed scalar radius, under CR18 §5.2.3's sufficient criterion: "A
function `γ ∈ Γ` is called non-expanding for the pseudo-metric `d` if
`d(γ(R), γ(S)) ≤ d(R, S)`" for resource points `R, S`. "If all `γ ∈ Γ` are
non-expanding for `d`, then the `ǫ`-relaxation is compatible with `Γ`." -/
theorem epsilonRelaxation_compatible [SMul Sigma Φ] [IsNonexpandingSMul Sigma Φ] (ε : ℝ≥0∞) :
    (epsilonRelaxation (Φ := Φ) ε).Compatible Sigma := by
  rintro π R _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
  exact mem_epsilonRelaxation_iff.mpr
    ⟨π • r, Set.smul_mem_smul_set hr, (edist_smul_le π y r).trans hyr⟩

/-- JM20 §2.3, **Theorem 3**, second half: "Moreover, it is compatible
with parallel composition, i.e., `[ℛ^ε, 𝒮] ⊆ [ℛ, 𝒮]^{ε_𝒮}`, for
`ε_𝒮(D) := sup_{S∈𝒮} ε(D[ · , S])`, where `D[ · , S]` denotes the
distinguisher that emulates `S` in parallel to the given resource and
then lets `D` interact with them."

Here at a fixed scalar radius, valid in both ordered binary slots under
`IsNonexpandingPar`.  The second slot is CR18 Definition 5.7's, supported by
MauRen11 footnote 9's independent right-context inequality. -/
theorem epsilonRelaxation_parCompatible [Par Φ] [IsNonexpandingPar Φ] (ε : ℝ≥0∞) :
    (epsilonRelaxation (Φ := Φ) ε).ParCompatible := by
  intro R T
  constructor
  · rintro x ⟨y, hy, t, ht, rfl⟩
    obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
    exact mem_epsilonRelaxation_iff.mpr
      ⟨r ∥ t, par_mem_par hr ht, (edist_par_left_le y r t).trans hyr⟩
  · rintro x ⟨t, ht, y, hy, rfl⟩
    obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
    exact mem_epsilonRelaxation_iff.mpr
      ⟨t ∥ r, par_mem_par ht hr, (edist_par_right_le t y r).trans hyr⟩

end EBall

end Relaxation
section EBallConstruction

variable [Monoid Sigma] [MulAction Sigma Φ] [PseudoEMetricSpace Φ]

/-- JM20 Definitions 1 and 3 (printed pp. 8 and 10) / CR18 Definitions 5.4
and 5.5 (printed pp. 115--116), scalar
specialization: constructing the `ε`-relaxation of `S` is exactly the
pointwise obligation that every constructed source resource lies within `ε`
of some center in `S`. -/
theorem constructs_epsilonRelaxation_iff {π : Sigma} {R S : Specification Φ} {ε : ℝ≥0∞} :
    R —[π]→ Relaxation.epsilonRelaxation ε S ↔
      ∀ r ∈ R, ∃ s ∈ S, edist (π • r) s ≤ ε := by
  constructor
  · intro h r hr
    exact Relaxation.mem_epsilonRelaxation_iff.mp (h (Set.smul_mem_smul_set hr))
  · rintro h _ ⟨r, hr, rfl⟩
    exact Relaxation.mem_epsilonRelaxation_iff.mpr (h r hr)

/-- Singleton specialization of `constructs_epsilonRelaxation_iff`, matching JM20's
singleton-specification convention after Definition 1 (printed p. 8). -/
theorem constructs_singleton_epsilonRelaxation_iff {π : Sigma} {R S : Φ} {ε : ℝ≥0∞} :
    ({R} : Specification Φ) —[π]→ Relaxation.epsilonRelaxation ε ({S} : Specification Φ) ↔
      edist (π • R) S ≤ ε := by
  rw [constructs_epsilonRelaxation_iff]
  simp

omit [Monoid Sigma] [MulAction Sigma Φ] in
/-- Scalar approximate construction: a reducible wrapper around the ordinary
construction relation into `Relaxation.epsilonRelaxation`, introducing no independent
relation.  It needs only `HasReduction`, not a `Monoid`/`MulAction` on `Sigma`,
so it accepts the same converters as the exact form. -/
@[reducible] def ApproximatelyConstructs [HasReduction (Specification Φ) Sigma]
    (π : Sigma) (ε : ℝ≥0∞)
    (R S : Specification Φ) : Prop :=
  HasReduction.Red R π (Relaxation.epsilonRelaxation ε S)

/-- `R —[π; ε]→ S` is `ApproximatelyConstructs π ε R S`. -/
scoped notation:50 R " —[" π "; " ε "]→ " S:51 =>
  ApproximatelyConstructs π ε R S

/-- Transport a scalar approximate construction across a supplied equality of
protocols.  The error and endpoint specifications are unchanged; only the
constructor label is rewritten. -/
theorem approximately_constructs_congr_protocol {π π' : Sigma} {ε : ℝ≥0∞}
    {R S : Specification Φ} (same : π = π') :
    (R —[π; ε]→ S) ↔ R —[π'; ε]→ S := by
  subst π'
  rfl

end EBallConstruction

section Cor1

variable [Monoid Sigma] [MulAction Sigma Φ] [PseudoEMetricSpace Φ]

/-- JM20 §2.3: "The composition theorem with `ε`-relaxations then follows
directly from these compatibility results.  The following corollary
phrases the corresponding result — which in older version of Constructive
Cryptography used to be called the composition theorem, thereby
hard-coding computational security."

**Corollary 1.1**: "For any specifications `ℛ`, `𝒮`, and `𝒯`, any
protocols `π` and `π′`, and any `ε`-relaxation `ε` and `ε′`, we have

  1. `ℛ —π→ 𝒮^ε ∧ 𝒮 —π′→ 𝒯^{ε′}  ⟹  ℛ —π′∘π→ 𝒯^{ε_{π′} + ε′}`"

— here at a fixed scalar radius, under `IsNonexpandingSMul`. -/
@[crypto_rule "ac.constructs.epsilonRelaxation_serial" ac_spec_construction abstract_crypto]
theorem Constructs.epsilonRelaxation_trans [IsNonexpandingSMul Sigma Φ] {π π' : Sigma} {R S T : Specification Φ}
    {ε ε' : ℝ≥0∞} (h : R —[π]→ Relaxation.epsilonRelaxation ε S) (h' : S —[π']→ Relaxation.epsilonRelaxation ε' T) :
    R —[π' * π]→ Relaxation.epsilonRelaxation (ε + ε') T := by
  rw [add_comm ε ε']
  exact fun x hx =>
    Relaxation.epsilonRelaxation_epsilonRelaxation_subset T
      (Constructs.relax_trans h h' (Relaxation.epsilonRelaxation_compatible ε) hx)

/-- JM20 §2.3, **Corollary 1**, item 2:
`ℛ —π→ 𝒮^ε ⟹ [ℛ, 𝒯] —π→ [𝒮, 𝒯]^{ε_𝒯}`, where Theorem 3 defines
`ε_𝒯(D) := sup_{T∈𝒯} ε(D[·, T])`.

The paper overloads `π` for its extension to the untouched parallel interface;
the homogeneous model here writes that converter `π ∥ 1`.  At a fixed scalar
radius, under `IsNonexpandingPar`. -/
theorem Constructs.epsilonRelaxation_par [Par Φ] [Par Sigma] [SMulParClass Sigma Φ] [IsNonexpandingPar Φ]
    {π : Sigma} {R S : Specification Φ} {ε : ℝ≥0∞} (h : R —[π]→ Relaxation.epsilonRelaxation ε S) (T : Specification Φ) :
    R ∥ T —[π ∥ 1]→ Relaxation.epsilonRelaxation ε (S ∥ T) :=
  h.relax_par T (Relaxation.epsilonRelaxation_parCompatible ε)

/-- Resource-level presentation of `Constructs.epsilonRelaxation_par`, on singleton
specifications. -/
theorem Constructs.epsilonRelaxation_par_resource
    [Par Φ] [Par Sigma] [SMulParClass Sigma Φ] [IsNonexpandingPar Φ]
    {π : Sigma} {R S : Φ} {ε : ℝ≥0∞}
    (h : ApproximatelyConstructs π ε ({R} : Specification Φ) ({S} : Specification Φ))
    (T : Φ) :
    ApproximatelyConstructs (π ∥ 1) ε
      ({R ∥ T} : Specification Φ) ({S ∥ T} : Specification Φ) := by
  simpa only [singleton_par_singleton] using
    h.epsilonRelaxation_par ({T} : Specification Φ)

end Cor1

end AbstractCryptography