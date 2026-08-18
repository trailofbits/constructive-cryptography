/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Specification.Basic
import AbstractCryptography.Specification.Parallel

/-!
# Relaxations (JM20 §2.3, CR18 §5.2.3, MauRen16)

A relaxation weakens a specification to an "almost-as-good" one: statistical
error, computational assumptions, and no-guarantee interfaces are all
formalized this way rather than being hard-coded into the construction
notion.

This file is carrier-free: no pseudo-emetric and no converter submonoid
appears here.  The two carrier-bearing specializations sit downstream —
`AbstractCryptography.Metric.Epsilon` (the `ε`-relaxation, `epsilonRelaxation`, and the
distinguisher-indexed budgets) and `AbstractCryptography.Algebra.Star` (the
`∗`-relaxation and MauRen16 §3.4's right-outbound `⟦`).

## Two different definitions

CR18 and JM20 both say "relaxation", but they do **not** define the same
thing.  CR18's is a map on *specifications*; JM20's is a map on *single
resources*, lifted by union (`Relaxation.ofPointwise`).  The `Relaxation`
structure here is CR18 Def 5.5 plus monotonicity, so

`JM20 pointwise lifts ⊆ Relaxation ⊆ CR18 extensive maps`,

and both inclusions are strict once the resource carrier has at least two
elements.

CR18 §5.2.3, **Definition 5.5**:

> "A relaxation `ρ` is a function `P(Φ) → P(Φ)` such that `ℛ ⊆ ρ(ℛ)`."

— that and nothing more: any extensive map.  CR18 notes the pointwise
case only as the typical one, one page earlier (§5.2.1):

> "Typically, a relaxation is defined by a function `ρ : Φ → P(Φ)` which
> induces a function `ρ : P(Φ) → P(Φ)` as follows:
>
>   `ρ(ℛ) = ⋃_{R∈ℛ} ρ(R).`"

JM20 §2.3, **Definition 2** — the pointwise notion, definitionally:

> "Let `Θ` denote the set of all resources.  A relaxation `φ` is a
> function `φ : Θ → 2^Θ` (where `2^Θ` denotes the power set of `Θ`) such
> that `R ∈ φ(R)` for all `R ∈ Θ`.  In addition, for a specification `ℛ`,
> we define `ℛ^φ := ⋃_{R∈ℛ} φ(R)` as a shorthand notation."

JM20 §2.3, **Proposition 3**:

> "For any specifications `ℛ` and `𝒮`, and any relaxation `φ`, we have
>
>   1. `ℛ ⊆ ℛ^φ`,
>   2. `ℛ ⊆ 𝒮 ⟹ ℛ^φ ⊆ 𝒮^φ`,
>   3. `(ℛ ∩ 𝒮)^φ ⊆ ℛ^φ ∩ 𝒮^φ`,
>   4. `(ℛ ∪ 𝒮)^φ = ℛ^φ ∪ 𝒮^φ`.
>
> *Proof.* All properties trivially follow from `R ∈ φ(R)`."

Prop 3.4 is an equality about JM20 Def 2; it is not guaranteed for arbitrary
CR18 Def 5.5 relaxations.

* `Relaxation Φ` — CR18 Def 5.5 plus monotonicity (Prop 3.2, which the
  union lift always has and which CR18 Def 5.5 does not state).
* `Relaxation.ofPointwise` — **JM20 Def 2**, the union lift.
* Prop 3.1 = `le_toFun`, Prop 3.2 = `mono`, Prop 3.3 = `inter_subset`.
* Prop 3.4 splits: `ofPointwise_union` is the paper's **equality**, and
  it is stated only for `ofPointwise`; `union_subset` is the `⊇`
  inclusion, all that survives for a general `Relaxation`.
* `Relaxation.Compatible` — CR18 Def 5.6, in pull-through form
  `π φ(ℛ) ⊆ φ(πℛ)` (equivalent by `compatible_iff`); `ParCompatible` is
  CR18 Def 5.7's binary specification-level specialization.  Compatible
  relaxations can be "pulled to the outside" of construction chains:
  `Constructs.relax_trans` (CR18 eq. (5.4)).
* `Relaxation.epsilonRelaxation` — the ε-relaxation from a pseudo-emetric (CR18
  §5.2.3, JM20 Def 3 specialized to a single metric): `ℛ^ε = ⋃_{R∈ℛ}`
  closed ε-ball.  `epsilonRelaxation_epsilonRelaxation_subset` is JM20 Thm 2 (errors add up, by the
  triangle inequality); compatibility (JM20 Thm 3) holds when the action is
  non-expanding (`IsNonexpandingSMul`) and parallel composition is
  non-expanding (`IsNonexpandingPar`); `Constructs.epsilonRelaxation_trans` is JM20
  Cor 1.  JM20's per-distinguisher refinement (`ε` a function of the
  distinguisher, `ε_π(D) = ε(Dπ)`) is
  `DistinguisherClass.reductionRelaxation`.
* `Relaxation.star` — the *-relaxation (CR18 Def 5.9): no guarantee at an
  adversary interface, modeled by attaching arbitrary converters from a
  `Submonoid` (Def 17-style closed converter class).
* `constructs_of_simulator` — MauRen16 §4.2's demotion of the simulator to a
  proof device: exhibiting one simulator `σ` with `d(πR, σS) ≤ ε` proves the
  construction of the doubly-relaxed ideal specification `R —π→ (S^∗)^ε`.

## References

* [D. Jost, U. Maurer, *Overcoming Impossibility Results in Composable
  Security using Interval-Wise Guarantees*, CRYPTO 2020][JM20], §2.3.
* [U. Maurer, *Cryptography Foundations* lecture notes][CR18], §5.2.3,
  §5.3.6.
* [U. Maurer, R. Renner, *From Indifferentiability to Constructive
  Cryptography (and Back)*, TCC 2016-B][MauRen16].
-/

namespace AbstractCryptography

universe u v w

open Pointwise
open scoped ENNReal

variable {Sigma Φ : Type*}

/-- CR18 §5.2.3, **Definition 5.5**: "A relaxation `ρ` is a function
`P(Φ) → P(Φ)` such that `ℛ ⊆ ρ(ℛ)`."

This structure adds monotonicity, which CR18 Def 5.5 does not require and
every JM20 union lift has (Prop 3.2).  Idempotence is *not* required — the
ε-relaxation is not idempotent — so this is not a `ClosureOperator`. -/
structure Relaxation (Φ : Type*) where
  /-- The underlying map on specifications. -/
  toFun : Specification Φ → Specification Φ
  /-- JM20 Prop 3.1: "`ℛ ⊆ ℛ^φ`" — which is CR18 Def 5.5's own
  requirement, `ℛ ⊆ ρ(ℛ)`. -/
  le_toFun (R : Specification Φ) : R ⊆ toFun R
  /-- JM20 Prop 3.2: "`ℛ ⊆ 𝒮 ⟹ ℛ^φ ⊆ 𝒮^φ`". -/
  mono : Monotone toFun

namespace Relaxation

instance : CoeFun (Relaxation Φ) fun _ => Specification Φ → Specification Φ := ⟨toFun⟩

/-- Paper-order application of a relaxation; definitionally `ρ R`. -/
@[reducible] def relaxedBy (R : Specification Φ) (ρ : Relaxation Φ) : Specification Φ :=
  ρ R

/-- `R ^ᵣ[ρ]` is the scoped notation for `Relaxation.relaxedBy R ρ`. -/
scoped[AbstractCryptography] notation:max R:max " ^ᵣ[" ρ "]" =>
  Relaxation.relaxedBy R ρ

/-- JM20 §2.3, **Definition 2**: "Let `Θ` denote the set of all
resources.  A relaxation `φ` is a function `φ : Θ → 2^Θ` (where `2^Θ`
denotes the power set of `Θ`) such that `R ∈ φ(R)` for all `R ∈ Θ`.  In
addition, for a specification `ℛ`, we define `ℛ^φ := ⋃_{R∈ℛ} φ(R)` as a
shorthand notation."

This is narrower than the monotone `Relaxation` structure above: it is
exactly CR18's "typical" pointwise case.  `ofPointwise_union` is JM20
Prop 3.4's stronger equality. -/
def ofPointwise (φ : Φ → Specification Φ) (self_mem : ∀ R, R ∈ φ R) : Relaxation Φ where
  toFun R := ⋃ r ∈ R, φ r
  le_toFun _ x hx := Set.mem_biUnion hx (self_mem x)
  mono _ _ h := Set.biUnion_mono h fun _ _ => le_rfl

@[simp] theorem mem_ofPointwise_iff {φ : Φ → Specification Φ} {h : ∀ R, R ∈ φ R} {R : Specification Φ} {x : Φ} :
    x ∈ ofPointwise φ h R ↔ ∃ r ∈ R, x ∈ φ r := by
  simp [ofPointwise]

/-- JM20 Prop 3.3: "`(ℛ ∩ 𝒮)^φ ⊆ ℛ^φ ∩ 𝒮^φ`".  An inclusion in the paper
too; monotonicity is all it needs. -/
theorem inter_subset (φ : Relaxation Φ) (R S : Specification Φ) : φ (R ∩ S) ⊆ φ R ∩ φ S :=
  Set.subset_inter (φ.mono Set.inter_subset_left) (φ.mono Set.inter_subset_right)

/-- The `⊇` half of JM20 Prop 3.4 — *not* the paper's statement.

JM20 Prop 3.4 reads "`(ℛ ∪ 𝒮)^φ = ℛ^φ ∪ 𝒮^φ`", an **equality**, for a
JM20 Def 2 (pointwise) relaxation; that is `ofPointwise_union`.  For a
merely monotone relaxation the equality can fail and only this inclusion
follows. -/
theorem union_subset (φ : Relaxation Φ) (R S : Specification Φ) : φ R ∪ φ S ⊆ φ (R ∪ S) :=
  Set.union_subset (φ.mono Set.subset_union_left) (φ.mono Set.subset_union_right)

/-- JM20 Prop 3.4, the paper's statement: "`(ℛ ∪ 𝒮)^φ = ℛ^φ ∪ 𝒮^φ`" — an
equality, available because `φ` is a JM20 Def 2 pointwise relaxation.
Compare `union_subset`. -/
theorem ofPointwise_union {φ : Φ → Specification Φ} {h : ∀ R, R ∈ φ R} (R S : Specification Φ) :
    ofPointwise φ h (R ∪ S) = ofPointwise φ h R ∪ ofPointwise φ h S := by
  simp only [ofPointwise, Set.biUnion_union]

/-- Composition of relaxations: apply `ψ`, then `φ`, which is the order JM20
§4.3 writes `ψ · φ`.  This is not the combined relaxation of JM20 Definition
8 or 9. -/
def comp (φ ψ : Relaxation Φ) : Relaxation Φ where
  toFun R := φ (ψ R)
  le_toFun R := (ψ.le_toFun R).trans (φ.le_toFun _)
  mono _ _ h := φ.mono (ψ.mono h)

@[simp] theorem comp_apply (φ ψ : Relaxation Φ) (R : Specification Φ) :
    φ.comp ψ R = φ (ψ R) := rfl

/-- Pull-through form of CR18 Definition 5.6: applying a protocol after
relaxing is contained in relaxing after protocol application.  `compatible_iff`
below identifies it with the paper's construction-preservation phrasing.

JM20 Theorem 3 transports the error parameter, `π(ℛ^ε) ⊆ (πℛ)^{ε_π}`; this
predicate keeps `φ` fixed. -/
def Compatible (Sigma : Type*) [SMul Sigma Φ] (φ : Relaxation Φ) : Prop :=
  ∀ (π : Sigma) (R : Specification Φ), π • φ R ⊆ φ (π • R)

/-- Compatibility is closed under composition; this is the mechanism behind
JM20 Theorem 12, once Theorem 10 has rewritten the combined from-until
relaxation as an alternating nesting.  JM20 Theorem 14 additionally
transports `ε` to `ε_π`, so it is not an instance of this. -/
theorem Compatible.comp [SMul Sigma Φ] {φ ψ : Relaxation Φ}
    (hφ : φ.Compatible Sigma) (hψ : ψ.Compatible Sigma) :
    (φ.comp ψ).Compatible Sigma :=
  fun π R => (hφ π (ψ R)).trans (φ.mono (hψ π R))

/-- CR18 §5.2.3, **Definition 5.6** as stated: "A relaxation `ρ` is
compatible with the construction set `Γ` if any construction statement
holds also if the assumed and the constructed resource specification is
relaxed by `ρ`, i.e., if

  `ℛ —γ→ 𝒮 ⟹ ρ(ℛ) —γ→ ρ(𝒮)`." -/
theorem compatible_iff [Monoid Sigma] [MulAction Sigma Φ] (φ : Relaxation Φ) :
    φ.Compatible Sigma ↔ ∀ (π : Sigma) (R S : Specification Φ), R —[π]→ S → φ R —[π]→ φ S := by
  constructor
  · exact fun hc π R S h => (hc π R).trans (φ.mono h)
  · exact fun h π R => h π R (π • R) (constructs_iff.mpr Set.Subset.rfl)

/-- CR18 §5.2.3, **Definition 5.7**: "A relaxation `ρ` is compatible
with the parallel composition (or tuple-forming) operation if

  `[ℛ₁, …, ℛᵢ₋₁, ρ(ℛᵢ), ℛᵢ₊₁, …, ℛₙ] ⊆ ρ([ℛ₁, …, ℛₙ])`.

This definition naturally extends to specifications `ℛ₁, …, ℛₙ`."

Stated here in the binary form (`n = 2`, either side). -/
def ParCompatible [Par Φ] (φ : Relaxation Φ) : Prop :=
  ∀ R T : Specification Φ, (φ R ∥ T ⊆ φ (R ∥ T)) ∧ (T ∥ φ R ⊆ φ (T ∥ R))

end Relaxation

section RelaxedComposition

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- CR18 §5.2.3: "These two compatibility properties allow us to compose
construction statements that contain relaxations on the right (the
constructed) side by 'pulling relaxations to the outside'.  For example,
we have

  `ℛ —γ→ ρ(𝒮) ∧ 𝒮 —γ′→ 𝒯  ⟹  ℛ —γ′∘γ→ ρ(𝒯)`     (5.4)

because `ρ(𝒮) —γ′→ ρ(𝒯)` and hence Lemma 5.1 can be applied to obtain
(5.4)." -/
theorem Constructs.relax_trans {π π' : Sigma} {R S T : Specification Φ} {φ : Relaxation Φ}
    (h : R —[π]→ φ S) (h' : S —[π']→ T) (hφ : φ.Compatible Sigma) :
    R —[π' * π]→ φ T := by
  rw [constructs_iff, mul_smul]
  calc π' • π • R ⊆ π' • φ S := Set.smul_set_mono h
    _ ⊆ φ (π' • S) := hφ π' S
    _ ⊆ φ T := φ.mono h'

/-- Parallel analogue of `Constructs.relax_trans` via CR18 Def 5.7. -/
theorem Constructs.relax_par [Par Φ] [Par Sigma] [SMulParClass Sigma Φ]
    {π : Sigma} {R S : Specification Φ} {φ : Relaxation Φ}
    (h : R —[π]→ φ S) (T : Specification Φ) (hφ : φ.ParCompatible) :
    R ∥ T —[π ∥ 1]→ φ (S ∥ T) :=
  fun _ hx => (hφ S T).1 (Constructs.par_left T h hx)

/-- Binary right-slot counterpart of `Constructs.relax_par`, using the second
clause of CR18 Definition 5.7's specification-level specialization. -/
theorem Constructs.relax_par_right [Par Φ] [Par Sigma] [SMulParClass Sigma Φ]
    {π : Sigma} {R S : Specification Φ} {φ : Relaxation Φ}
    (h : R —[π]→ φ S) (T : Specification Φ) (hφ : φ.ParCompatible) :
    T ∥ R —[(1 : Sigma) ∥ π]→ φ (T ∥ S) :=
  fun _ hx => (hφ S T).2 (red_one_par T h hx)

end RelaxedComposition
namespace Relaxation

/-- A relaxation is determined by its underlying map on specifications. -/
theorem toFun_injective :
    Function.Injective (Relaxation.toFun : Relaxation Φ → Specification Φ → Specification Φ) := by
  rintro ⟨f, _, _⟩ ⟨g, _, _⟩ h
  cases h
  rfl

end Relaxation

end AbstractCryptography
