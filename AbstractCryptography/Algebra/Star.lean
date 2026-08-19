/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import AbstractCryptography.Metric.Epsilon

/-!
# The `∗`-relaxation, the right-outbound `⟦`, and indifferentiability

The relaxations whose parameter is a **converter class** rather than an error:

* `Relaxation.star` — CR18 Definition 5.9's `ℛ^{∗E} := {αᴱR | α ∈ Σ, R ∈ ℛ}`,
  "no guarantee at an adversary interface", generic over a `Submonoid` of the
  ambient converter monoid: idempotence, monotonicity in the class, both
  compatibility halves, and MauRen16 §4.2's simulator recipe (`star_construct`
  and its `ε`-relaxed form `star_construct_eps`).
* `Relaxation.outboundHull` — MauRen16 §3.4's `ℛ⟦`, together with the
  correction to eq. (2): `ℛ ⊆ ℛ⟦` is **not** unconditional, and
  `outboundHull_eq_empty_of_top` witnesses that the missing hypothesis cannot
  be dropped.
* `Indifferentiable` — MauRen11 App. D Definition 23, and MauRen16 Lemma 5
  turning it into the construction statement `R —π→ (S∗)ᵉ`.

Everything here needs `Monoid Sigma` / `MulAction Sigma Φ` and a `Submonoid Sigma`, which
is why it is the top tier of the split.  The carrier-free calculus is
`AbstractCryptography.Specification.Relaxation`; the metric error notions this file
composes with are `AbstractCryptography.Metric.Epsilon`.
-/

namespace AbstractCryptography

open Pointwise
open scoped ENNReal

variable {Sigma Φ : Type*}

/-! ### The *-relaxation (CR18 Def 5.9) -/

namespace Relaxation

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- CR18 §5.3.6: "We recall that an adversary entity Eve is only a
hypothetical entity, taken into consideration in order to state
guarantees to the honest parties no matter what Eve does.  Eve simply
stands for a universal quantifier (`∀`) over strategies, not for an
entity that actually participates.  In other words, we want to capture
that there is no guarantee for what happens at an adversary interface.
An arbitrary converter could be applied at such an interface.  This is
modeled by the following relaxation type."

**Definition 5.9**: "The `∗`-relaxation of a specification `ℛ` for
interface `E` is:

  `ℛ^{∗E} := {αᴱR | α ∈ Σ, R ∈ ℛ}`,

where `Σ` denotes the set of trivial converters mentioned above.  If
there is only a single adversary interface, we can drop the superscript
`E` and simply write `ℛ^∗`."

Here `star` is generic over an action submonoid `H`. `Submonoid` supplies
identity (used for extensivity) and multiplication closure (used by the
subsequent star calculus). This models the full ambient converter class, or a
feasible class only after MauRen11 Definition 17's restricted cryptographic
algebra has been constructed; its efficient class need not contain identity.
The declaration itself neither records an interface `E` nor proves that `H`
is CR18's class of trivial converters. An instantiation must select the
corresponding supported interface or genuinely joint merged-interface
submonoid and action. -/
def star (H : Submonoid Sigma) : Relaxation Φ where
  toFun R := (H : Set Sigma) • R
  le_toFun _ x hx := ⟨1, H.one_mem, x, hx, one_smul Sigma x⟩
  mono _ _ h := Set.smul_subset_smul_left h

/-- Stable paper-order star relaxation with its converter class explicit. -/
@[reducible] def starRelaxed (R : Specification Φ) (H : Submonoid Sigma) : Specification Φ :=
  Relaxation.star H R

/-- `R ^⋆[H]` expands to `Relaxation.starRelaxed R H`. -/
scoped[AbstractCryptography] notation:max R:max " ^⋆[" H "]" =>
  Relaxation.starRelaxed R H

theorem mem_star_iff {H : Submonoid Sigma} {R : Specification Φ} {x : Φ} :
    x ∈ (star H : Relaxation Φ) R ↔ ∃ σ ∈ H, ∃ r ∈ R, σ • r = x := Set.mem_smul

/-- The `∗`-relaxation is idempotent — the submonoid absorbs its own
products.  "It is easy to see that the described `∗`-relaxation is
idempotent: For any specification `S` … we have `(S∗)∗ = S∗`."  Stated
here for `star` over any submonoid; LiuMau20 §2.5's `(S∗Z)∗Z = S∗Z` is
the instance `H = zSub Z`. -/
theorem star_idem (H : Submonoid Sigma) (R : Specification Φ) :
    (star H : Relaxation Φ) ((star H) R) = (star H) R := by
  refine le_antisymm ?_ ((star H : Relaxation Φ).le_toFun _)
  rintro x ⟨σ, hσ, y, ⟨τ, hτ, r, hr, rfl⟩, rfl⟩
  exact ⟨σ * τ, mul_mem hσ hτ, r, hr, mul_smul σ τ r⟩

/-- `∗` is monotone in the converter class: a larger `Σ` gives a weaker
specification. -/
theorem star_mono_submonoid {H H' : Submonoid Sigma} (h : H ≤ H') (R : Specification Φ) :
    (star H : Relaxation Φ) R ⊆ (star H') R := by
  rintro x ⟨σ, hσ, r, hr, rfl⟩
  exact ⟨σ, h hσ, r, hr, rfl⟩

/-- A converter commuting with the whole class pulls through the
relaxation: `π(ℛ∗) ⊆ (πℛ)∗`.  (The `∗`-compatibility of `star_compatible`
is the special case where `π` is quantified over all of `Sigma`; here `π` is
a single fixed converter, e.g. a composite of honest-interface
attachments.) -/
theorem smul_star_subset {H : Submonoid Sigma} {g : Sigma}
    (hg : ∀ σ ∈ H, ActCommute Φ g σ)
    (R : Specification Φ) :
    g • (star H : Relaxation Φ) R ⊆ (star H) (g • R) := by
  rintro x ⟨y, ⟨σ, hσ, r, hr, rfl⟩, rfl⟩
  refine ⟨σ, hσ, g • r, Set.smul_mem_smul_set hr, ?_⟩
  exact (hg σ hσ r).symm

/-- MauRen16 §4.2 / LiuMau20 §2.5's proof recipe as a `∗`-relaxation
lemma, over any converter class `H`.  "If one wants to prove that a given
specification `U` is contained in `S∗Z`, one can exhibit for every `U ∈ U`
a converter `α` such that `U = αᶻS` … the same `α` … is a (joint)
simulator for the interfaces in `Z`."

This theorem is the exact/perfect, singleton-ideal specialization rather than
MauRen16 Lemma 5's approximate statement itself. Its leaf premise has order
`∀ R ∈ real, ∃ s ∈ H`: the witness may vary with `R`, although for that `R`
it is reused for every incoming converter introduced by `star`. One uniform
joint simulator for the whole specification is the strictly stronger statement
`∃ s ∈ H, ∀ R ∈ real, g • R = s • ideal`.

If an honest attachment `g` commutes with the whole class `H` and, up to
some `s ∈ H`, sends every real resource to the ideal, then `g` constructs
the `∗`-relaxed ideal from the `∗`-relaxed real specification.  The
`∗Z`-relaxation is the instance `H = zSub γ Z`
(`AbstractCryptography.zStar_construct_of_simulators`). -/
theorem star_construct {H : Submonoid Sigma} {g : Sigma}
    (hg : ∀ σ ∈ H, ActCommute Φ g σ)
    {real : Specification Φ} {ideal : Φ}
    (hsim : ∀ R ∈ real, ∃ s ∈ H, g • R = s • ideal) :
    g • (star H : Relaxation Φ) real ⊆ (star H) {ideal} := by
  refine (smul_star_subset hg real).trans ?_
  rintro x ⟨h, hh, r, ⟨R, hR, rfl⟩, rfl⟩
  obtain ⟨s, hs, heq⟩ := hsim R hR
  refine ⟨h * s, mul_mem hh hs, ideal, rfl, ?_⟩
  show (h * s) • ideal = h • (g • R)
  rw [mul_smul, heq]

/-- **The metric (`ε`-relaxed) form of `star_construct`** — MauRen16 §4.2
Lemma 5 at specification level.  When the honest attachment `g` sends every
real resource to *within `ε`* of the ideal (up to a class member `s ∈ H`),
it constructs the `ε`-ball of the `∗`-relaxed ideal from the `∗`-relaxed
real specification: `g (ℛ∗) ⊆ ((S∗)ᵉ)`.  This is what a real (statistical /
computational) simulator gives. Literal equality witnesses for
`star_construct` imply this theorem's `ε = 0` premise. On a pseudo-emetric
carrier its zero-radius target can be strictly larger than the exact target;
the conclusions coincide only under zero-distance separation (or after the
corresponding quotient). -/
theorem star_construct_eps [PseudoEMetricSpace Φ] [IsNonexpandingSMul Sigma Φ]
    {H : Submonoid Sigma} {g : Sigma} (hg : ∀ σ ∈ H, ActCommute Φ g σ)
    {real : Specification Φ} {ideal : Φ} {ε : ℝ≥0∞}
    (hsim : ∀ R ∈ real, ∃ s ∈ H, edist (g • R) (s • ideal) ≤ ε) :
    g • (star H : Relaxation Φ) real ⊆ epsilonRelaxation ε ((star H) {ideal}) := by
  rintro x ⟨y, ⟨σ, hσ, R, hR, rfl⟩, rfl⟩
  obtain ⟨s, hs, hd⟩ := hsim R hR
  refine mem_epsilonRelaxation_iff.mpr ⟨(σ * s) • ideal, ⟨σ * s, mul_mem hσ hs, ideal, rfl, rfl⟩, ?_⟩
  calc edist (g • σ • R) ((σ * s) • ideal)
      = edist (σ • g • R) (σ • s • ideal) := by
        rw [hg σ hσ R, mul_smul]
    _ ≤ edist (g • R) (s • ideal) := edist_smul_le σ _ _
    _ ≤ ε := hd

/-- **MauRen16 p. 18, unnumbered, inside the proof of Theorem 2**:
`(ℛᵋ)∗ ⊆ (ℛ∗)ᵋ` — the `ε`/`∗` interchange.  Relaxing first by an error and
then by the converter class is at least as weak as doing it the other way
round: an adversary converter `σ ∈ H` applied to a point within `ε` of `ℛ`
lands within `ε` of `σℛ ⊆ ℛ∗`.

The whole content is non-expansion (MauRen16 Definition 2) and nothing else —
`σ` moves the two points by at most the distance between them — so the
hypothesis is `IsNonexpandingSMul` alone; no commutation and no property of
`H` beyond being the class `∗` relaxes by are used.  The reverse inclusion is
**not** claimed: a point within `ε` of `σr` need not be `σ` of anything.

MauRen16 uses it to push an `ε` accumulated at an inner step out through the
surrounding `∗`, which is what any `ε`-relaxed `∗`-chain needs. -/
theorem star_epsilonRelaxation_subset_epsilonRelaxation_star [PseudoEMetricSpace Φ]
    [IsNonexpandingSMul Sigma Φ] (H : Submonoid Sigma) (ε : ℝ≥0∞)
    (R : Specification Φ) :
    (star H : Relaxation Φ) (epsilonRelaxation ε R) ⊆
      epsilonRelaxation ε ((star H) R) := by
  rintro x ⟨σ, hσ, y, hy, rfl⟩
  obtain ⟨r, hr, hyr⟩ := mem_epsilonRelaxation_iff.mp hy
  exact mem_epsilonRelaxation_iff.mpr
    ⟨σ • r, ⟨σ, hσ, r, hr, rfl⟩, (edist_smul_le σ y r).trans hyr⟩

/-! MauRen16 §4.2's remark on equation (3) — "Note that `πRβ ≈ᵋ Sσβ` due to the
non-expanding property of the pseudo-metric", the one place §4.2 actually
spends Definition 2 — is `edist_mul_smul_le_of_edist_le`, stated beside
Definition 2 itself in `AbstractCryptography.Metric.Nonexpansion`.  It is what
`star_construct_eps` above and `Indifferentiable.trans` below use inline, as
`edist_smul_le σ`. -/

/-- CR18 §5.3.6: "We point out that `∗`-relaxation is compatible
according to Definitions 5.6 and 5.7." — this is the Def 5.6 half.

The paper's statement is relative to a construction set `Γ`. The formal
conclusion below instead quantifies over every `π : Sigma`, so `hc` says that each
member of `H` centralizes the entire ambient monoid (and in particular forces
members of `H` to commute pairwise). This is a stronger sufficient
specialization of the paper's remark.

In a concrete distinct-interface model, it applies when the chosen constructor
carrier `Sigma` is restricted so that every element acts away from `H`'s interfaces,
as in JM20 Proposition 2. For one selected honest converter in an unrestricted
ambient converter monoid, use `smul_star_subset`; honest/adversary support
disjointness alone does not prove `hc` for every ambient converter. -/
theorem star_compatible {H : Submonoid Sigma}
    (hc : ∀ π : Sigma, ∀ σ ∈ H, ActCommute Φ π σ) :
    (star (Φ := Φ) H).Compatible Sigma := by
  rintro π R _ ⟨y, ⟨σ, hσ, r, hr, rfl⟩, rfl⟩
  refine ⟨σ, hσ, π • r, Set.smul_mem_smul_set hr, ?_⟩
  exact (hc π σ hσ r).symm

/-- CR18 §5.3.6's same remark ("compatible according to Definitions 5.6
and 5.7") — this is the selected ordered binary, both-slot specialization
of the Definition 5.7 half. It proves no identification between nested binary
`Par` expressions and the paper's primitive flat n-ary tuple.

The closure of the converter class under extension by the neutral converter is
an explicit hypothesis in each ordered slot. -/
theorem star_parCompatible [Par Φ] [Par Sigma] [SMulParClass Sigma Φ] {H : Submonoid Sigma}
    (hl : ∀ σ ∈ H, σ ∥ (1 : Sigma) ∈ H) (hr : ∀ σ ∈ H, (1 : Sigma) ∥ σ ∈ H) :
    (star (Φ := Φ) H).ParCompatible := by
  intro R T
  constructor
  · rintro x ⟨y, ⟨σ, hσ, r, hrR, rfl⟩, t, ht, rfl⟩
    exact ⟨σ ∥ 1, hl σ hσ, r ∥ t, par_mem_par hrR ht, by simp only [smul_par, one_smul]⟩
  · rintro x ⟨t, ht, y, ⟨σ, hσ, r, hrR, rfl⟩, rfl⟩
    exact ⟨1 ∥ σ, hr σ hσ, t ∥ r, par_mem_par ht hrR, by simp only [smul_par, one_smul]⟩

/-! ### Right-outbound resources and the `⟦` relaxation (MauRen16 §3.4)

MauRen16 pictures a two-interface resource: Alice acts on the left, Eve on the
right, and the paper *requires* the two to commute — `(αR)β = α(Rβ)` (p. 8),
"which justifies to write `αRβ`".

We do not introduce a second action for this.  In the interface-indexed setting
Alice's and Eve's converters are elements of the **same** converter monoid with
**disjoint support**, and the commutation the paper postulates is then a
consequence of the tuple monoid being a product — not an extra axiom.  So the
machinery below is parameterized by

* `H : Submonoid Sigma` — Eve's converters, the `Σ` of `R* = RΣ`; and
* `blk : Sigma` — the blocking converter `⊣`, which shuts the right interface,

and commutation appears as an **explicit hypothesis** wherever it is used, so a
carrier lacking it is excluded rather than silently assumed. -/

/-- MauRen16 §3.4: `S` is *right-outbound* when `S*⊣ = S⊣` — no converter
attached to the right interface has any effect at the left one, i.e. "no
signalling from the right to the left interface of `S` is possible". -/
def RightOutbound (H : Submonoid Sigma) (blk : Sigma) (S : Φ) : Prop :=
  ∀ β ∈ H, (blk * β) • S = blk • S

/-- MauRen16 §3.4 `ℛ⟦`: the right-outbound resources compatible with `ℛ` at the
left interface only.  This is what makes an impossibility result *strong* — it
tolerates arbitrary leakage to Eve, so "an impossibility result stating that
`ℛ⟦` is not constructible is a significantly stronger statement than that a
standard random oracle is not constructible" (p. 9). -/
def outboundHull (H : Submonoid Sigma) (blk : Sigma) (R : Specification Φ) : Specification Φ :=
  {S | RightOutbound H blk S ∧ blk • S ∈ blk • R}

theorem mem_outboundHull_iff {H : Submonoid Sigma} {blk : Sigma} {R : Specification Φ} {S : Φ} :
    S ∈ outboundHull H blk R ↔
      RightOutbound H blk S ∧ blk • S ∈ blk • R := Iff.rfl

/-- **MauRen16 eq. (2), idempotence half: `ℛ⟦ = (ℛ⟦)⟦`.**  This half holds
with no hypothesis at all: `⊇` because `(ℛ⟦)⊣ ⊆ ℛ⊣`, and `⊆` because any
`S ∈ ℛ⟦` is itself right-outbound and so contributes its own `S⊣`. -/
theorem outboundHull_idem (H : Submonoid Sigma) (blk : Sigma) (R : Specification Φ) :
    outboundHull H blk (outboundHull H blk R) = outboundHull H blk R := by
  ext S
  refine ⟨fun hS => ⟨hS.1, ?_⟩, fun hS => ⟨hS.1, ?_⟩⟩
  · obtain ⟨T, hT, hTS⟩ := hS.2
    exact hTS ▸ hT.2
  · exact Set.smul_mem_smul_set hS

/-- **MauRen16 eq. (2), containment half: `ℛ ⊆ ℛ⟦` — and it is NOT
unconditional.**  The source prints `ℛ ⊆ ℛ⟦ = (ℛ⟦)⟦` with no hypothesis, but
`ℛ⟦` contains *only* right-outbound resources by construction, so a
specification with a signalling member cannot be contained in its own hull.
The precondition is exactly that every member of `ℛ` be right-outbound.

Every resource the paper actually applies this to satisfies it — public
randomness `PRᵏ`, and a random oracle that hides Alice's queries from Eve, are
both right-outbound — so Corollary 1's use of eq. (2) is sound.  It is the
general statement as printed that over-claims.  `outboundHull_eq_empty_of_top`
below shows the hypothesis cannot simply be dropped. -/
theorem subset_outboundHull (H : Submonoid Sigma) (blk : Sigma) {R : Specification Φ}
    (outbound : ∀ r ∈ R, RightOutbound H blk r) :
    R ⊆ outboundHull H blk R :=
  fun _ hr => ⟨outbound _ hr, Set.smul_mem_smul_set hr⟩

/-- **The precondition of `subset_outboundHull` cannot be dropped**, so
MauRen16 eq. (2)'s `ℛ ⊆ ℛ⟦` is not a theorem as printed.

Witness: `Function.End Bool`, blocking converter `⊣ = 1`, and Eve allowed
*every* endofunction.  Right-outboundness then reads `∀ β, β S = S`, which the
constant function `fun _ => !S` refutes for every `S`.  So **no** resource is
right-outbound, the hull is empty, and no nonempty `ℛ` is contained in it. -/
theorem outboundHull_eq_empty_of_top (R : Set Bool) :
    outboundHull (⊤ : Submonoid (Function.End Bool)) 1 R = ∅ := by
  ext S
  simp only [Set.mem_empty_iff_false, iff_false, mem_outboundHull_iff, not_and]
  rintro outbound
  have signal := outbound (show Function.End Bool from fun _ => !S)
    (Submonoid.mem_top _)
  simp only [one_mul] at signal
  exact absurd signal (by cases S <;> simp [Function.End.smul_def])

/-- **MauRen16 Lemma 3**, which the source states *without proof*:
`ℛ —π→ 𝒮 ⟹ ℛ* —π→ 𝒮*`.

The whole content is the commutation the paper postulates on p. 8: `π` pushes
through Eve's converter `β`, so an arbitrary right-interface behaviour on the
assumed side maps to the same behaviour on the ideal side. -/
theorem constructs_star {π : Sigma} {H : Submonoid Sigma} {R S : Specification Φ}
    (commutes : ∀ β ∈ H, π * β = β * π)
    (construct : Constructs π R S) :
    Constructs π ((H : Set Sigma) • R) ((H : Set Sigma) • S) := by
  rintro _ ⟨_, ⟨β, hβ, r, hr, rfl⟩, rfl⟩
  refine ⟨β, hβ, π • r, construct ⟨r, hr, rfl⟩, ?_⟩
  simp only [smul_smul, commutes β hβ]

/-- **MauRen16 Lemma 4**, also stated *without proof* in the source:
`ℛ —π→ 𝒮 ⟹ ℛ⟦ —π→ 𝒮⟦`.

Two obligations.  That `π • T` is still right-outbound needs `π` to commute
with `blk * β`, whereupon `T`'s own right-outboundness discharges it; that its
blocked form lands in `𝒮⊣` needs only commutation with `blk` and the
hypothesis `π • R ⊆ S`.  Neither obligation requires members of `ℛ` to be
right-outbound, so unlike eq. (2) this lemma **is** unconditional. -/
theorem constructs_outboundHull {π : Sigma} {H : Submonoid Sigma} {blk : Sigma}
    {R S : Specification Φ}
    (commutesH : ∀ β ∈ H, π * β = β * π) (commutesBlk : π * blk = blk * π)
    (construct : Constructs π R S) :
    Constructs π (outboundHull H blk R) (outboundHull H blk S) := by
  rintro _ ⟨T, ⟨outbound, ⟨r, hr, hblocked⟩⟩, rfl⟩
  have push : ∀ x : Φ, π • (blk • x) = blk • (π • x) := by
    intro x; rw [← mul_smul, commutesBlk, mul_smul]
  refine ⟨fun β hβ => ?_, ?_⟩
  · have swap : (blk * β) * π = π * (blk * β) := by
      rw [mul_assoc, ← commutesH β hβ, ← mul_assoc, ← commutesBlk, mul_assoc]
    show (blk * β) • (π • T) = blk • (π • T)
    calc (blk * β) • (π • T) = ((blk * β) * π) • T := by rw [← mul_smul]
      _ = (π * (blk * β)) • T := by rw [swap]
      _ = π • ((blk * β) • T) := by rw [mul_smul]
      _ = π • (blk • T) := by rw [outbound β hβ]
      _ = blk • (π • T) := push T
  · refine ⟨π • r, construct ⟨r, hr, rfl⟩, ?_⟩
    have blocked : blk • r = blk • T := hblocked
    show blk • (π • r) = blk • (π • T)
    rw [← push r, blocked, push T]

end Relaxation

/-- MauRen16 §4.2, **Lemma 5**: "If the metric is non-expanding, then

  `∃σ ∈ Σ : πR ≈ᵋ Sσ  ⟹  R —π→ (S∗)ᵋ`."

"*Proof.* Since `σ ∈ Σ` we have `Sσ ∈ SΣ = S∗`.  Hence `πR ≈ᵋ Sσ` implies
that `πR ⊆ (Sσ)ᵋ ⊆ (S∗)ᵋ`, which is the definition of `R —π→ (S∗)ᵋ`."

The simulator is thereby a proof device, not part of the notion: "the
simulator does not appear in the definition of a construction, and there
can be interesting construction statements proved in different ways than
by use of Lemma 5" (MauRen16 §4.2).

This is Lemma 5's explicit-witness form.  Its printed non-expansion premise is
deliberately not carried: the displayed membership proof never transports a
distance through an action.  The paper first uses non-expansion in the
following remark, to derive `πRβ ≈ᵋ Sσβ` after appending `β`.
`Indifferentiable.construct` below packages this fixed-`π` implication with
Definition 23. -/
theorem constructs_of_simulator [Monoid Sigma] [MulAction Sigma Φ] [PseudoEMetricSpace Φ]
    {H : Submonoid Sigma} {π : Sigma} {R S : Φ} {ε : ℝ≥0∞}
    (σ : Sigma) (hσ : σ ∈ H) (h : edist (π • R) (σ • S) ≤ ε) :
    ({R} : Specification Φ) —[π]→ Relaxation.epsilonRelaxation ε ((Relaxation.star H) {S}) := by
  rintro x ⟨r, rfl : r = R, rfl⟩
  exact Relaxation.mem_epsilonRelaxation_iff.mpr ⟨σ • S, ⟨σ, hσ, S, rfl, rfl⟩, h⟩

/-- **MauRen16 §4.3 (printed p. 13)** — the kernel of the explicit-simulation
rephrasing, before the target is named as a parallel composition.

The paper's step, with `[·,·]` abstracted away, is: an *exact* equation
`πR = Tσ` whose right factor `σ` lies in the admitted converter class exhibits
`πR` as a member of `TΣ = T∗`, and that membership *is* the construction
statement `R —π→ T∗`.

Nothing else is used: no metric, no non-expansion, no commutation, no property
of `H` beyond `σ ∈ H`.  Compare the two neighbours.  `Relaxation.star_construct`
reaches the same conclusion from a `∗`-relaxed *source* and therefore pays a
commutation premise that §4.3 never spends.  `constructs_of_simulator` is the
`ε`-relaxed form of the same step; on a pseudo-emetric carrier the exact
conclusion here is strictly stronger than that form at `ε = 0`, and it needs no
`PseudoEMetricSpace` at all. -/
theorem constructs_star_of_smul_eq [Monoid Sigma] [MulAction Sigma Φ]
    {H : Submonoid Sigma} {π : Sigma} {R T : Φ}
    (σ : Sigma) (hσ : σ ∈ H) (h : π • R = σ • T) :
    ({R} : Specification Φ) —[π]→ (Relaxation.star H) ({T} : Specification Φ) := by
  rintro x ⟨r, rfl : r = R, rfl⟩
  exact ⟨σ, hσ, T, rfl, h.symm⟩

/-- **MauRen16 §4.3 (printed p. 13), the explicit-simulation rephrasing as
printed** — the statement matrix row 45 asks for.

> "Suppose furthermore that one has shown that equality `πR = Sβ` holds for
> some system `β` that requires some computation, i.e., `β ∉ Σ`.  Then we can
> give the equation the following meaning.  Let `β̄` be a system corresponding
> to the resource that behaves like `β`, with inside and outside interface both
> available to Eve (only at the right interface).  Then one can rephrase the
> equation `πR = Sβ` as
>
>   `πR = [S, β̄] σ`,
>
> where `σ` is the trivial converter that simply connects `β̄` to `S`, i.e.,
> such that
>
>   `[S, β̄] σ = Sβ`.
>
> In other words, any equation of the type `πR = Sβ` can be turned into a
> construction statement of the form
>
>   `R —π→ ([S, β̄])∗`
>
> which makes the computational resource required for the 'simulation'
> explicit."

**How the paper's objects appear here.**  MauRen16's admitted converter set
`Σ` is the submonoid `H` that `∗` relaxes by; the ambient monoid `Sigma` holds
*all* converters, so the offending `β` is an ordinary `β : Sigma`.  The
resource `β̄` is `betaRes`, and `S ∥ betaRes` is the paper's `[S, β̄]`.

**Two hypotheses, both of them the paper's own.**  `connect` is the *defining
property* of the trivial converter σ — the paper introduces σ by exactly this
equation, `[S, β̄] σ = Sβ` — and `equation` is the given `πR = Sβ`.  That
`β̄` exists and that its connecting converter is admitted are carrier facts:
§4.3 posits them ("let `β̄` be a system corresponding to the resource that
behaves like `β`"), and they are hypotheses here for the same reason.

**`β ∉ Σ` is deliberately not carried.**  It is what makes the rephrasing
*worth* doing — an equation with an inadmissible right factor is not a
construction statement, and the move to `[S, β̄]` buys admissibility by paying
a parallel resource.  The implication itself holds for every `β`, so adding
`β ∉ H` would only weaken the theorem. -/
theorem constructs_star_par_of_smul_eq [Monoid Sigma] [MulAction Sigma Φ] [Par Φ]
    {H : Submonoid Sigma} {π β : Sigma} {R S betaRes : Φ}
    (σ : Sigma) (hσ : σ ∈ H)
    (connect : σ • (S ∥ betaRes) = β • S)
    (equation : π • R = β • S) :
    ({R} : Specification Φ) —[π]→
      (Relaxation.star H) ({S ∥ betaRes} : Specification Φ) :=
  constructs_star_of_smul_eq σ hσ (equation.trans connect.symm)

/-!
# Indifferentiability as a construction type

This file braids **two** papers, so each declaration is cited
individually.  The *definition* is MauRen11 App. D Definition 23; the
*theorem that makes it a construction statement* is MauRen16 §4.2
Lemma 5.  (MauRen16 has no Definition 23 — it numbers only Definitions 1
and 2.)

MauRen11 §D, **Definition 23**:

> "`S` is reducible to `R` in the sense of indifferentiability if
>
>   `πR ≈ Sσ`
>
> for some converters `π` and `σ`.  This definition captures both the
> information-theoretic and the computational setting."

MauRen16 §4.2, on the same equation (their eq. (3), `πR ≈ᵋ Sσ`):

> "The usefulness of finding a simulator `σ` satisfying the equation is
> that it implies a construction statement."

> "We point out, however, that in contrast to most of the existing
> literature, the actual statement of interest (see Lemma 5) to us is not
> Eq. (3) itself, but the construction statement it implies.  In
> particular, the simulator does not appear in the definition of a
> construction, and there can be interesting construction statements
> proved in different ways than by use of Lemma 5."

> "In view of Lemma 5, the notion of indifferentiability [18] can be
> understood as follows: `T` is indifferentiable from `S`, within `ε`, if
> `T ⊆ (S∗)ᵋ`, where this is proved by demonstrating a simulator `σ` such
> that `T ≈ᵋ Sσ`.  If `T = πR`, this corresponds to the construction
> statement `R —π→ (S∗)ᵋ`."
-/

open scoped ENNReal

variable {Sigma Φ : Type*} [Monoid Sigma] [MulAction Sigma Φ] [PseudoEMetricSpace Φ]

/-- MauRen11 App. D, **Definition 23**: "`S` is reducible to `R` in the
sense of indifferentiability if

  `πR ≈ Sσ`

for some converters `π` and `σ`.  This definition captures both the
information-theoretic and the computational setting."

Here MauRen11's `≈` is zero pseudo-distance, not resource equality. The
explicit finite-error reading is MauRen16's equation (3), `πR ≈ᵋ Sσ`, modeled
as distance `≤ ε`; at `ε = 0` this again means zero pseudo-distance. The
broader `ℝ≥0∞` codomain also contains the cryptographically vacuous radius
`⊤`, so a concrete security statement must supply its intended finite range.

Definition 23 is stated for doubled, out-bound two-interface resources, with
`π` on the honest side and `σ` on the dishonest side. This homogeneous
equation-level predicate does not record those roles or support conditions: the
chosen action must encode them. Taking `Sigma` to be the paper's allowed converter
class and `H = ⊤` recovers its same-class quantification; a proper `H` is an
additional simulator restriction. Information-theoretic or computational
meaning likewise comes from the concrete carrier, metric/distinguisher class,
and feasibility or asymptotic model, not from this Prop alone. -/
def Indifferentiable (H : Submonoid Sigma) (ε : ℝ≥0∞) (R S : Φ) : Prop :=
  ∃ π : Sigma, ∃ σ ∈ H, edist (π • R) (σ • S) ≤ ε

/-- MauRen16 §4.2, **Lemma 5**: "If the metric is non-expanding, then

  `∃σ ∈ Σ : πR ≈ᵋ Sσ  ⟹  R —π→ (S∗)ᵋ`."

"*Proof.* Since `σ ∈ Σ` we have `Sσ ∈ SΣ = S∗`.  Hence `πR ≈ᵋ Sσ` implies
that `πR ⊆ (Sσ)ᵋ ⊆ (S∗)ᵋ`, which is the definition of `R —π→ (S∗)ᵋ`."

This declaration packages Lemma 5 with Definition 23: the printed lemma fixes
`π`, while `h` existentially hides and the conclusion re-exports that same
protocol witness.

**Deviation from the cited statement, deliberate.** The Lemma's
hypothesis "if the metric is non-expanding" is *not* carried here, and
the omission is not an oversight: this is the singleton case
(`R S : Φ`, not specifications), where the conclusion is the direct
`ε`-ball membership `σ • S ∈ (S∗)` with `edist (π • R) (σ • S) ≤ ε` —
see `constructs_of_simulator`, whose proof invokes no non-expansion.
Non-expansion is what MauRen16 needs for the *surrounding* claims, not
for this implication: it is used in the remark that follows the Lemma
("Note that `πRβ ≈ Sσβ` due to the non-expanding property of the
pseudo-metric"), i.e. for the statement to survive an appended
distinguisher.  In this development non-expansion is required exactly
where it is genuinely load-bearing — `Relaxation.epsilonRelaxation_compatible`
(JM20 Thm 3), via the `IsNonexpandingSMul` instance, and hence in
`Indifferentiable.trans` below. -/
theorem Indifferentiable.construct {H : Submonoid Sigma} {ε : ℝ≥0∞} {R S : Φ}
    (h : Indifferentiable H ε R S) :
    ∃ π : Sigma, ({R} : Specification Φ) —[π]→
      Relaxation.epsilonRelaxation ε ((Relaxation.star H) {S}) := by
  obtain ⟨π, σ, hσ, hd⟩ := h
  exact ⟨π, constructs_of_simulator σ hσ hd⟩

/-- **Ours**, not a quotation.  MRH04 Theorems 1–2 give the
universal-substitution characterizations that motivate chaining, but do not
state this quantitative transitivity theorem.  MauRen16 §4.2 supplies the
one-leg reading through `R —π→ (S∗)ᵋ`; the composed witness order and selected
protocol/simulator crossing come from JM20 Proposition 2.  The additive
`ε + ε'` bound here is the repository's non-expansion-plus-triangle derivation.

The explicit hypotheses are non-expansion of the action
(`IsNonexpandingSMul`), multiplication closure of the simulator class
(`H : Submonoid Sigma`), and `hcomm`.  After the existential witnesses are
unpacked, the proof consumes only `Commute π₂ σ₁` for the selected outer
protocol and inner simulator.  The displayed `hcomm`, however, quantifies over
every `π' : Sigma` and every `σ ∈ H`; it centralizes `H` in all of `Sigma` and is a
strictly stronger sufficient premise than JM20's selected disjoint-interface
crossing or the local premise of `Constructs.simulator_trans`.  Thus this is a
conditional graded transitivity law, not unconditional transitivity. -/
theorem Indifferentiable.trans [IsNonexpandingSMul Sigma Φ]
    {H : Submonoid Sigma} {ε ε' : ℝ≥0∞} {R S T : Φ}
    (h : Indifferentiable H ε R S) (h' : Indifferentiable H ε' S T)
    (hcomm : ∀ π' : Sigma, ∀ σ ∈ H, ActCommute Φ π' σ) :
    Indifferentiable H (ε + ε') R T := by
  obtain ⟨π₁, σ₁, hσ₁, hd₁⟩ := h
  obtain ⟨π₂, σ₂, hσ₂, hd₂⟩ := h'
  refine ⟨π₂ * π₁, σ₁ * σ₂, mul_mem hσ₁ hσ₂, ?_⟩
  calc edist ((π₂ * π₁) • R) ((σ₁ * σ₂) • T)
      ≤ edist ((π₂ * π₁) • R) ((σ₁ * π₂) • S)
          + edist ((σ₁ * π₂) • S) ((σ₁ * σ₂) • T) := edist_triangle ..
    _ ≤ ε + ε' := by
        refine add_le_add ?_ ?_
        · have : (σ₁ * π₂) • S = π₂ • σ₁ • S := by
            rw [mul_smul]
            exact (hcomm π₂ σ₁ hσ₁ S).symm
          rw [this, mul_smul]
          exact (edist_smul_le π₂ (π₁ • R) (σ₁ • S)).trans hd₁
        · rw [mul_smul, mul_smul]
          exact (edist_smul_le σ₁ (π₂ • S) (σ₂ • T)).trans hd₂

end AbstractCryptography
