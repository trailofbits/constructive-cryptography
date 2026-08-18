/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Submonoid.MulAction
import AbstractCryptography.Refinement.Basic

/-!
# The non-expanding pseudo-metric (MauRen11 §2.2, Def 3; MauRen16 Def 2)

MauRen16 **Definition 2**: "A metric `d` on `Φ` is called **non-expanding** if
`d(αR, αS) ≤ d(R, S)` for all `α` and `d(Rβ, Sβ) ≤ d(R, S)` for all `β`."
MauRen11 **Definition 2** gives the same for the interface-indexed algebra, as
eq. (4) `d(αⁱR, αⁱS) ≤ d(R, S)` alongside eq. (3)
`d(R‖R′, S‖S′) ≤ d(R, S) + d(R′, S′)`: "they state that the pseudo-metric is
non-expanding in the sense that `d(R, S)` does not increase if one puts a
resource `T` in parallel to `R` and `S`, or if one connects a converter to
the same interface of `R` and `S`."

The two halves are separate `Prop` mixins over `edist`
(`PseudoEMetricSpace`).
-/

namespace AbstractCryptography

open scoped ENNReal

variable {Sigma Φ : Type*}

/-- The inequality `edist R S ≤ ε`.  In a pseudo-emetric, radius zero need
not imply equality without an explicit point-separation hypothesis. -/
@[reducible] def WithinEDistance [PseudoEMetricSpace Φ]
    (ε : ℝ≥0∞) (R S : Φ) : Prop :=
  edist R S ≤ ε

/-- Scalar closeness, backed by `WithinEDistance`. -/
scoped notation:50 R " ≈[" ε "] " S:51 => WithinEDistance ε R S

/-- MauRen16 Definition 2, the converter clauses: "A metric `d` on `Φ` is called
**non-expanding** if `d(αR, αS) ≤ d(R, S)` for all `α`" — equivalently
Maurer11 Definition 2 eq. (4), "`d(αⁱR, αⁱS) ≤ d(R, S)` for all `i ∈ I`,
`R, S ∈ Φ` and `α ∈ Σ`".  Here: every `c : Sigma` acts as a `1`-Lipschitz map.

**Both of Definition 2's clauses, not one.**  MauRen16 states it two-sidedly —
`d(αR, αS) ≤ d(R, S)` for all `α` *and* `d(Rβ, Sβ) ≤ d(R, S)` for all `β` —
because it pictures a two-interface resource with Alice left and Eve right.
This class quantifies over *every* `c : Sigma`, and in the interface-indexed
model both `αR` and `Rβ` are actions of elements of the one monoid `Sigma`
(`Pi.mulSingle` at a left- resp. right-face interface), so the β-clause is the
same universally quantified statement, not a second axiom.  A carrier that
keeps left and right attachment in *distinct* monoids (the `eL`/`eR` pair of
`Specification.Outbound`) owes the β-clause separately; no such statement is
made in this file. -/
class IsNonexpandingSMul (Sigma Φ : Type*) [PseudoEMetricSpace Φ] [SMul Sigma Φ] : Prop where
  lipschitz_smul (c : Sigma) : LipschitzWith 1 (fun x : Φ => c • x)

theorem edist_smul_le [PseudoEMetricSpace Φ] [SMul Sigma Φ] [IsNonexpandingSMul Sigma Φ]
    (c : Sigma) (x y : Φ) : edist (c • x) (c • y) ≤ edist x y := by
  simpa using (IsNonexpandingSMul.lipschitz_smul (Φ := Φ) c).edist_le_mul x y

/-- **MauRen16 §4.2, the remark following Lemma 5** — used there, never stated:
"Note that `πRβ ≈ᵋ Sσβ` due to the non-expanding property of the
pseudo-metric."  Equation (3)'s closeness `πR ≈ᵋ Sσ` survives attaching a
further converter `β` to both sides, so a statement proved with a simulator is
not destroyed by whatever the environment does afterwards.  This is the one
place §4.2 actually spends Definition 2, and until now it appeared only
inline, as `edist_smul_le σ` inside `Relaxation.star_construct_eps` and
`Indifferentiable.trans`.

**Why one monoid suffices.**  The paper writes the appended converter on the
right (`Rβ`) because it pictures a two-interface resource with Alice on the
left and Eve on the right.  In the homogeneous, interface-addressed rendering
used here, `αR` and `Rβ` are both actions of elements of the *same* converter
monoid — the interface is a component of the element, not a side of the
juxtaposition — so appending `β` to the composite `πR` is the action of
`β * π`, and Definition 2's β-clause is its α-clause instantiated at that
element rather than a second axiom (see the class docstring above).  Hence
`IsNonexpandingSMul`, which quantifies over every `c : Sigma`, is the whole
hypothesis.  The one carrier where left and right attachment are genuinely
distinct monoids is `Specification.Outbound`'s `eL`/`eR` pair, which imports
no metric; that residue is the one recorded above. -/
theorem edist_mul_smul_le_of_edist_le [Monoid Sigma] [MulAction Sigma Φ]
    [PseudoEMetricSpace Φ] [IsNonexpandingSMul Sigma Φ]
    {π σ : Sigma} {R S : Φ} {ε : ℝ≥0∞} (h : edist (π • R) (σ • S) ≤ ε)
    (β : Sigma) :
    edist ((β * π) • R) ((β * σ) • S) ≤ ε := by
  rw [mul_smul, mul_smul]
  exact (edist_smul_le β _ _).trans h

/-- MauRen11 Definition 3: "A pseudo-metric `δ` for a set `Ω` with operation
`‖` is called **`‖`-non-expanding** if `δ(a‖a′, b‖b′) ≤ δ(a, b) + δ(a′, b′)`
for all `a, a′, b, b′ ∈ Ω`."

"As an example, let `Ω` be the set of probability distributions, with `P‖P′`
defined as the product distribution between `P` and `P′`.  Then the
statistical distance is `‖`-non-expanding." -/
class IsNonexpandingPar (Φ : Type*) [PseudoEMetricSpace Φ] [Par Φ] : Prop where
  edist_par_par_le (a a' b b' : Φ) : edist (a ∥ b) (a' ∥ b') ≤ edist a a' + edist b b'

export IsNonexpandingPar (edist_par_par_le)

section Par

variable [PseudoEMetricSpace Φ] [Par Φ] [IsNonexpandingPar Φ]

/-- Fn. 9: "Note that the condition is equivalent to `δ(a‖c, b‖c) ≤ δ(a, b)`
and `δ(c‖a, c‖b) ≤ δ(a, b)` for all `a, b, c ∈ Ω`, which could be used as an
alternative definition of `‖`-non-expanding."  This is the first half. -/
theorem edist_par_left_le (a a' b : Φ) : edist (a ∥ b) (a' ∥ b) ≤ edist a a' := by
  simpa [edist_self] using edist_par_par_le a a' b b

/-- Fn. 9, second half: "`δ(c‖a, c‖b) ≤ δ(a, b)` for all `a, b, c ∈ Ω`." -/
theorem edist_par_right_le (a b b' : Φ) : edist (a ∥ b) (a ∥ b') ≤ edist b b' := by
  simpa [edist_self] using edist_par_par_le a a b b'

end Par

/-- The `1`-Lipschitz endomorphisms of a pseudo-emetric space form a
submonoid of `Function.End`.  A converter's action is "a mapping `Φ → Φ`"
(LiuMau20 §2.3), and MauRen16 Definition 2 asks that mapping to be
non-expanding, so these are the converters that definition admits. -/
def nonexpandingEnd (α : Type*) [PseudoEMetricSpace α] : Submonoid (Function.End α) where
  carrier := {f | LipschitzWith 1 f}
  one_mem' := LipschitzWith.id
  mul_mem' {f g} hf hg := by simpa using hf.comp hg

/-- Tautologically, the nonexpanding endomorphisms act non-expandingly. -/
instance (α : Type*) [PseudoEMetricSpace α] :
    IsNonexpandingSMul (nonexpandingEnd α) α :=
  ⟨fun c => c.2⟩

end AbstractCryptography
