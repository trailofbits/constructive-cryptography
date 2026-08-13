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

variable {M Φ : Type*}

/-- The inequality `edist R S ≤ ε`.  In a pseudo-emetric, radius zero need
not imply equality without an explicit point-separation hypothesis. -/
@[reducible] def WithinEDistance [PseudoEMetricSpace Φ]
    (ε : ℝ≥0∞) (R S : Φ) : Prop :=
  edist R S ≤ ε

/-- Scalar closeness, backed by `WithinEDistance`. -/
scoped notation:50 R " ≈[" ε "] " S:51 => WithinEDistance ε R S

/-- MauRen16 Definition 2, the converter half: "A metric `d` on `Φ` is called
**non-expanding** if `d(αR, αS) ≤ d(R, S)` for all `α`" — equivalently
Maurer11 Definition 2 eq. (4), "`d(αⁱR, αⁱS) ≤ d(R, S)` for all `i ∈ I`,
`R, S ∈ Φ` and `α ∈ Σ`".  Here: every `c : M` acts as a `1`-Lipschitz map. -/
class IsNonexpandingSMul (M Φ : Type*) [PseudoEMetricSpace Φ] [SMul M Φ] : Prop where
  lipschitz_smul (c : M) : LipschitzWith 1 (fun x : Φ => c • x)

theorem edist_smul_le [PseudoEMetricSpace Φ] [SMul M Φ] [IsNonexpandingSMul M Φ]
    (c : M) (x y : Φ) : edist (c • x) (c • y) ≤ edist x y := by
  simpa using (IsNonexpandingSMul.lipschitz_smul (Φ := Φ) c).edist_le_mul x y

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
