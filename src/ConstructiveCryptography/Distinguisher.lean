import Mathlib.Data.ENNReal.Real

set_option autoImplicit false

/-!
# Distinguishers, decisions and admission

A distinguisher `d` on an interface `A` is tested by its decision evaluation on a resource
`R`, read as `Pr[d(R) = 1]`, and its advantage between two resources is the absolute
difference of these evaluations:

```text
advantage d R S = |probability d R - probability d S|      ∈ ENNReal
```

The evaluations are abstract reals: the class asserts no range `[0, 1]`, and needs no
category, metric or efficiency notion. Which tests a security statement quantifies over is a
separate choice, made by `AdmissibleDistinguishers`; it makes no closure claim. Absorbing a
converter into a distinguisher, and the closure a particular reduction needs, are in
`CryptographicAlgebra.DistinguisherAction`.

`DistinguisherAdvantage` is the more general per-test pseudo-distance record consumed by the
substitution calculus, with an arbitrary advantage function. The decision evaluations give
one instance of it for each admitted set.

## Main definitions

* `CryptographicAlgebra.DistinguisherAdvantage`: admitted tests and a per-test
  pseudo-distance
* `Distinguishers I Phi D`: decision evaluation of distinguishers `D A` on resources `Phi A`
* `AdmissibleDistinguishers I D`: the selected tests on each interface;
  `AdmissibleDistinguishers.all` admits every test, for local installation only
* `Distinguishers.advantage`: absolute decision advantage
* `Distinguishers.distinguisherAdvantage admitted`: the decision-derived
  `DistinguisherAdvantage`

Sources: CR18, Definition 4.7 (printed p. 91), takes the signed performance; this library
takes the absolute value, as Banfi, §2.3.3 (printed p. 16).
-/

namespace ConstructiveCryptography

universe u v w x

namespace CryptographicAlgebra

/-- A typed family of admissible distinguishers and its advantage function.

Banfi 2023, Section 2.3.3 (printed p. 16) defines concrete substitution by
requiring `Δ_D(S, T) ≤ ε(D)` “for all poly-time (distinguishing) programs.”
The three advantage laws below are exactly the symmetry and triangle facts
used by the substitution and reduction-relaxation calculations. The laws hold for every
distinguisher, admitted or not. -/
structure DistinguisherAdvantage
    -- `C` is the type of interfaces; no category structure is needed here.
    (C : Type u)
    -- `Systems A` is the type of resources compared on `A : C`; `Distinguisher A` contains all
    -- candidate distinguishers on `A`, admitted or not.
    (Systems : C → Type w) (Distinguisher : C → Type x) where
  /-- The distinguishers admitted at each resource interface, Banfi's “poly-time” programs: the
  class over which `SubstitutesWithin` quantifies. It is an arbitrary subset, possibly empty;
  efficiency is only the caller's choice of this set, and no closure property is assumed. -/
  admissible : ∀ A, Set (Distinguisher A)
  /-- The distinguishing advantage `Δ_D(S, T)` of `D : Distinguisher A` between two resources
  `S T : Systems A` in one fibre, possibly `∞`. It is an abstract pseudo-distance per
  distinguisher, not assumed bounded by `1` or derived from a concrete experiment; advantage
  `0` for every admitted `D` does not make `S` and `T` equal. -/
  advantage : ∀ A, Distinguisher A → Systems A → Systems A → ENNReal
  /-- A distinguisher has zero advantage between identical resources. -/
  advantage_self : ∀ A distinguisher resource,
    advantage A distinguisher resource resource = 0
  /-- Distinguishing advantage is symmetric in the compared resources. -/
  advantage_symm : ∀ A distinguisher left right,
    advantage A distinguisher left right = advantage A distinguisher right left
  /-- Distinguishing advantage satisfies the triangle inequality. -/
  advantage_triangle : ∀ A distinguisher left middle right,
    advantage A distinguisher left right ≤
      advantage A distinguisher left middle + advantage A distinguisher middle right


end CryptographicAlgebra

/-- Decision evaluations of distinguishers. CR18 §4.5.2 (printed p. 91) starts with a
function `κ : D × O → {0, 1}`; here its output-1 probability is already averaged.

The evaluation is an abstract real number. Instances such as typed distinguishers return
genuine probabilities, but the class has no range axiom, so the advantage laws hold for any
real evaluation. -/
class Distinguishers
    -- `I` contains interfaces; `Phi A` contains resources presenting interface `A : I`.
    (I : Type u) (Phi : I → Type v)
    -- `D A` contains distinguishers on `A`; the selected evaluation instance determines `D`.
    (D : outParam (I → Type w)) where
  /-- `probability d R` is the decision evaluation of `d` on `R`, read as `Pr[d(R) = 1]`. -/
  probability : ∀ {A : I}, D A → Phi A → ℝ

/-- The selected admitted tests, with no efficiency or converter-closure assertion.
Banfi §2.3.3 (printed p. 16) restricts to “poly-time (distinguishing) programs”. Closure
under a converter is proved per reduction (`AdmissibleDistinguishers.ClosedUnder`). -/
class AdmissibleDistinguishers
    -- `I` contains interfaces and `D A` contains candidate distinguishers on `A : I`.
    (I : Type u) (D : I → Type w) where
  /-- `admissible A` selects the tests quantified over by the security statement. -/
  admissible : ∀ A : I, Set (D A)

namespace AdmissibleDistinguishers

/-- Admit every test: `admissible A = Set.univ`. A value, not an instance: a statement over all
distinguishers installs it locally, and importing it selects no security model. -/
@[reducible] def all {I : Type u} {D : I → Type w} : AdmissibleDistinguishers I D where
  admissible _ := Set.univ

end AdmissibleDistinguishers

namespace Distinguishers

-- `I` contains interfaces, `Phi A` resources and `D A` distinguishers on `A : I`, with the
-- selected decision evaluation.
variable {I : Type u} {Phi : I → Type v} {D : I → Type w} [Distinguishers I Phi D]

/-- Absolute advantage: `|Pr[d(R) = 1] - Pr[d(S) = 1]|`, in `ENNReal` for additive budgets.
Banfi §2.3.3 (printed p. 16) uses “|Pr[Dκ(Sκ) = 0] − Pr[Dκ(Tκ) = 0]|”; taking output 1
instead gives the same absolute difference for genuine probability evaluations. Here
`d : D A` is the one test applied to both resources `R S : Phi A`. -/
noncomputable def advantage {A : I} (d : D A) (R S : Phi A) : ENNReal :=
  ENNReal.ofReal |probability d R - probability d S|

/-- The decision-derived `DistinguisherAdvantage`: `admitted A` is the set of tests quantified
over on interface `A`, and the advantage is `Distinguishers.advantage`, whose zero, symmetry
and triangle laws follow from those of `|x - y|` on `ℝ`. No absorption or resource metric is
assumed. -/
noncomputable def distinguisherAdvantage (admitted : ∀ A : I, Set (D A)) :
    CryptographicAlgebra.DistinguisherAdvantage I Phi D where
  admissible := admitted
  advantage _ d R S := advantage d R S
  advantage_self _ d R := by simp only [advantage, sub_self, abs_zero, ENNReal.ofReal_zero]
  advantage_symm _ d R S := by rw [advantage, advantage, abs_sub_comm]
  advantage_triangle _ d R S T := by
    rw [advantage, advantage, advantage,
      ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

end Distinguishers

end ConstructiveCryptography
