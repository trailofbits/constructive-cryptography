/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Specification.ConstructorClass

/-!
# Cost-bounded constructor classes (MauRen16 §2.1, §3.5; CR18 §4.4.7)

MauRen16 §2.1 (printed p. 4) admits the constructor set `Γ` "possibly
restricted in terms of efficiency or implementation cost", and §3.5 (printed
pp. 9–10) lists the *efficiency-bounded* model as one of four instantiations of
that parameter: "If, for some notion of efficiency, efficient computing power
is considered irrelevant, then one can consider `Σ` to be the set of
efficiently implementable converter systems."  `Specification.ConstructorClass`
supplies `Γ` itself and the two monotonicity laws; this module supplies the
one family of classes those laws were stated for, and nothing else.

`costBounded γ c` is the class of converters of cost at most `c`.  Everything
below is the chain of construction-hardness facts that the bound `c` alone
carries: a *larger* budget proves more constructions
(`Constructible.mono_costBounded`), and an impossibility proved against the
larger budget is the stronger statement (`Unconstructible.mono_costBounded`) —
both by the landed `mono_constructors` at the inclusion `costBounded_mono`.

## Why the cost function is a parameter

CR18 §4.4.7 (printed p. 84) declines to fix a computational model: the cost of
an algorithm is left to the modeling decision, exactly as MauRen16 §3.5 leaves
the converter set to it.  So `γ : Sigma → ℕ∞` is a parameter here and is never
specialized: no complexity measure, no machine model, and no asymptotics enter.
`ℕ∞` rather than `ℕ` because a converter may have no finite cost at all, and
`⊤` is then the budget that admits everything (`costBounded_top`).

This module deliberately builds **no** performance function and **no** problem
object: CR18 §4.1's `Problem`/performance layer is a separate item, and the
half of the source's monotonicity statement that speaks about performance
(`p̄′`, `ρ′`) is content-empty without it.

## References

* [U. Maurer, R. Renner, *From Indifferentiability to Constructive
  Cryptography (and Back)*, TCC 2016-B][MauRen16], §2.1 and §3.5.
* [U. Maurer, *Cryptography Foundations* lecture notes][CR18], §4.4.7.
-/

namespace AbstractCryptography

variable {Sigma Φ : Type*}

/-- MauRen16 §3.5's efficiency-bounded converter class at an explicit budget:
the converters whose cost `γ` does not exceed `c`.

Both the cost function and the budget are parameters — see the module
docstring for why the cost function is never specialized here. -/
def costBounded (γ : Sigma → ℕ∞) (c : ℕ∞) : Set Sigma := {s | γ s ≤ c}

@[simp] theorem mem_costBounded {γ : Sigma → ℕ∞} {c : ℕ∞} {s : Sigma} :
    s ∈ costBounded γ c ↔ γ s ≤ c := Iff.rfl

/-- A larger budget admits more converters. -/
theorem costBounded_mono {γ : Sigma → ℕ∞} {c c' : ℕ∞} (h : c ≤ c') :
    costBounded γ c ⊆ costBounded γ c' :=
  fun _ hs => le_trans hs h

theorem monotone_costBounded (γ : Sigma → ℕ∞) : Monotone (costBounded γ) :=
  fun _ _ h => costBounded_mono h

/-- The unbounded budget admits everything: MauRen16 §3.5's
information-theoretic model, where "the converter set includes all systems,
regardless of the computational complexity of implementing them", is the case
`c = ⊤` of this family. -/
@[simp] theorem costBounded_top (γ : Sigma → ℕ∞) :
    costBounded γ ⊤ = (Set.univ : Set Sigma) :=
  Set.eq_univ_of_forall fun _ => mem_costBounded.mpr le_top

section Constructions

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- **A larger budget proves more constructions.**  `Constructible.mono_constructors`
at the inclusion of cost-bounded classes: the same constructor witnesses both
statements, so nothing is asked of `γ`. -/
theorem Constructible.mono_costBounded {γ : Sigma → ℕ∞} {c c' : ℕ∞} (h : c ≤ c')
    {𝓡 𝒮 : Specification Φ} (hc : 𝓡 —[∈ costBounded γ c]→ 𝒮) :
    𝓡 —[∈ costBounded γ c']→ 𝒮 :=
  Constructible.mono_constructors (costBounded_mono h) hc

/-- **An impossibility against a larger budget is the stronger statement.**  The
impossibility side is antitone in the budget exactly where the possibility side
is monotone. -/
theorem Unconstructible.mono_costBounded {γ : Sigma → ℕ∞} {c c' : ℕ∞} (h : c ≤ c')
    {𝓡 𝒮 : Specification Φ} (hu : Unconstructible (costBounded γ c') 𝓡 𝒮) :
    Unconstructible (costBounded γ c) 𝓡 𝒮 :=
  Unconstructible.mono_constructors (costBounded_mono h) hu

/-- A construction admitted at a budget is a construction admitted at the
unbounded budget — the information-theoretic reading of a cost-bounded
statement. -/
theorem Constructible.mono_costBounded_top {γ : Sigma → ℕ∞} {c : ℕ∞}
    {𝓡 𝒮 : Specification Φ} (hc : 𝓡 —[∈ costBounded γ c]→ 𝒮) :
    𝓡 —[∈ costBounded γ ⊤]→ 𝒮 :=
  Constructible.mono_costBounded le_top hc

end Constructions

/-- MauRen16 footnote 6's closure requirement, at an explicit budget:
"converters `α` and `β` from this particular set `Σ` can be composed to a new
converter, say `α ∘ β`, and this composition is closed".  The two clauses are
exactly what a `Submonoid` needs, and they are hypotheses rather than
consequences: for a fixed budget, closure under composition is a property of
the cost function, not of the bound.

`Constructible.trans` (`Specification.ConstructorClass`) is stated over a
`Submonoid` for precisely this reason, and this is the constructor that feeds
it a cost-bounded class. -/
def costBoundedSubmonoid [Monoid Sigma] (γ : Sigma → ℕ∞) (c : ℕ∞)
    (one_mem : γ 1 ≤ c) (mul_mem : ∀ a b : Sigma, γ a ≤ c → γ b ≤ c → γ (a * b) ≤ c) :
    Submonoid Sigma where
  carrier := costBounded γ c
  one_mem' := one_mem
  mul_mem' := fun {a b} ha hb => mul_mem a b ha hb

@[simp] theorem coe_costBoundedSubmonoid [Monoid Sigma] {γ : Sigma → ℕ∞} {c : ℕ∞}
    {one_mem : γ 1 ≤ c} {mul_mem : ∀ a b : Sigma, γ a ≤ c → γ b ≤ c → γ (a * b) ≤ c} :
    (costBoundedSubmonoid γ c one_mem mul_mem : Set Sigma) = costBounded γ c := rfl

/-- **MauRen16 §4.1 Lemma 1 at a cost-bounded class**: construction statements
compose, and the composite constructor stays within the budget.  The closure
hypotheses of `costBoundedSubmonoid` are where MauRen16 footnote 6's
requirement actually bites — on a bare `costBounded γ c` the statement is false
in general. -/
theorem Constructible.trans_costBounded [Monoid Sigma] [MulAction Sigma Φ]
    {γ : Sigma → ℕ∞} {c : ℕ∞} {one_mem : γ 1 ≤ c}
    {mul_mem : ∀ a b : Sigma, γ a ≤ c → γ b ≤ c → γ (a * b) ≤ c}
    {𝓡 𝒮 𝒯 : Specification Φ}
    (h : 𝓡 —[∈ costBounded γ c]→ 𝒮) (h' : 𝒮 —[∈ costBounded γ c]→ 𝒯) :
    𝓡 —[∈ costBounded γ c]→ 𝒯 :=
  Constructible.trans (Γ := costBoundedSubmonoid γ c one_mem mul_mem) h h'

end AbstractCryptography
