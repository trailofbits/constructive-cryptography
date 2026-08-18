/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Algebra.Group.Defs

/-!
# Abstract constructions (MauRen11 §3)

"A central paradigm in any constructive discipline, for example in
software design, the construction of machines, and also in security
engineering and cryptography, is to construct a complex system from
simpler component systems, which each may consist of yet simpler
component systems, and so on.  This important iterative construction
paradigm is sometimes called **step-wise refinement**."

The section in the paper's order: Definition 5 (component set,
constructor set), Definition 6 (reduction), Definition 7 (serially
composable, context-insensitive, generally composable), the parallel
composability that (i)–(iii) together imply, and — from Appendix A —
Definition 19 and **Theorem 3**, represented here in two formal
interpretations: the law-free derived-chain forward theorem
`soundForDerivedChainStepwiseRefinement_of_isGenerallyComposable` and, under
the two serial unit laws, the exact repaired child-parallel characterization
`isGenerallyComposable_and_red_par_par_iff_soundForChildParallelStepwiseRefinement`.

MauRen11 §1.5 places this file's content at **Level 1**: "the most
general notion of a *system* and of the *composition* of systems.  The
composition laws are described by simple algebraic rules."
-/

namespace AbstractCryptography

universe u v w

/-! ## Notation

Definition 5 equips `Γ` with "a (serial composition) operation `∘`, a
(parallel composition) operation `|`, and a special (neutral) element `id`":
here `∘` is `*`, `id` is `1`, and `|` is the `Par` class below.  No equational
law is postulated on `Γ`.

The serial composite is written in function-composition order: Definition 7
(i)'s "`α` first, then `β`", printed `α∘β`, is `β * α` here.  This is §6.2's
reading ("serial composition: `αβ` (or `α ∘ β`) is defined by
`(αβ)ⁱR := αⁱβⁱR`"), and it agrees with MauRen16 Lemma 1 (`π′ ∘ π`), CR18
Lemma 5.1 (`γ′ ∘ γ`), and mathlib's `mul_smul : (β * α) • R = β • (α • R)`.
-/

/-- Definition 5: "A **component set** is a set `Ω` equipped with a (parallel
composition) operation, denoted `‖`.  A **constructor set** `Γ` is a set
equipped with a (serial composition) operation `∘`, a (parallel composition)
operation `|`, and a special (neutral) element `id`."

One class for both `‖` and `|`, carrying no laws.  Fn. 10: "If `‖` is not
associative, appropriate parentheses are required in the expression
`R₁‖⋯‖R_d`."  Fn. 23, on constructors: "Note also that `α‖1 ≠ α`." -/
class Par (α : Type*) where
  /-- Parallel composition. -/
  par : α → α → α

@[inherit_doc] scoped infixl:65 " ∥ " => Par.par

/-- Definition 6: "A **reduction** for a component set `Ω` and a constructor
set `Γ` is a subset of `Ω × Γ × Ω`.  A reduction is often denoted by an
arrow, for example `—→`, as follows: If `(R, α, S)` is in the reduction, then
we write `R —α→ S` and say that `S` can be *reduced to* `R` by `α` or,
equivalently, that `S` can be *realized* (or *constructed*) *from* `R` by
`α`."

"A reduction `—→` for a component set `Ω` and a constructor set `Γ` can
equivalently be interpreted as a collection `{—α→}_{α∈Γ}` of relations on
`Ω`, indexed by elements of `Γ`." -/
class HasReduction (Ω : Type*) (Γ : Type*) where
  /-- The reduction relation: `Red R α S` means `S` is constructed from `R`
  by `α`. -/
  Red : Ω → Γ → Ω → Prop

@[inherit_doc] scoped notation:50 R " —[" α "]→ " S:51 => HasReduction.Red R α S

export HasReduction (Red)

variable {Ω Γ : Type*}

/-- Definition 6: "We write `R —→ S` if there exists an `α ∈ Γ` such that
`R —α→ S`."  `Γ` is explicit: it is not determined by `R` and `S`. -/
def Reduces (Γ : Type*) [HasReduction Ω Γ] (R S : Ω) : Prop :=
  ∃ α : Γ, R —[α]→ S

/-- MauRen11 Definition 6's unlabelled existential reduction, with the
constructor type visible because it cannot be inferred from `R` and `S`.
Thus `R —[∃ Γ]→ S` expands to `Reduces Γ R S`. -/
scoped notation:50 R " —[∃ " Γ "]→ " S:51 => Reduces Γ R S

/-- Definition 7: "A reduction `—→` for `Ω` and `Γ` is called **serially
composable** if the following properties hold for all `R, S, T ∈ Ω` and
`α, β ∈ Γ`." -/
class IsSeriallyComposable (Ω Γ : Type*) [Mul Γ] [One Γ] [HasReduction Ω Γ] : Prop where
  /-- "(i) `R —α→ S ∧ S —β→ T  ⟹  R —α∘β→ T`" — the paper's `α∘β` here
  (first `α`, then `β`) is `β * α` in function-composition order. -/
  red_mul {R S T : Ω} {α β : Γ} : R —[α]→ S → S —[β]→ T → R —[β * α]→ T
  /-- "(ii) `R —id→ R`." -/
  red_one (R : Ω) : R —[(1 : Γ)]→ R

export IsSeriallyComposable (red_mul red_one)

/-- Definition 7: "Furthermore, `Γ` is called **context-insensitive** if

  (iii) `R —α→ S  ⟹  R‖T —α|id→ S‖T ∧ T‖R —id|α→ T‖S`."

"Property (iii) states that `R —α→ S` remains true independently of the
environment or context, i.e., independently of which systems are available in
parallel." -/
class IsContextInsensitive (Ω Γ : Type*) [Par Ω] [One Γ] [Par Γ]
    [HasReduction Ω Γ] : Prop where
  /-- "(iii) `R —α→ S  ⟹  R‖T —α|id→ S‖T` …" -/
  red_par_one {R S : Ω} {α : Γ} (T : Ω) : R —[α]→ S → R ∥ T —[α ∥ (1 : Γ)]→ S ∥ T
  /-- "… `∧ T‖R —id|α→ T‖S`." -/
  red_one_par {R S : Ω} {α : Γ} (T : Ω) : R —[α]→ S → T ∥ R —[(1 : Γ) ∥ α]→ T ∥ S

export IsContextInsensitive (red_par_one red_one_par)

/-- Definition 7: "A reduction that is both serially composable and
context-insensitive is called **generally composable** (or just
**composable**)." -/
class IsGenerallyComposable (Ω Γ : Type*) [Par Ω] [Mul Γ] [One Γ] [Par Γ]
    [HasReduction Ω Γ] : Prop
    extends IsSeriallyComposable Ω Γ, IsContextInsensitive Ω Γ

section Serial

variable [Mul Γ] [One Γ] [HasReduction Ω Γ] [IsSeriallyComposable Ω Γ]

/-- `—→` is reflexive, by (ii). -/
theorem Reduces.refl (R : Ω) : Reduces Γ R R := ⟨1, red_one R⟩

/-- "Property (i) implies transitivity of the relation `—→`." -/
theorem Reduces.trans {R S T : Ω} (h : Reduces Γ R S) (h' : Reduces Γ S T) :
    Reduces Γ R T := by
  obtain ⟨α, hα⟩ := h
  obtain ⟨β, hβ⟩ := h'
  exact ⟨β * α, red_mul hα hβ⟩

end Serial

section Parallel

variable [Par Ω] [Mul Γ] [One Γ] [Par Γ] [HasReduction Ω Γ]
  [IsSeriallyComposable Ω Γ] [IsContextInsensitive Ω Γ]

/-- "Properties (i) to (iii) together imply that the reduction `—→` is
**parallelly composable**, in the following sense:

  `R —α→ S ∧ R′ —α′→ S′  ⟹  R‖R′ —β→ S‖S′`,

where `β = (α|id)(id|α′)`."

Fn. 11: "One could naturally postulate that `(α|id)(id|α′) = α|α′`, but this
is not necessary" — so `β` stays the serial composite, not `α ∥ α′`.

The paper's `β` juxtaposes its two factors; read here as in §6.2, so
`(id|α′)` acts first.  `red_par_left_first` is the other reading. -/
theorem red_par {R R' S S' : Ω} {α α' : Γ} (h : R —[α]→ S) (h' : R' —[α']→ S') :
    R ∥ R' —[(α ∥ 1) * (1 ∥ α')]→ S ∥ S' :=
  red_mul (red_one_par R h') (red_par_one S' h)

/-- Parallel composability with `β = (α|id)(id|α′)` read as Definition 7 (i)
reads `∘`: `(α|id)` first, then `(id|α′)`. -/
theorem red_par_left_first {R R' S S' : Ω} {α α' : Γ}
    (h : R —[α]→ S) (h' : R' —[α']→ S') :
    R ∥ R' —[(1 ∥ α') * (α ∥ 1)]→ S ∥ S' :=
  red_mul (red_par_one R' h) (red_one_par S h')

/-- MauRen11 Definitions 6-7: existential reduction is closed under parallel
composition.  The witness is Definition 7's derived serial chain, not the
literal parallel constructor, which footnote 11 does not postulate. -/
theorem Reduces.par {R R' S S' : Ω}
    (h : Reduces Γ R S) (h' : Reduces Γ R' S') :
    Reduces Γ (R ∥ R') (S ∥ S') := by
  obtain ⟨α, hα⟩ := h
  obtain ⟨α', hα'⟩ := h'
  exact ⟨(α ∥ 1) * (1 ∥ α'), red_par hα hα'⟩

end Parallel

end AbstractCryptography
