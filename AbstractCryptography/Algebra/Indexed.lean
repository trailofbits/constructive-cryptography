/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Logic.Equiv.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The interface-indexed resource algebra

The index-varying layer: a resource is indexed by its free interface type, and
parallel composition exposes both components' interfaces through a sum, so
`R ‖ S` has interface type `I ⊕ J`.  Associativity and commutativity hold
modulo interface relabelling.

This is the shape MauRen11 Definition 14 leaves implicit.  Its footnote 20
defers the addressing mechanism that merges two `i`-interfaces into one, which
is exactly what keeps that paper's `‖` inside a fixed `Φ`.  Jost §2.2 and
Liu-Zhang §3.3.2 supply the addressing, and these classes are the result.

## Rendering

The algebra is split into small mixins over the type family `Res`, matching the
unbundled treatment of the fixed-interface algebra in
`AbstractCryptography.Algebra.Attachment` and `AbstractCryptography.Metric.Nonexpansion`:

* `IndexedPar Res` carries only the *algebraic* data — `par`, `relabel`,
  `empty` and their laws.  A consumer that never measures resources needs
  nothing else.
* `IsNonexpandingIndexedPar Res` is the separate *metric* mixin.  The metric
  itself is Mathlib's, one `PseudoEMetricSpace` per fibre, so `edist_self`,
  `edist_comm` and `edist_triangle` are inherited rather than restated; the
  mixin adds exactly the two laws that are about the algebra, MauRen11
  Definition 3 / eq. (3) non-expansion of `‖` and invariance of the distance
  under relabelling.

Two consequences of that choice are load-bearing downstream:

* the distance takes values in `ℝ≥0∞`, so `⊤` ("no bound", the vacuous
  distinguisher class) is expressible — it is not in `ℝ≥0`;
* the fibres are **pseudo**-emetric spaces, so `edist R S = 0` does not force
  `R = S`.  Zero distance is behavioural equivalence, and the carrier is
  quotiented by it only downstream.

## References

- Maurer-Renner, *Abstract Cryptography* (2011), Definition 14 and footnote 20;
  Definition 3 and eq. (3) for `‖`-non-expansion
- Matt, Maurer, Portmann, Renner, Tackmann, *Algebraic Theory of Systems*
  (2018), Definition 3.1
-/

namespace AbstractCryptography

universe u v

/-- Parallel composition with explicit interface accounting.

A resource is indexed by its free interface type, and parallel composition
exposes the interfaces of both components through a sum type.  This matches the
system algebra shape in Matt--Maurer--Portmann--Renner--Tackmann 2018,
Definition 3.1: systems carry interface labels, parallel composition combines
disjoint interfaces, and associativity/commutativity hold up to interface
relabelling.

The fixed-interface specialization — one `Φ`, one interface set — is
`AbstractCryptography.Par` together with the `Monoid`/`MulAction` attachment surface
of `AbstractCryptography.Algebra.Attachment`.  Use this indexed layer when the interface
set changes across parallel composition. -/
class IndexedPar (Res : Type u → Type v) where
  /-- Parallel composition exposes the left and right interfaces through `Sum`. -/
  par : {I J : Type u} → Res I → Res J → Res (I ⊕ J)
  /-- Relabel the free interfaces of a resource along an equivalence. -/
  relabel : {I J : Type u} → (I ≃ J) → Res I → Res J
  /-- The empty resource, the unit for parallel composition. -/
  empty : Res PEmpty
  /-- Relabelling by the identity equivalence does not change the resource. -/
  relabel_refl : ∀ {I : Type u} (R : Res I), relabel (Equiv.refl I) R = R
  /-- Relabelling composes functorially. -/
  relabel_trans : ∀ {I J K : Type u} (e₁ : I ≃ J) (e₂ : J ≃ K) (R : Res I),
    relabel e₂ (relabel e₁ R) = relabel (e₁.trans e₂) R
  /-- Associativity of parallel composition, up to the canonical sum relabelling. -/
  par_assoc : ∀ {I J K : Type u} (R : Res I) (S : Res J) (T : Res K),
    relabel (Equiv.sumAssoc I J K) (par (par R S) T) = par R (par S T)
  /-- Commutativity of parallel composition, up to the canonical sum relabelling. -/
  par_comm : ∀ {I J : Type u} (R : Res I) (S : Res J),
    relabel (Equiv.sumComm I J) (par R S) = par S R
  /-- Left unit law for parallel composition. -/
  par_empty_left : ∀ {I : Type u} (R : Res I),
    relabel (Equiv.emptySum PEmpty I) (par empty R) = R
  /-- Right unit law for parallel composition. -/
  par_empty_right : ∀ {I : Type u} (R : Res I),
    relabel (Equiv.sumEmpty I PEmpty) (par R empty) = R

/-! The fields are deliberately **not** `export`ed.  `AbstractCryptography` already
owns `Par.par` and `IsNonexpandingPar.edist_par_par_le` as short names in that
namespace; exporting the indexed homonyms would make both ambiguous for every
file that does `open AbstractCryptography`.  Write `IndexedPar.par`, or `open
IndexedPar` locally. -/

namespace IndexedPar

variable {Res : Type u → Type v} [IndexedPar Res]

/-- Relabelling along `e` and then along `e.symm` is the identity. -/
@[simp] theorem relabel_symm_relabel {I J : Type u} (e : I ≃ J) (R : Res I) :
    relabel e.symm (relabel e R) = R := by
  rw [relabel_trans, Equiv.self_trans_symm, relabel_refl]

/-- Relabelling along `e.symm` and then along `e` is the identity. -/
@[simp] theorem relabel_relabel_symm {I J : Type u} (e : I ≃ J) (R : Res J) :
    relabel e (relabel e.symm R) = R := by
  rw [relabel_trans, Equiv.symm_trans_self, relabel_refl]

/-- Relabelling is a bijection between fibres: the functoriality laws make
`relabel e` and `relabel e.symm` mutually inverse. -/
@[simps] def relabelEquiv {I J : Type u} (e : I ≃ J) : Res I ≃ Res J where
  toFun := relabel e
  invFun := relabel e.symm
  left_inv R := relabel_symm_relabel e R
  right_inv R := relabel_relabel_symm e R

end IndexedPar

/-! ## The metric mixin

MauRen11 **Definition 3**: "A pseudo-metric `δ` for a set `Ω` with operation
`‖` is called **`‖`-non-expanding** if `δ(a‖a′, b‖b′) ≤ δ(a, b) + δ(a′, b′)`
for all `a, a′, b, b′ ∈ Ω`" — eq. (3) of Definition 14's metric half, here on
the index-varying carrier, together with the statement that relabelling an
interface is not something a distinguisher can see. -/

/-- The `‖`-non-expansion mixin for an indexed resource algebra, over one
Mathlib `PseudoEMetricSpace` per fibre.

Only the two algebra-facing laws are fields.  `edist_self`, `edist_comm` and
`edist_triangle` come from `PseudoEMetricSpace`, and the `ℝ≥0∞` codomain keeps
`⊤` available as "no bound". -/
class IsNonexpandingIndexedPar (Res : Type u → Type v)
    [∀ I : Type u, PseudoEMetricSpace (Res I)] [IndexedPar Res] : Prop where
  /-- MauRen11 Definition 3 / eq. (3): parallel composition is non-expanding. -/
  edist_par_par_le : ∀ {I J : Type u} (R R' : Res I) (S S' : Res J),
    edist (IndexedPar.par R S) (IndexedPar.par R' S') ≤ edist R R' + edist S S'
  /-- Relabelling interfaces is invisible to the distance, i.e. `relabel e` is
  an isometry between fibres.  (Stated on `edist` rather than as Mathlib's
  `Isometry`, which lives in the real-valued metric hierarchy this file
  deliberately does not import; `fun R S => edist_relabel e R S` is the
  `Isometry` proof wherever that import is already present.) -/
  edist_relabel : ∀ {I J : Type u} (e : I ≃ J) (R S : Res I),
    edist (IndexedPar.relabel e R) (IndexedPar.relabel e S) = edist R S

namespace IsNonexpandingIndexedPar

open IndexedPar

variable {Res : Type u → Type v} [∀ I : Type u, PseudoEMetricSpace (Res I)]
  [IndexedPar Res] [IsNonexpandingIndexedPar Res]

/-- MauRen11 fn. 9: the non-expansion condition is equivalent to
`δ(a‖c, b‖c) ≤ δ(a, b)` and `δ(c‖a, c‖b) ≤ δ(a, b)`.  This is the first
half. -/
theorem edist_par_left_le {I J : Type u} (R R' : Res I) (S : Res J) :
    edist (par R S) (par R' S) ≤ edist R R' := by
  simpa using edist_par_par_le R R' S S

/-- MauRen11 fn. 9, second half. -/
theorem edist_par_right_le {I J : Type u} (R : Res I) (S S' : Res J) :
    edist (par R S) (par R S') ≤ edist S S' := by
  simpa using edist_par_par_le R R S S'

/-! ### Behavioural equivalence

Zero distance, not equality: the fibres are pseudo-emetric, so `edist R S = 0`
is a genuine equivalence relation on resources that need not be equal.  The
`PseudoEMetricSpace` structure already makes it reflexive (`edist_self`),
symmetric (`edist_comm`) and transitive (`edist_triangle`); these two lemmas
add that the algebra respects it. -/

/-- Relabelling preserves behavioural equivalence. -/
theorem edist_relabel_eq_zero {I J : Type u} (e : I ≃ J) {R S : Res I}
    (h : edist R S = 0) : edist (relabel e R) (relabel e S) = 0 := by
  rw [edist_relabel, h]

/-- Parallel composition preserves behavioural equivalence. -/
theorem edist_par_eq_zero {I J : Type u} {R R' : Res I} {S S' : Res J}
    (hR : edist R R' = 0) (hS : edist S S' = 0) :
    edist (par R S) (par R' S') = 0 :=
  le_antisymm (by simpa [hR, hS] using edist_par_par_le R R' S S') (zero_le _)

end IsNonexpandingIndexedPar

end AbstractCryptography
