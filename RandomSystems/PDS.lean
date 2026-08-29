/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DDS
import Probability.Distribution

/-!
# Probabilistic discrete systems

Lanzenberger, Definition 2.14 (printed p. 15): a PDS “is a distribution over
`(X, Y)`-DDS.”

Definition 2.1 (printed p. 11) defines a distribution as “a function
`X : A → ℝ≥0` with finite support.” The Lean carrier is deliberately broader:
it is a signed finite-support law. Nonnegativity and the common-domain clause
are separate predicates; they recover those two clauses of Definition 2.14.
The thesis's standing finiteness and uniform domain-bound assumptions remain
separate hypotheses. Normalization is an additional specialization:
immediately before Definition 2.14 (printed p. 15), Lanzenberger says that the
distributions need not be probability distributions.
-/

namespace RandomSystems

open Probability (Distribution)

universe u v

/-! ## The carrier -/

/-- Lanzenberger, Definition 2.14 (printed p. 15): a PDS “is a distribution
over `(X, Y)`-DDS.” Lean uses the broader signed finite-support carrier and
records nonnegativity, common domain, and the standing finiteness assumptions
separately. -/
abbrev PDS (X : Type u) (Y : Type v) : Type (max u v) :=
  Distribution (System.DDS X Y)

namespace PDS

variable {X : Type u} {Y : Type v}

/-- Lanzenberger, Definition 2.14 (printed p. 15): “all DDS in the support of
`S` have the same domain.”  This existential form records that clause for one
law. -/
class HasFixedDomain (S : PDS X Y) : Prop where
  exists_common : ∃ D : Set (List X), ∀ s ∈ S.support, System.dom s = D

/-- Definition 2.1 (printed p. 11): “A probability distribution is a
distribution `X` with weight 1.” -/
class IsProbability (S : PDS X Y) : Prop where
  nonNeg : S.NonNeg
  weight_eq_one : S.weight = 1

/-- Lanzenberger, Definition 2.14 (printed p. 15): “all DDS in the support of
`S` have the same domain.”  Lean names that domain explicitly so statements
about several laws can require the same `D`; `HasFixedDomain` existentially
packages the one-law form. -/
def HasDomain (S : PDS X Y) (D : Set (List X)) : Prop :=
  ∀ s ∈ S.support, System.dom s = D

/-- The existential and explicitly named forms of Definition 2.14's common
domain clause (printed p. 15) are equivalent for one law. -/
theorem hasFixedDomain_iff_exists_hasDomain {S : PDS X Y} :
    HasFixedDomain S ↔ ∃ D : Set (List X), HasDomain S D :=
  ⟨fun h => h.exists_common, fun h => ⟨h⟩⟩

/-- The degenerate PDS concentrated on one deterministic system. -/
noncomputable def ofDDS (S : System.DDS X Y) : PDS X Y :=
  Finsupp.single S 1

end PDS

end RandomSystems
