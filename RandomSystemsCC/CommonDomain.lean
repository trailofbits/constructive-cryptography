/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical
import RandomSystems.Converter.CommonDomain.Category

set_option autoImplicit false

/-!
# Common-domain Random Systems adapter

This adapter selects the induced distance on the normalized specialization of
Lanzenberger's common-domain carrier and proves that every image-preserving
DDC is non-expanding. Exact and approximate construction, serial composition,
and star relaxation are then the generic
categorical theorems. No monoidal instance is asserted for this fixed-interface
subcategory because this boundary selects no routed parallel operation. Jost
separates the axiomatic algebra from his probabilistic-system presentation and
does not require the common-domain relation. Liu--Maurer's resource model does
not state it.
-/

namespace RandomSystemsCC.CommonDomain

noncomputable section

open RandomSystems.CommonDomain

universe u v

attribute [local instance]
  RandomSystems.CommonDomain.Interface.category

/-- The common-domain resource functor is non-expanding under every arrow of
its source-specific category.

Maurer--Renner 2016, Definition 2 (printed p. 11), calls a metric non-expanding
when “`d(αR, αS) ≤ d(R, S)` for all `α`.” -/
noncomputable instance instIsNonexpanding :
    AbstractCryptography.Categorical.IsNonexpanding
      RandomSystems.CommonDomain.Interface.randomSystems where
  fibreMetric := fun boundary => inferInstanceAs
    (PseudoEMetricSpace
      (ProbabilityRandomSystem
        boundary.unop.query boundary.unop.answer))
  -- Restricted DDC attachment inherits ambient non-expansion.
  edist_map_le converter left right :=
    ProbabilityRandomSystem.edist_apply_le converter.unop left right

end

end RandomSystemsCC.CommonDomain
