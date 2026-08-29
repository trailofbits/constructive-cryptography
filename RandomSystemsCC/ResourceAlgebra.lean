/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical.ResourceAlgebra
import RandomSystems.Converter.RandomSystem.Category

set_option autoImplicit false

/-!
# Resource algebra of query-indexed random systems

This is the sole abstract-layer dependency boundary for query-indexed random
systems.  It selects the proved DDC category, routed ordered parallel,
normalized random-system functor, observational distance, and their
non-expansion laws as one `ResourceAlgebra`.  No symmetry is asserted.
-/

namespace RandomSystemsCC

noncomputable section

open CategoryTheory
open RandomSystems.Ambient

universe u v

/-- Query-indexed random systems, DDC attachment, and routed ordered parallel
instantiate the carrier-independent resource algebra.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “A converter α, when applied
as an interface i of a resource, induces a function Φ → Φ : R → αⁱR.”

Jost, Section 2.2.2 (printed pp. 17--18): “A finite set of resources with
disjoint interface sets can be viewed as a single one.” Jost proves attachment
locality but does not state a monoidal category or require symmetry.

Liu--Maurer, Section 3.2 (printed p. 9), says that independent resources may be
formed into their “parallel composition”; Section 3.3 (printed pp. 10--11)
defines a converter with inside and outside interfaces and its application to
a resource. The object, attachment, and parallel equations here specialize to
that synchronous conditional-probability model, although this finite-support
deterministic-mixture carrier is not the Liu--Maurer carrier. Lanzenberger
defines fixed-interface DDSs, common-domain PDS equivalence, and `Adv`; these
supply the separate common-domain specialization, not the ambient DDC category
or additional `ResourceAlgebra` axioms. -/
noncomputable instance instResourceAlgebra :
    AbstractCryptography.Categorical.ResourceAlgebra
      RandomSystems.Ambient.Interface.{u, v}
      RandomSystems.Ambient.Interface.randomSystems where
  -- Select the proved observational pseudo-emetric in each interface fibre.
  fibreMetric := fun boundary => inferInstanceAs
    (PseudoEMetricSpace
      (RandomSystems.Ambient.RandomSystem boundary.unop))
  -- DDC attachment is non-expanding by finite DDE observation factorization.
  edist_map_le converter left right :=
    RandomSystems.Ambient.RandomSystem.edist_apply_le
      converter.unop left right
  -- Ordered routed parallel supplies the selected lax-monoidal resource map.
  laxMonoidal :=
    RandomSystems.Ambient.Interface.randomSystemsLaxMonoidal
  -- Independent ordered parallel is jointly non-expanding.
  parallel_nonexpanding := fun _ _ left left' right right' =>
    RandomSystems.Ambient.RandomSystem.edist_parallel_le
      left left' right right'

end

end RandomSystemsCC
