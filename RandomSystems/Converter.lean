/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Category
import RandomSystems.Converter.Filter
import RandomSystems.Converter.BoundedInnerQueries
import RandomSystems.Converter.RandomSystem.Category
import RandomSystems.Converter.CommonDomain
import RandomSystems.Converter.CommonDomain.Category

/-!
# Deterministic discrete converters

This optional root provides the query-indexed interface category, DDSs and
DDCs as functions on complete attempted histories, attachment, forwarding,
serial composition, ordered routed parallel composition, normalized
finite-support PDSs, observational random systems, and their non-expanding DDC
action. It also exposes the faithful embedding of the normalized
specialization of Lanzenberger's fixed-interface common-domain carrier and the
DDCs that preserve its image.

Jost, immediately before Definition 2.2.2 (printed p. 17), permits a converter
to make “a bounded number of queries to the inside interfaces.” The DDC carrier
below realizes that interface-changing converter shape as a complete-history
function; branch-finiteness is the explicit Lean generalization of Jost's numerical
bound. Liu--Maurer's component converters are obtained by fixing the relevant
outer and inner interfaces. Neither source requires a second resource carrier
or a second attachment operation.

The fixed-interface `RandomSystems` root does not import this extension.
-/
