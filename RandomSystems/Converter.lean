/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Filter
import RandomSystems.Converter.BoundedInnerQueries
import RandomSystems.Converter.RandomSystemAction
import RandomSystems.Converter.CommonDomain

/-!
# Deterministic discrete converters and their random-system action

This optional root provides query-indexed interfaces, DDSs and DDCs as
functions on complete attempted histories, deterministic attachment,
forwarding, serial composition, cumulative random systems, and the scoped
contravariant DDC action. It also exposes the faithful embedding of the
normalized specialization of Lanzenberger's fixed-interface common-domain
carrier and its image-preserving DDC action.

Jost, immediately before Definition 2.2.2 (printed p. 17), permits a converter
to make “a bounded number of queries to the inside interfaces.” The DDC carrier
below realizes that interface-changing converter shape as a complete-history
function; branch-finiteness is the explicit Lean generalization of Jost's numerical
bound. Liu--Maurer's component converters are obtained by fixing the relevant
outer and inner interfaces. Neither source requires a second resource carrier
or a second attachment operation.

Routed parallel and probabilistic converters are intentionally not exported by
this root while their redesigned category is developed separately. The
fixed-interface `RandomSystems` root does not import this extension.
-/
