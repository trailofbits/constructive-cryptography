import ConstructiveCryptography.Construction.Basic
import ConstructiveCryptography.Specification.Basic
import ConstructiveCryptography.Specification.Game.Basic
import ConstructiveCryptography.Specification.Maps
import ConstructiveCryptography.Specification.Relaxation.Kernel

/-!
# Objects, specifications and maps

The interface-free foundation: constructor-indexed judgments, set
specifications, resource maps, union lifts, pointwise relaxations and closure.
General maps use functions, monotone maps use `OrderHom`, and union-preserving
maps use `sSupHom`. `Relaxation.toClosureOperator` adds proved idempotence.

Everything imported here is stated over arbitrary carrier types `X`, `Y`, … whose elements
are called resources; no interface, random system, category or distance is assumed. A
specification `Specification X` is a set of elements of `X`, and a map `f : X → Y` is a plain
function, not necessarily a converter.

* `Construction.Basic`: `Constructible judgment constructors source target`, existence of an
  admitted constructor in a selected set satisfying a supplied judgment.
* `Specification.Basic`: exact construction `Constructs f source target`, that is
  `f '' source ⊆ target`.
* `Specification.Maps`: the union lift `lift r` of a set-valued map `r : X → Set Y`.
* `Specification.Relaxation.Kernel` (with `Defs`, `Basic`, `Closure`): reflexive pointwise
  relaxations, their composition, idempotent relaxations as closure operators, and the
  relaxation identifying resources with equal value under a map.
* `Specification.Game.Basic`: `gameSpec tests error`, resources on which every selected test
  is at most `error`.

Converter actions, `star` closure, parallel locality and distance-based construction live in
`Specification.Action`, `Star`, `Parallel`, `Metric` and `Star.Metric`, imported separately.
-/
