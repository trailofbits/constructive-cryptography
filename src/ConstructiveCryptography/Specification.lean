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
-/
