import ConstructiveCryptography.DSL

/-!
# DSL components

Systems, converters and filters declared in the DSL: a counter with two ports, fresh and
persistent random bits, arithmetic with loops, tuples and matching, a counter on an exact
domain, branches, a padding converter with an inferred cost (`Padding.exact`), a write-through
converter onto a smaller interface, typed by per-port budgets through a partial port map, and a
filter.
-/

open SystemAlgebra SystemAlgebra.DSL
open scoped SystemAlgebra.DSL

namespace DSLExamples

system Counter
  initialize
    count ← (0 : Fin 16)
  on next() → Fin 16
    count ← count + 1
    return count
  on read() → Fin 16
    return count

system FreshBits
  on bit() → Bool
    b ←$ 𝒰[Bool]
    return b

system SecretBit
  initialize
    secret ←$ 𝒰[Bool]
  on bit() → Bool
    return secret

system Arithmetic
  on sum(xs : List.Vector (Fin 16) 3) → Fin 16
    total ← (0 : Fin 16)
    for x ∈ xs.toList
      total ← total + x
    if total > 10
      return 10
    else
      return total
  on swap(x : Fin 16, y : Fin 16) → Fin 16 × Fin 16
    (x, y) ← (y, x)
    return (x, y)
  on optional(x : Option (Fin 16)) → Fin 16
    match x
    | none →
      return 0
    | some n →
      return n + 1

system BoundedCounter(q : Nat)
  domain h ↦ h ≠ [] ∧ h.length ≤ q
  initialize
    count ← (0 : Fin 16)
  on next() → Fin 16
    count ← count + 1
    return count
by
  constructor
  · simp
  · intro p h hp hne hd
    exact ⟨hne, hp.length_le.trans hd.2⟩

system Branches
  initialize
    count ← (0 : Fin 16)
  on update(increase : Bool) → Fin 16
    if increase
      count ← count + 1
    else
      count ← count + 2
    return count

-- A request of `n` padding steps makes `n` inside queries: besides `Padding` itself, the
-- inferred cost gives `Padding.exact`, from outside histories of total cost `q` into `q`
-- inside queries.
interface Pad
  pad(steps : Fin 4) → Fin 16

converter Padding : Pad
  inside f : Fin 16 → Fin 16
  on pad(steps : Fin 4) → Fin 16
    total ← (0 : Fin 16)
    for i ∈ List.range steps.val
      total ← f(total + Fin.ofNat 16 i)
    return total

interface Store
  put(value : Fin 16) → Fin 16

interface Cache
  write(value : Fin 16) → Fin 16
  read() → Fin 16

-- Write through to the store and remember the reply; read it back without an inside query. At
-- per-port budgets it is a converter from `Cache` to `Store` whose reads need no inside budget:
-- `WriteThrough.portMap` sends `write` to `put` and `read` to nothing.
converter WriteThrough : Cache
  inside store : Store
  initialize
    last ← (0 : Fin 16)
  on write(value : Fin 16) → Fin 16
    stored ← store.put(value)
    last ← stored
    return stored
  on read() → Fin 16
    return last

-- Forward at most `q` padding requests, then stop.
filter FirstRequests(q : Nat) : Pad
  domain h ↦ h.length ≤ q

end DSLExamples
