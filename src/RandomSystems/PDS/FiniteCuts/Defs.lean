module

public import RandomSystems.PDS.Filter

/-!
# Deterministic finite observation cuts

`cutSystem s q` restricts the existing partial system `s` to input histories of length at
most `q`, using `filterDom`. Every retained history keeps exactly its original partial reply.
The DDS, domain and iterated-cut laws are in `PDS.FiniteCuts`.
-/

@[expose] public section

namespace SystemAlgebra

/-- Keep `s` through query `q`; longer input histories have no reply. -/
noncomputable def cutSystem
    -- `A` carries queries and `B` replies; `s` is a partial function on input histories.
    {A B : Type} (s : System A B)
    -- `q` is the maximum retained input-history length.
    (q : ℕ) : System A B :=
  filterDom (fun xs => xs.length ≤ q) s

end SystemAlgebra
