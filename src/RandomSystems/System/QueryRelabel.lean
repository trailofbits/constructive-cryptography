module

public import RandomSystems.System.InterfaceSystem

/-!
# Relabeling a distinguisher's queries

`DDD.relabelQueries D code` changes each resource query `x` at port `i` to `code i x`.
The caller receives the same replies and returns the same final decision. The laws in
`System.QueryRelabel.Laws` connect this relabeling to its query strategy and interactions.
-/

@[expose] public section

namespace SystemAlgebra

/-- `D.relabelQueries code` sends query `x` at port `i` as `code i x`.
The trigger, received replies and final decision are unchanged. -/
def DDD.relabelQueries
    -- `I` labels resource ports; `X i`, `X' i` are the old and new queries, with replies `Y i`.
    {I : Type} {X X' Y : I → Type} (D : DDD I X Y)
    (code : ∀ i, X i → X' i) : DDD I X' Y :=
  relabel D id fun
    | ⟨.start, e⟩ => e.elim
    | ⟨.dec, b⟩ => ⟨.dec, b⟩
    | ⟨.res i, x⟩ => ⟨.res i, code i x⟩

end SystemAlgebra
