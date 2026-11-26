module

public import RandomSystems.Typed.DSL.Programs
public import Probability.List

/-!
# Chronological query labeling

With a lawful input comparison, `chronologicalLabelingProgram` maps each distinct outside input
to its first-occurrence position in the retained input prefix. It calls the inside resource
at the corresponding enumerated label and forwards its reply. A fresh position beyond the
finite pool uses the explicit fallback; repeated inputs keep their old position.

```text
outside a ──► encoder [prefix xs] ──► label of first occurrence ──► inside resource
outside c ◄────────────────────── c ◄─────────────────────────────
```

The encoder is deterministic. In the permutation application the inside resource owns one
retained permutation shared by every call. The encoder stores only the outside input prefix.
-/

@[expose] public section

namespace SystemAlgebra

/-- Append `a` to the prefix, query at its first-occurrence label, and retain the prefix when
returning the inside reply. Positions beyond the label pool query `fallback`. -/
noncomputable def chronologicalLabelingProgram
    -- `A` carries outside inputs, `B` the finite query labels, and `C` the unchanged replies.
    {A B C : Type}
    -- `BEq A` is the selected input comparison; first-occurrence laws use its `LawfulBEq`.
    [BEq A] [Fintype B]
    -- `labels` orders the pool; `fallback` gives a total query rule after exhaustion.
    (labels : Fin (Fintype.card B) ≃ B) (fallback : B) :
    Program (List A) Unit Unit (fun _ => A) (fun _ => C) (fun _ => B) (fun _ => C) :=
  fun xs _ a =>
    let next := xs ++ [a]
    let index := next.eraseDups.idxOf a
    let label := if h : index < Fintype.card B then labels ⟨index, h⟩ else fallback
    DSL.callProg () label fun c => DSL.returnProg (next, c)

end SystemAlgebra
