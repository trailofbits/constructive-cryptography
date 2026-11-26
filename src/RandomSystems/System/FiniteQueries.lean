module

public import RandomSystems.System.DDE
public import Mathlib.Data.Set.Finite.List

/-!
# Finite query sets

`finite_queries_before` collects the queries proposed after fewer than `n` replies.
A finite reply alphabet gives finitely many such histories, each proposing at most one query.
`finite_queries_of_queryBounded` therefore gives a finite query set for a bounded environment,
even when the query alphabet is infinite.
-/

@[expose] public section

namespace SystemAlgebra

/-- The queries proposed before horizon `n` form a finite set. -/
lemma finite_queries_before
    -- `A` carries queries; only the reply alphabet `B` must be finite.
    {A B : Type} [_root_.Finite B]
    -- `σ ys` is the next partial query after reply history `ys`; `n` bounds its length.
    (σ : List B →. A) (n : ℕ) :
    {x | ∃ ys, ys.length < n ∧ x ∈ σ ys}.Finite := by
  -- There are finitely many histories, each contributing at most one query.
  have finiteUnion := (List.finite_length_lt B n).biUnion
    (fun ys _ => (σ ys).subsingleton.finite)
  apply finiteUnion.subset
  rintro x ⟨ys, short, member⟩
  exact Set.mem_iUnion.mpr ⟨ys, Set.mem_iUnion.mpr ⟨short, member⟩⟩

/-- A bounded environment proposes finitely many queries across all reply histories. -/
theorem finite_queries_of_queryBounded
    -- `A` carries queries and `B` the finite replies observed by `E`.
    {A B : Type} [_root_.Finite B] (E : DDE A B)
    -- `bounded` requires `E` to stop after at most `n` queries on every reply history.
    {n : ℕ} (bounded : QueryBounded n E) :
    {x | ∃ ys, x ∈ E.1 ys}.Finite := by
  apply (finite_queries_before E.1 n).subset
  rintro x ⟨ys, hx⟩
  exact ⟨ys, bounded ys (Part.dom_iff_mem.mpr ⟨x, hx⟩), hx⟩

end SystemAlgebra
