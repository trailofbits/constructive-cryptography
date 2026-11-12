module

public import RandomSystems.Typed.ParallelAllSelection.Defs
public import RandomSystems.Typed.ParallelAllRegroup

/-!
# Selecting exchanges across family presentations

`Interface.selectExchange_reindex` preserves selection through a family reindexing.
`Interface.selectExchange_optionSplit` identifies selection at `none` with the left exchange
of the head/tail presentation. Both equations follow the existing transcript projection laws.
-/

@[expose] public section

namespace SystemAlgebra.Interface

/-- Reindexing preserves the local exchange at the corresponding family member. -/
lemma selectExchange_reindex
    -- `e` presents the family `A` with indices in `K'`; `k'` selects its member.
    {K K' : Type} [DecidableEq K] [DecidableEq K'] (e : K' ≃ K) (A : K → Interface) (k' : K')
    (z : (Σ l : Σ k, (A k).I, (A l.1).X l.2) ×
      (Σ l : Σ k, (A k).I, (A l.1).Y l.2)) :
    selectExchange (e k') z = selectExchange k'
      (((reindexLabels e A fun k i => (A k).X i).prodCongr
        (reindexLabels e A fun k i => (A k).Y i)) z) := by
  unfold selectExchange
  apply congrArg List.head?
  -- Reindex the projected singleton, using the typed alphabet correspondence.
  have projected := RandomSystem.restrictExchanges_sigmaCongrLeft e
    (A := fun k => Σ i, (A k).X i) (B := fun k => Σ i, (A k).Y i)
    [((Equiv.sigmaAssoc fun j i => (A (e j)).X i).prodCongr
      (Equiv.sigmaAssoc fun j i => (A (e j)).Y i))
      (((reindexLabels e A fun k i => (A k).X i).prodCongr
        (reindexLabels e A fun k i => (A k).Y i)) z)] k'
  -- The raw law uses classical equality decisions; projections ignore this proof choice.
  rw [Subsingleton.elim (fun a b : K => Classical.propDecidable (a = b))
      (inferInstance : DecidableEq K),
    Subsingleton.elim (fun a b : K' => Classical.propDecidable (a = b))
      (inferInstance : DecidableEq K')] at projected
  refine Eq.trans ?_ projected
  apply congrArg (RandomSystem.restrictExchanges (e k'))
  simp only [List.map_singleton, Equiv.prodCongr_apply]
  exact congrArg List.singleton (Prod.ext
    (reindexLabels_assoc e A (fun k i => (A k).X i) z.1).symm
    (reindexLabels_assoc e A (fun k i => (A k).Y i) z.2).symm)

/-- Selection at the head is the left/left exchange of the split presentation. -/
lemma selectExchange_optionSplit
    -- `A none` is the head and `A (some j)` the tail; `z` is the family exchange.
    {J : Type} [DecidableEq J] (A : Option J → Interface)
    (z : (Σ l : Σ o, (A o).I, (A l.1).X l.2) ×
      (Σ l : Σ o, (A o).I, (A l.1).Y l.2)) :
    selectExchange none z =
      match ((optionSplitLabels A fun o i => (A o).X i).prodCongr
        (optionSplitLabels A fun o i => (A o).Y i)) z with
      | (⟨.inl i, x⟩, ⟨.inl j, y⟩) => some (⟨i, x⟩, ⟨j, y⟩)
      | _ => none := by
  unfold selectExchange
  have projected := RandomSystem.optionSplit_left
    (A := fun o => Σ i, (A o).X i) (B := fun o => Σ i, (A o).Y i)
    [((Equiv.sigmaAssoc fun j i => (A j).X i).prodCongr
      (Equiv.sigmaAssoc fun j i => (A j).Y i)) z]
  -- Identify the raw projection's equality decisions with the caller's decisions.
  rw [Subsingleton.elim (fun a b : J => Classical.propDecidable (a = b))
    (inferInstance : DecidableEq J)] at projected
  rw [← projected]
  -- The typed split and the cumulative split retain the same local values.
  obtain ⟨⟨⟨(_ | j), i⟩, x⟩, ⟨⟨(_ | k), l⟩, y⟩⟩ := z <;> rfl

end SystemAlgebra.Interface
