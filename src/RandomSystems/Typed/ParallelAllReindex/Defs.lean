module

public import RandomSystems.Typed.ParallelAllRegroup

/-!
# Reindexing a finite interface family

`TypedConverter.reindex` assembles the existing renaming converter from the family alphabet
bijections and their domain correspondence. A query at component `k` reaches component
`e.symm k`, preserving its local port, query and reply.
-/

@[expose] public section

namespace SystemAlgebra.TypedConverter

/-- Forward a family through `e : L ≃ K`, preserving each component's declared domain. -/
noncomputable def reindex
    -- `A k` is the component interface; `e` chooses its new family index in `L`.
    {K L : Type} [Fintype K] [Fintype L] (e : L ≃ K) (A : K → Interface) :
    TypedConverter (Interface.tensorAll A) (Interface.tensorAll fun l => A (e l)) :=
  rename (Equiv.sigmaCongrLeft (β := fun k => (A k).I) e).symm
    (reindexLabels e A fun k i => (A k).X i) (reindexLabels e A fun k i => (A k).Y i)
    (reindexLabels_fst e A fun k i => (A k).X i)
    (reindexLabels_fst e A fun k i => (A k).Y i) (tensorAll_domain_reindexLabels e A)

end SystemAlgebra.TypedConverter
