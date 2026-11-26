module

public import RandomSystems.Typed.ParallelAllSelection
public import Tests.TypedNaryParallel

/-!
# Selecting a heterogeneous family exchange

The Boolean-indexed family has Boolean messages at `false` and unit messages at `true`.
Selection retains the local exchange only when both component tags match the selected member.
-/

@[expose] public section

namespace SystemAlgebra.Tests.ParallelAllSelection

/-- Matching selected tags retain the Boolean query and reply. -/
example : Interface.selectExchange (A := heterogeneousFamily) false
    (⟨⟨false, ()⟩, true⟩, ⟨⟨false, ()⟩, false⟩) = some (⟨(), true⟩, ⟨(), false⟩) := by
  rfl

/-- Matching tags at the other component select no exchange. -/
example : Interface.selectExchange (A := heterogeneousFamily) false
    (⟨⟨true, ()⟩, ()⟩, ⟨⟨true, ()⟩, ()⟩) = none := by
  rfl

/-- A query and reply at different components select no exchange. -/
example : Interface.selectExchange (A := heterogeneousFamily) false
    (⟨⟨false, ()⟩, true⟩, ⟨⟨true, ()⟩, ()⟩) = none := by
  rfl

#print axioms Interface.selectExchange_reindex
#print axioms Interface.selectExchange_optionSplit

end SystemAlgebra.Tests.ParallelAllSelection
