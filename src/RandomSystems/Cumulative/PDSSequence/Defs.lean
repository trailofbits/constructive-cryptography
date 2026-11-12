module

public import RandomSystems.PDS.Sequence.Defs
public import RandomSystems.Cumulative.FiniteCuts

/-!
# Cumulative behavior of a coherent presentation

`PDSSequence.behavior` reads each finite transcript in the presentation at its own depth.
It is `RandomSystem.limitMass` applied to the existing finite PDS behavior map.
Its normalization and recovery of all finite-level behaviors are proved in `Cumulative.PDSSequence`.
-/

@[expose] public section

namespace SystemAlgebra.PDSSequence

/-- Read the cumulative mass at the level given by the transcript's length. -/
noncomputable def behavior
    -- Finite alphabets are required by the existing bounded `PDS.behavior` carrier.
    {A B : Type} [Fintype A] [Fintype B] {D : List (A × B) → A → Prop}
    (P : PDSSequence A B D) : List (A × B) → ℝ :=
  RandomSystem.limitMass D (fun n => PDS.behavior (P.level n).1 (P.level n).2)

end SystemAlgebra.PDSSequence
