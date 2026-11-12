module

public import RandomSystems.PDS.PDS

/-!
# Independent parallel cumulative masses

`RandomSystem.parallelLeft` and `parallelRight` retain each component's exchanges.
`parallelConsistent` requires matching query/reply tags; `parallelAdmits` queries the selected
component on its projected history. `parallelMass` multiplies their independent masses on
consistent transcripts and assigns zero to mismatched tags.
-/

@[expose] public section

namespace SystemAlgebra

variable {A B C E : Type}

namespace RandomSystem

/-- Project the exchanges belonging to the left component. -/
def parallelLeft (h : List ((Two A C) × (Two B E))) : List (A × B) :=
  h.filterMap fun z => match z with
    | (⟨none, x⟩, ⟨none, y⟩) => some (x, y)
    | _ => none

/-- Project the exchanges belonging to the right component. -/
def parallelRight (h : List ((Two A C) × (Two B E))) : List (C × E) :=
  h.filterMap fun z => match z with
    | (⟨some (), x⟩, ⟨some (), y⟩) => some (x, y)
    | _ => none

/-- An exchange is with one of the two independent components. -/
def parallelConsistent (h : List ((Two A C) × (Two B E))) : Prop :=
  ∀ z ∈ h, z.1.1 = z.2.1

/-- Parallel composition queries the selected component at its own history. -/
def parallelAdmits (D : List (A × B) → A → Prop) (D' : List (C × E) → C → Prop)
    (h : List ((Two A C) × (Two B E))) : Two A C → Prop
  | ⟨none, x⟩ => D (parallelLeft h) x
  | ⟨some (), x⟩ => D' (parallelRight h) x

end RandomSystem

open RandomSystem

open Classical in
/-- Independent components have the product of their projected transcript masses. -/
noncomputable def parallelMass
    -- `p` has query/reply alphabets `A`, `B`; `r` has alphabets `C`, `E`.
    (p : List (A × B) → ℝ) (r : List (C × E) → ℝ)
    -- `h` interleaves the two components using the existing ordered tags.
    (h : List ((Two A C) × (Two B E))) : ℝ :=
  if parallelConsistent h then p (parallelLeft h) * r (parallelRight h) else 0

end SystemAlgebra
