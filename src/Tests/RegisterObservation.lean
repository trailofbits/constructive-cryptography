module

public import Tests.AbstractModelRegisters

/-!
# Register contents through observation blocks

The existing integer-register fixture is reused. A block and its pending prefix preserve
an overwritten map. Successful reads allow repeated selection; a missing unselected operand
shows why the complete source read must succeed.
-/

@[expose] public section

namespace Tests.RegisterObservation

open Commons.AbstractModel Tests.AbstractModel Tests.AbstractModelRegisters

/-- An overwrite changes address 0 before the two observations are issued. -/
def overwritten : ℕ → Option ℤ :=
  model.registers operate initialRegisters [⟨.compute (), (fun _ => 0, 0)⟩]

/-- Read the overwritten address, then perform the model's zero-operand observation. -/
def queries : List (Σ ρ : model.Query, Fin (model.queryArity ρ) → ℕ) :=
  [⟨false, fun _ => 0⟩, ⟨true, fun i => Fin.elim0 i⟩]

example : model.registers operate overwritten
    (queries.map fun q => ⟨Port.query q.1, q.2⟩) = overwritten :=
  registers_map_query operate overwritten queries

/-- The prefix issued before the second call preserves the same overwritten map. -/
example : model.registers operate overwritten
    ((queries.take 1).map fun q => ⟨Port.query q.1, q.2⟩) = overwritten :=
  registers_map_query operate overwritten (queries.take 1)

example : model.registers operate overwritten
    (([] : List (Σ ρ : model.Query, Fin (model.queryArity ρ) → ℕ)).map
      fun q => ⟨Port.query q.1, q.2⟩) = overwritten :=
  registers_map_query operate overwritten []

/-- The overwritten input contains 9, and the observation block retains that value. -/
example : model.registers operate overwritten
    (queries.map fun q => ⟨Port.query q.1, q.2⟩) 0 = some 9 := by
  rw [registers_map_query]
  have present : read initialRegisters (fun _ : Fin 1 => 0) = some (fun _ => (7 : ℤ)) :=
    (read_eq_some_iff _ _ _).mpr (fun _ => initial_self 0 7)
  change (read initialRegisters (fun _ : Fin 1 => 0)).map (operate ()) = some 9
  rw [present]
  rfl

/-- Two output positions can select the same successfully read operand. -/
example : read initialRegisters ((fun _ : Fin 1 => (0 : ℕ)) ∘ (fun _ : Fin 2 => 0)) =
    some ((fun _ : Fin 1 => (7 : ℤ)) ∘ (fun _ : Fin 2 => 0)) := by
  apply read_comp_of_eq_some
  exact (read_eq_some_iff _ _ _).mpr (fun _ => initial_self 0 7)

example : read initialRegisters ((fun _ : Fin 1 => (0 : ℕ)) ∘ (fun i : Fin 0 => Fin.elim0 i)) =
    some ((fun _ : Fin 1 => (7 : ℤ)) ∘ (fun i : Fin 0 => Fin.elim0 i)) := by
  apply read_comp_of_eq_some
  exact (read_eq_some_iff _ _ _).mpr (fun _ => initial_self 0 7)

/-- Selecting only address 0 succeeds, while the full tuple also asks for absent address 7. -/
theorem missing_unselected_operand :
    read initialRegisters (![0, 7] ∘ (fun _ : Fin 1 => (0 : Fin 2))) ≠
      (read initialRegisters ![0, 7]).map (fun v => v ∘ (fun _ : Fin 1 => (0 : Fin 2))) := by
  have absent : read initialRegisters ![0, 7] = none := by
    apply Option.not_isSome_iff_eq_none.mp
    intro present
    have last := (read_isSome initialRegisters ![0, 7]).mp present 1
    change (initialRegisters 7).isSome at last
    simp only [initialRegisters, initial, Function.update_of_ne (by omega : (7 : ℕ) ≠ 0),
      Option.isSome_none, Bool.false_eq_true] at last
  have first : read initialRegisters (![0, 7] ∘ (fun _ : Fin 1 => (0 : Fin 2))) =
      some (fun _ => (7 : ℤ)) := by
    apply (read_eq_some_iff _ _ _).mpr
    intro j
    exact initial_self 0 7
  rw [absent, Option.map_none, first]
  intro impossible
  cases impossible

#print axioms read_eq_some_iff
#print axioms read_comp_of_eq_some
#print axioms registers_map_query
#print axioms missing_unselected_operand

end Tests.RegisterObservation
