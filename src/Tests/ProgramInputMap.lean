module

public import Tests.ProgramQueryMap

/-!
# Mapping outside inputs through a pending call

Natural-number queries are mapped to Booleans by `n == 0`. Both programs make one unit
inside query and return its Boolean reply. The input map is deliberately noninjective.
-/

@[expose] public section

namespace Tests.ProgramInputMap

open SystemAlgebra

/-- Ignore the outside natural number, make one unit query, then return its Boolean reply. -/
def naturalQuery : Program Unit Unit Unit (fun _ => ℕ) (fun _ => Bool)
    (fun _ => Unit) (fun _ => Bool)
  | _, (), _, [] => .inr ⟨(), ()⟩
  | s, (), _, (_, ⟨(), y⟩) :: _ => .inl (s, y)

/-- Map the outside query `n` to `n == 0`; inside replies remain unchanged. -/
def queryMap (u : Σ _ : Unit, ℕ) : Σ _ : Unit, Bool := ⟨(), u.2 == 0⟩

/-- Rename the held outside query while retaining the state, exchanges, and pending call. -/
def modeMap : Program.Mode Unit Unit Unit (fun _ => ℕ) (fun _ => Unit) (fun _ => Bool) →
    Program.Mode Unit Unit Unit (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) :=
  Program.Mode.mapStateInput id (fun _ n => n == 0)

/-- Erasing the outside query preserves a step, including its pending inside reply. -/
lemma step_commutes (m : Program.Mode Unit Unit Unit (fun _ => ℕ)
    (fun _ => Unit) (fun _ => Bool))
    (x : Σ l, twoFam (fun _ : Unit => ℕ) (fun _ : Unit => Bool) l) :
    (naturalQuery.step m x).map (Prod.map modeMap id) =
      ProgramQueryMap.unitQuery.step (modeMap m) (outsideMap queryMap x) := by
  apply Program.step_stateInputMap id (fun _ n => n == 0)
  intro s o n h
  cases s
  cases o
  cases h with
  | nil => rfl
  | cons z h =>
    obtain ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, y⟩⟩ := z
    rfl

/-- The whole converter is transported by the input map, without an injectivity assumption. -/
lemma converter_map (xs : List (Σ l, twoFam (fun _ : Unit => ℕ)
    (fun _ : Unit => Bool) l)) :
    DDC.ofProgram () naturalQuery xs =
      DDC.ofProgram () ProgramQueryMap.unitQuery (xs.map (outsideMap queryMap)) := by
  calc
    DDC.ofProgram () naturalQuery xs = (DDC.ofProgram () naturalQuery xs).map id :=
      (Part.map_id' (f := id) (fun _ => rfl) _).symm
    _ = _ := DDC.ofProgram_map_inputs_of_stepMap naturalQuery ProgramQueryMap.unitQuery
      (outsideMap queryMap) modeMap id step_commutes () () rfl xs

example : queryMap ⟨(), 7⟩ = queryMap ⟨(), 42⟩ := rfl

/-- The pending inside query is the same after mapping an actual outside query. -/
example : DDC.ofProgram () naturalQuery [⟨⟨none, ()⟩, 7⟩] =
    DDC.ofProgram () ProgramQueryMap.unitQuery [⟨⟨none, ()⟩, false⟩] :=
  converter_map _

/-- The pending call retains the mapped outside value and its one unanswered inside query. -/
example : modeMap (.busy () () 7 [] ⟨(), ()⟩) =
    .busy () () false [] ⟨(), ()⟩ := rfl

/-- The reply after an outside query and its inside answer is unchanged. -/
example : DDC.ofProgram () naturalQuery [⟨⟨none, ()⟩, 7⟩, ⟨⟨some (), ()⟩, true⟩] =
    DDC.ofProgram () ProgramQueryMap.unitQuery
      [⟨⟨none, ()⟩, false⟩, ⟨⟨some (), ()⟩, true⟩] :=
  converter_map _

/-- A pending call rejects a second outside query in both representations. -/
example : naturalQuery.step (.busy () () 7 [] ⟨(), ()⟩) ⟨⟨none, ()⟩, 42⟩ = none := rfl

#print axioms Program.emit_stateInputMap
#print axioms Program.step_stateInputMap
#print axioms Program.run_map_inputs
#print axioms DDC.ofProgram_map_inputs_of_stepMap
#print axioms DDC.ofProgramOn_map_inputs_of_stepMap
#print axioms converter_map

end Tests.ProgramInputMap
