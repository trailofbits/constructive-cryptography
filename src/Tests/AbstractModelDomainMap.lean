module

public import Tests.AbstractModelAddressMap

/-!
# Admission under register address maps

The shift embedding preserves the existing legal store, observation and submission history.
A constant address map also preserves legal histories, but can make an originally undefined
read legal by identifying it with the input address.
-/

@[expose] public section

namespace Tests.AbstractModelDomainMap

open Commons.AbstractModel Tests.AbstractModel Tests.AbstractModelAddressMap

/-- The legal history stays legal with its initial address shifted to five. -/
lemma shifted_admitted :
    model.Admitted (shift 0) 2 ([store, observe, submit].map (model.mapCommand shift)) :=
  complete_admitted.mapCommand shift

example : model.Admitted (shift 0) 2
    ([store, observe, submit].map (model.mapCommand shift)) ↔
    model.Admitted 0 2 [store, observe, submit] :=
  admitted_mapCommand_iff shift 0 2 _

/-- Overwriting the input still changes neither the domain nor the separate terminal position. -/
example : model.Admitted (shift 0) 1
    ([overwrite, submit].map (model.mapCommand shift)) := by
  apply Admitted.mapCommand shift
  rw [show [overwrite, submit] = [overwrite] ++ [submit] from rfl, admitted_snoc_iff]
  refine ⟨Or.inr ?_, ?_, ?_, ?_⟩
  · rw [show [overwrite] = [] ++ [overwrite] from rfl, admitted_snoc_iff]
    simp [overwrite, ordinary, reads, initialized]
  · change (1 : ℕ) ≤ 1
    exact le_rfl
  · simp [overwrite, ordinary]
  · exact Finset.empty_subset _

/-- Collapsing every register to one address still preserves the original legal history. -/
example : model.Admitted () 2
    ([store, observe, submit].map (model.mapCommand (fun _ : ℕ => ()))) :=
  complete_admitted.mapCommand (fun _ => ())

/-- A noninjective map may make a previously uninitialized read legal. -/
example : model.Admitted () 1 [model.mapCommand (fun _ : ℕ => ()) observe] ∧
    ¬ model.Admitted 0 1 [observe] := by
  constructor
  · rw [show [model.mapCommand (fun _ : ℕ => ()) observe] =
        [] ++ [model.mapCommand (fun _ : ℕ => ()) observe] from rfl, admitted_snoc_iff]
    simp [mapCommand, Sigma.map, mapInput, observe, ordinary, reads, initialized]
  · intro admitted
    have operands := admitted.2.2.2 [] observe (List.prefix_refl _)
    have impossible := operands (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    simp [initialized] at impossible

#print axioms mapCommand_leftInverse
#print axioms initialized_mapCommand
#print axioms Admitted.mapCommand
#print axioms admitted_mapCommand_iff
#print axioms shifted_admitted

end Tests.AbstractModelDomainMap
