module

public import Commons.Definitions.AbstractModel.ExtractionPresentation.AddressMap
public import Tests.AbstractModelAddressMap

/-!
# Address embeddings preserve extraction

The existing shift sends the initial address 0 to 5 and keeps one parameter/secret pair.
A later overwrite does not alter the original-secret condition on the submitted guess.
-/

@[expose] public section

namespace Tests.AbstractModelExtractionAddressMap

open Commons.AbstractModel SystemAlgebra
open Tests.AbstractModel Tests.AbstractModelAddressMap

/-- The actual attached DDS uses the same parameter 9 and original secret 3 after shifting. -/
example : (model.extractionDDS 0 2 (9, 3)).1 =
    relabel (model.extractionDDS (shift 0) 2 (9, 3)).1 (model.mapCommand shift) id :=
  extractionDDS_mapCommand model shift 0 2 (9, 3)

/-- A zero-ordinary-call extraction game still permits the unchanged terminal guess. -/
example : (model.extractionDDS 0 0 (9, 3)).1 [submit] =
    (model.extractionDDS (shift 0) 0 (9, 3)).1 [submit] := by
  rw [extractionDDS_mapCommand model shift]
  exact Part.map_id' (f := id) (fun _ => rfl) _

/-- Overwriting and shifting addresses preserve success against the original secret 3. -/
example : (model.extracted 3).1
    ([overwrite, submit].map (model.mapCommand shift)) := by
  change model.submitted ([overwrite, submit].map (model.mapCommand shift)) = some 3
  rw [submitted_mapCommand]
  rfl

/-- The same history still loses against original secret 4. -/
example : ¬ (model.extracted 4).1
    ([overwrite, submit].map (model.mapCommand shift)) := by
  change model.submitted ([overwrite, submit].map (model.mapCommand shift)) ≠ some 4
  rw [submitted_mapCommand]
  intro impossible
  cases impossible

#print axioms Commons.AbstractModel.extractionDDS_mapCommand
#print axioms Commons.AbstractModel.submitted_mapCommand

end Tests.AbstractModelExtractionAddressMap
