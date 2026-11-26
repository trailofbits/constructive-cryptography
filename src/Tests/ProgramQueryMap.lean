module

public import RandomSystems.Converter.ProgramQueryMap

/-!
# Non-injective inside query maps

A forwarding program sends a Boolean query; its mapped program sends a unit query.
Both retain the Boolean outside input and return the same inside reply.
-/

@[expose] public section

namespace Tests.ProgramQueryMap

open SystemAlgebra

/-- Forward the outside Boolean once and return its inside Boolean reply. -/
def forward : Program Unit Unit Unit (fun _ => Bool) (fun _ => Bool)
    (fun _ => Bool) (fun _ => Bool)
  | _, (), u, [] => .inr ⟨(), u⟩
  | s, (), _, (_, ⟨(), y⟩) :: _ => .inl (s, y)

/-- Make one unit query and return its inside Boolean reply. -/
def unitQuery : Program Unit Unit Unit (fun _ => Bool) (fun _ => Bool)
    (fun _ => Unit) (fun _ => Bool)
  | _, (), _, [] => .inr ⟨(), ()⟩
  | s, (), _, (_, ⟨(), y⟩) :: _ => .inl (s, y)

/-- Both Boolean query values map to the sole unit query, at the same port. -/
def eraseQuery (_ : Σ _ : Unit, Bool) : Σ _ : Unit, Unit := ⟨(), ()⟩

lemma forward_body_map (s o : Unit) (u : Bool)
    (h : List ((Σ _ : Unit, Bool) × (Σ _ : Unit, Bool))) :
    Sum.map id eraseQuery (forward s o u h) =
      unitQuery s o u (h.map (Prod.map eraseQuery id)) := by
  cases o
  rcases h with _ | ⟨⟨q, ⟨⟨⟩, y⟩⟩, h⟩ <;> rfl

/-- The outside domain still accepts only the single outside query `false`. -/
lemma unitQuery_eq_relabel :
    DDC.ofProgramOn () unitQuery (fun us => us = [⟨(), false⟩]) =
      relabel (DDC.ofProgramOn () forward (fun us => us = [⟨(), false⟩]))
        id (insideMap eraseQuery) :=
  DDC.ofProgramOn_relabel_of_queryMap forward unitQuery eraseQuery
    (fun ⟨⟨⟩, _⟩ => rfl) forward_body_map () _

/-- Pending and completed inside queries are mapped; the outside input and replies remain. -/
example : Program.Mode.mapQueries eraseQuery
    (.busy () () true [(⟨(), false⟩, ⟨(), true⟩)] ⟨(), true⟩) =
    (Program.Mode.busy () () true [(⟨(), ()⟩, ⟨(), true⟩)] ⟨(), ()⟩ :
      Program.Mode Unit Unit Unit (fun _ => Bool) (fun _ => Unit) (fun _ => Bool)) := rfl

example : eraseQuery ⟨(), false⟩ = eraseQuery ⟨(), true⟩ := rfl

#print axioms Program.emit_queryMap
#print axioms Program.step_queryMap
#print axioms DDC.ofProgramOn_relabel_of_queryMap
#print axioms unitQuery_eq_relabel

end Tests.ProgramQueryMap
