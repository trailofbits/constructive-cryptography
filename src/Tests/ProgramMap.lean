module

public import RandomSystems.Converter.Program

/-!
# Mapping the replies of a compiled program

The same-state map from Boolean echo replies to unit acknowledgments is non-injective.
The compiler law applies on all input histories and preserves the selected outside domain.
The existing program-state comparison tests exercise the retained-state specialization.
-/

@[expose] public section

namespace Tests.ProgramMap

open SystemAlgebra

/-- Each Boolean query receives the same Boolean, without an inside call. -/
def echo : Program Unit Unit Unit (fun _ => Bool) (fun _ => Bool)
    (fun _ => Unit) (fun _ => Unit) := fun s _ u _ => .inl (s, u)

/-- Each Boolean query receives a unit acknowledgment, without an inside call. -/
def acknowledge : Program Unit Unit Unit (fun _ => Bool) (fun _ => Unit)
    (fun _ => Unit) (fun _ => Unit) := fun s _ _ _ => .inl (s, ())

/-- Erase outside Boolean replies; keep inside query messages. -/
def replyMap : (Σ l, twoFam (fun _ : Unit => Bool) (fun _ : Unit => Unit) l) →
    (Σ l, twoFam (fun _ : Unit => Unit) (fun _ : Unit => Unit) l)
  | ⟨⟨none, o⟩, _⟩ => ⟨⟨none, o⟩, ()⟩
  | ⟨⟨some (), j⟩, x⟩ => ⟨⟨some (), j⟩, x⟩

lemma echo_step_map (m : Program.Mode Unit Unit Unit (fun _ => Bool)
    (fun _ => Unit) (fun _ => Unit)) (x : Σ l, twoFam (fun _ : Unit => Bool)
    (fun _ : Unit => Unit) l) :
    (echo.step m x).map (Prod.map id replyMap) = acknowledge.step m x := by
  rcases m with s | ⟨o, s, u, h, q⟩ <;> rcases x with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
  · rfl
  · rfl
  · rfl
  · simp only [Program.step]
    split_ifs <;> rfl

lemma acknowledge_eq_relabel :
    DDC.ofProgram () acknowledge = relabel (DDC.ofProgram () echo) id replyMap :=
  DDC.ofProgram_relabel_of_stepMap echo acknowledge id replyMap echo_step_map () () rfl

/-- Restricting admitted queries does not change the reply-map equation. -/
example : DDC.ofProgramOn () acknowledge (fun us => us = [⟨(), false⟩]) =
    relabel (DDC.ofProgramOn () echo (fun us => us = [⟨(), false⟩])) id replyMap :=
  DDC.ofProgramOn_relabel_of_stepMap echo acknowledge id replyMap echo_step_map () () rfl _

example : replyMap ⟨⟨none, ()⟩, false⟩ = replyMap ⟨⟨none, ()⟩, true⟩ := rfl

#print axioms Program.run_map
#print axioms DDC.ofProgram_relabel_of_stepMap
#print axioms DDC.ofProgramOn_relabel_of_stepMap
#print axioms acknowledge_eq_relabel

end Tests.ProgramMap
