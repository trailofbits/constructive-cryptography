module

public import RandomSystems.Converter.ProgramTrace
public import RandomSystems.Typed.DSL.Programs

/-!
# Adaptive completed-invocation traces

The caller first sends its outside input, then sends the first reply plus one.
The inside automaton adds each query to its retained total and returns the new total.
The trace therefore checks adaptive queries, two different inside states, and both final states.
A direct-return caller checks the empty trace without changing the inside state.
-/

@[expose] public section

namespace Tests.ProgramTrace

open SystemAlgebra

/-- Query `u`, then `first + 1`; retain `s + second` and return `first + second`. -/
noncomputable def adaptive : Program Nat Unit Unit (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) := fun s _ u =>
  DSL.callProg () u fun first =>
    DSL.callProg () (first + 1) fun second => DSL.returnProg (s + second, first + second)

/-- Each query adds its input to the retained total and returns that new total. -/
def addAndReply (total : Nat) (_ : Unit) (query : Nat) : Nat × Nat :=
  (total + query, total + query)

lemma adaptive_bounded : adaptive.Bounded 2 := by
  intro s o u
  exact DSL.callBound_call (X := fun _ : Unit => Nat) (Y := fun _ => Nat)
    (b := 1) () u _ fun first =>
    DSL.callBound_call (X := fun _ : Unit => Nat) (Y := fun _ => Nat)
      (b := 0) () (first + 1) _ fun _ => DSL.callBound_return 0 _

/-- Starting at total 1, inputs 2 then 4 receive replies 3 then 7. -/
def adaptiveTrace : List ((Σ _ : Unit, Nat) × (Σ _ : Unit, Nat)) :=
  [(⟨(), 2⟩, ⟨(), 3⟩), (⟨(), 4⟩, ⟨(), 7⟩)]

lemma adaptive_consistent : adaptive.Consistent 10 () 2 adaptiveTrace := by
  have first : adaptive.Consistent 10 () 2 [(⟨(), 2⟩, ⟨(), 3⟩)] :=
    (Program.consistent_nil adaptive 10 () 2).snoc rfl 3
  exact first.snoc (by simp only [adaptive, DSL.callProg, ↓reduceDIte]) 7

lemma adaptive_replies : Replies (automatonSystem addAndReply 1)
    (adaptiveTrace.map Prod.fst) (adaptiveTrace.map Prod.snd) := by
  change Replies (automatonSystem addAndReply 1)
    (([] ++ [⟨(), 2⟩]) ++ [⟨(), 4⟩]) (([] ++ [⟨(), 3⟩]) ++ [⟨(), 7⟩])
  apply replies_snoc.mpr
  refine ⟨replies_snoc.mpr ⟨replies_nil _, ?_⟩, ?_⟩
  · rw [automatonSystem_snoc]
    rfl
  · rw [automatonSystem_snoc]
    rfl

/-- The body can receive a recorded 4 at its first call, but this automaton returns 3. -/
theorem false_reply : adaptive.Consistent 10 () 2 [(⟨(), 2⟩, ⟨(), 4⟩)] ∧
    ¬ Replies (automatonSystem addAndReply 1) [⟨(), 2⟩] [⟨(), 4⟩] := by
  refine ⟨(Program.consistent_nil adaptive 10 () 2).snoc rfl 4, ?_⟩
  intro actual
  have last := (replies_snoc.mp (show Replies (automatonSystem addAndReply 1)
    ([] ++ [⟨(), 2⟩]) ([] ++ [⟨(), 4⟩]) from actual)).2
  rw [automatonSystem_snoc] at last
  have impossible : (3 : Nat) = 4 := congrArg (fun y : Σ _ : Unit, Nat => y.2)
    (Part.some_injective last)
  cases impossible

/-- The caller retains 17, the inside retains 7, and the outside reply is 10. -/
theorem adaptive_result : adaptive.combine addAndReply adaptive_bounded (10, 1) () 2 =
    ((17, 7), 10) := by
  have returned : adaptive 10 () 2 adaptiveTrace = .inl (17, 10) := by
    simp only [adaptive, adaptiveTrace, DSL.callProg, DSL.returnProg, ↓reduceDIte]
  exact adaptive.combine_eq_of_consistent_replies addAndReply adaptive_bounded
    10 () 2 1 adaptiveTrace adaptive_consistent adaptive_replies returned

/-- Return `s + u` immediately, retaining the same result as the program's next state. -/
def direct : Program Nat Unit Unit (fun _ => Nat) (fun _ => Nat)
    (fun _ => Nat) (fun _ => Nat) := fun s _ u => DSL.returnProg (s + u, s + u)

lemma direct_bounded : direct.Bounded 0 := by
  intro s o u
  exact DSL.callBound_return 0 _

/-- An empty trace returns immediately and leaves the inside total 8 untouched. -/
theorem direct_result : direct.combine addAndReply direct_bounded (3, 8) () 4 =
    ((7, 8), 7) :=
  direct.combine_eq_of_consistent_replies addAndReply direct_bounded 3 () 4 8 []
    (Program.consistent_nil direct 3 () 4) (replies_nil _) rfl

#print axioms Program.invoke_eq_of_consistent_replies
#print axioms Program.combine_eq_of_consistent_replies
#print axioms false_reply
#print axioms adaptive_result
#print axioms direct_result

end Tests.ProgramTrace
