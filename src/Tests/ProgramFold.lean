module

public import RandomSystems.Converter.Program
public import RandomSystems.Typed.DSL.Programs

/-!
# Projected program state as a fold

A running sum receives a natural-number outside query, makes one unit inside call, then
retains the updated sum. `Program.after_fold` gives the same accumulator while that call
is pending and after its reply: the outside query contributes once, the inside reply never.
A list accumulator records two outside inputs in order using the same fold law.
-/

@[expose] public section

namespace Tests.ProgramFold

open SystemAlgebra

/-- On input `x`, make one unit inside call, then retain and return `total + x`. -/
noncomputable def sumAfterCall : Program Nat Unit Unit (fun _ => Nat) (fun _ => Nat)
    (fun _ => Unit) (fun _ => Unit) :=
  fun total _ x => DSL.callProg () () (fun _ => DSL.returnProg (total + x, total + x))

lemma sumAfterCall_returned (s : Nat) (o : Unit) (u : Nat) (h)
    (s' v : Nat) (returned : sumAfterCall s o u h = .inl (s', v)) : s' = s + u := by
  cases h with
  | nil => cases returned
  | cons z h =>
    obtain ⟨⟨⟨⟩, ⟨⟩⟩, ⟨⟨⟩, ⟨⟩⟩⟩ := z
    simp only [sumAfterCall, DSL.callProg, ↓reduceDIte, DSL.returnProg] at returned
    exact (congrArg Prod.fst (Sum.inl.inj returned)).symm

/-- A pending input 2 contributes once, although the retained sum is still 4. -/
theorem pending_sum : ∃ m, sumAfterCall.after 4 [⟨⟨none, ()⟩, 2⟩] = some m ∧
    (match m with | .idle s => s | .busy _ s u _ _ => s + u) = 6 := by
  let m : Program.Mode Nat Unit Unit (fun _ => Nat) (fun _ => Unit) (fun _ => Unit) :=
    .busy () 4 2 [] ⟨(), ()⟩
  have accepted : sumAfterCall.after 4 [⟨⟨none, ()⟩, 2⟩] = some m := rfl
  refine ⟨m, accepted, ?_⟩
  have score := Program.after_fold sumAfterCall id (fun s u => s + u.2)
    sumAfterCall_returned 4 [⟨⟨none, ()⟩, 2⟩] m accepted
  rw [outsideInputs_outside, List.foldl_cons, List.foldl_nil] at score

/-- The inside reply completes the update without adding another outside input. -/
theorem completed_sum : ∃ m,
    sumAfterCall.after 4 [⟨⟨none, ()⟩, 2⟩, ⟨⟨some (), ()⟩, ()⟩] = some m ∧
    (match m with | .idle s => s | .busy _ s u _ _ => s + u) = 6 := by
  let busy : Program.Mode Nat Unit Unit (fun _ => Nat) (fun _ => Unit) (fun _ => Unit) :=
    .busy () 4 2 [] ⟨(), ()⟩
  have pending : sumAfterCall.after 4 [⟨⟨none, ()⟩, 2⟩] = some busy := rfl
  have accepted :
      sumAfterCall.after 4 [⟨⟨none, ()⟩, 2⟩, ⟨⟨some (), ()⟩, ()⟩] = some (.idle 6) := by
    change sumAfterCall.after 4 ([⟨⟨none, ()⟩, 2⟩] ++ [⟨⟨some (), ()⟩, ()⟩]) = _
    rw [Program.after_snoc, pending]
    simp only [Option.bind_some, busy, Program.step, ite_true, Program.emit, sumAfterCall,
      DSL.callProg, DSL.returnProg, ↓reduceDIte, Option.map_some, List.nil_append]
  refine ⟨.idle 6, accepted, ?_⟩
  have score := Program.after_fold sumAfterCall id (fun s u => s + u.2)
    sumAfterCall_returned 4 _ (.idle 6) accepted
  change 6 = (outsideInputs (U := fun _ : Unit => Nat) (Y := fun _ : Unit => Unit)
    ([⟨⟨none, ()⟩, 2⟩] ++ [⟨⟨some (), ()⟩, ()⟩])).foldl (fun s u => s + u.2) 4 at score
  rw [outsideInputs_append, outsideInputs_outside, outsideInputs_inside,
    List.append_nil, List.foldl_cons, List.foldl_nil] at score

/-- Append each outside input to the retained list and return a unit acknowledgment. -/
def remember : Program (List Nat) Unit Unit (fun _ => Nat) (fun _ => Unit)
    (fun _ => Unit) (fun _ => Unit) := fun h _ x _ => .inl (h ++ [x], ())

/-- The history accumulator retains the two inputs in their original order. -/
theorem retained_history : ∃ m,
    remember.after [] [⟨⟨none, ()⟩, 7⟩, ⟨⟨none, ()⟩, 2⟩] = some m ∧
    (match m with | .idle h => h | .busy _ h u _ _ => h ++ [u]) = [7, 2] := by
  have returned h o u es h' v (hr : remember h o u es = .inl (h', v)) :
      h' = h ++ [u] :=
    (congrArg Prod.fst (Sum.inl.inj hr)).symm
  have accepted : remember.after [] [⟨⟨none, ()⟩, 7⟩, ⟨⟨none, ()⟩, 2⟩] =
      some (.idle [7, 2]) := rfl
  refine ⟨.idle [7, 2], accepted, ?_⟩
  have history := Program.after_fold remember id (fun h u => h ++ [u.2])
    returned [] _ (.idle [7, 2]) accepted
  change [7, 2] = (outsideInputs (U := fun _ : Unit => Nat) (Y := fun _ : Unit => Unit)
    ([⟨⟨none, ()⟩, 7⟩] ++ [⟨⟨none, ()⟩, 2⟩])).foldl (fun h u => h ++ [u.2]) [] at history
  rw [outsideInputs_append, outsideInputs_outside, List.foldl_append,
    List.foldl_cons, List.foldl_nil] at history

#print axioms Program.after_fold
#print axioms pending_sum
#print axioms completed_sum
#print axioms retained_history

end Tests.ProgramFold
