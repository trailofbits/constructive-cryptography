module

public import RandomSystems.System.Interconnection

/-!
# Selected inputs through feedback

Each external number causes one internal unit input. Positive numbers are then echoed;
zero causes silence. The projection laws retain external values in order and erase the
internal units, including the exchange that ends without an exposed reply.
-/

@[expose] public section

namespace Tests.TraceFilterMap

open SystemAlgebra

/-- Echo a positive input after one internal unit input; remain silent after input zero. -/
def feedbackReply : System (Nat ⊕ Unit) (Nat ⊕ Unit) := fun h =>
  match h.reverse with
  | .inl _ :: _ => Part.some (.inr ())
  | .inr () :: .inl (n + 1) :: _ => Part.some (.inl (n + 1))
  | _ => Part.none

/-- Expose number replies and feed unit replies back to the same component. -/
def route : Nat ⊕ Unit → Nat ⊕ (Nat ⊕ Unit)
  | .inl n => .inl n
  | .inr () => .inr (.inr ())

/-- Keep number inputs and erase the internal unit inputs. -/
def external : Nat ⊕ Unit → Option Nat
  | .inl n => some n
  | .inr () => none

lemma feedback_erased (y : Nat ⊕ Unit) (x : Nat ⊕ Unit)
    (routed : route y = .inr x) : external x = none := by
  cases y with
  | inl n => cases routed
  | inr u => cases u; cases routed; rfl

lemma first_input : Induces feedbackReply route Sum.inl [7] (some 7)
    [.inl 7, .inr ()] := by
  refine Induces.snoc [] 7 none [] (some 7) _ Induces.nil ?_
  refine Exchange.feed _ (.inr ()) (.inr ()) (some 7) _ (Part.mem_some _) rfl ?_
  exact Exchange.out _ (.inl 7) 7 (Part.mem_some _) rfl

/-- Two completed exchanges preserve the external order `[7, 2]`. -/
theorem exposed_inputs : ∃ H, Induces feedbackReply route Sum.inl [7, 2] (some 2) H ∧
    H.filterMap external = [7, 2] := by
  have induced : Induces feedbackReply route Sum.inl [7, 2] (some 2)
      [.inl 7, .inr (), .inl 2, .inr ()] := by
    refine Induces.snoc [7] 2 (some 7) _ (some 2) _ first_input ?_
    refine Exchange.feed _ (.inr ()) (.inr ()) (some 2) _ (Part.mem_some _) rfl ?_
    exact Exchange.out _ (.inl 2) 2 (Part.mem_some _) rfl
  refine ⟨_, induced, ?_⟩
  exact induced.filterMap_eq external some feedback_erased (fun _ => rfl)

/-- The silent exchange still retains its external zero and erases its internal unit. -/
theorem silent_inputs : ∃ H, Induces feedbackReply route Sum.inl [7, 0] none H ∧
    H.filterMap external = [7, 0] := by
  have induced : Induces feedbackReply route Sum.inl [7, 0] none
      [.inl 7, .inr (), .inl 0, .inr ()] := by
    refine Induces.snoc [7] 0 (some 7) _ none _ first_input ?_
    refine Exchange.feed _ (.inr ()) (.inr ()) none _ (Part.mem_some _) rfl ?_
    exact Exchange.silent _ id
  refine ⟨_, induced, ?_⟩
  exact induced.filterMap_eq external some feedback_erased (fun _ => rfl)

#print axioms Exchange.filterMap_eq
#print axioms Induces.filterMap_eq
#print axioms exposed_inputs
#print axioms silent_inputs

end Tests.TraceFilterMap
