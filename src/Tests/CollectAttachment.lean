module

public import RandomSystems.Typed.DSL.CollectAttachment
public import Tests.CollectCallsTrace

/-!
# Collection against retained state

The Boolean port checks whether the inside counter is zero; the natural-number port returns
its current value plus six. Both calls increment the same retained counter. The second reply
therefore distinguishes shared state from restarting the inside automaton for each call.
An empty collection leaves the counter unchanged.
-/

@[expose] public section

namespace Tests.CollectAttachment

open SystemAlgebra SystemAlgebra.DSL Tests.CollectCallsTrace

/-- Increment the counter; reply with its zero test at `false`, or its value plus six at `true`. -/
def advance (count : Nat) : (port : Bool) → Unit → Nat × Reply port
  | false, _ => (count + 1, count == 0)
  | true, _ => (count + 1, count + 6)

/-- Ask the existing Boolean/natural schedule and return its ordered pair. -/
noncomputable def collectPair : Program Unit Unit Bool (fun _ => Unit)
    (fun _ => Bool × Nat) (fun _ => Unit) Reply :=
  fun _ _ _ => collectCalls (Y := Reply) 2 request (fun ys => ((), finish ys))

lemma collectPair_bounded : collectPair.Bounded 2 := by
  intro s o u h q consistent issued
  exact (collectCalls_cost (Y := Reply) 2 request
    (fun ys => ((), finish ys)) h consistent).1 q issued

/-- The shared counter starts at zero, giving Boolean `true` and then natural number `7`. -/
lemma scheduled_replies : Replies (automatonSystem advance 0) (List.ofFn request)
    (List.ofFn fun i => (⟨(request i).1, answers i⟩ : Σ port, Reply port)) := by
  change Replies (automatonSystem advance 0)
    (([] ++ [⟨false, ()⟩]) ++ [⟨true, ()⟩])
    (([] ++ [⟨false, true⟩]) ++ [⟨true, (7 : Nat)⟩])
  apply replies_snoc.mpr
  refine ⟨replies_snoc.mpr ⟨replies_nil _, ?_⟩, ?_⟩
  · rw [automatonSystem_snoc]
    rfl
  · rw [automatonSystem_snoc]
    rfl

/-- Collection returns `(true,7)` and leaves the same inside counter at two. -/
theorem collected_result : collectPair.combine advance collectPair_bounded ((), 0) () () =
    (((), 2), (true, 7)) :=
  Program.combine_eq_of_collectCalls collectPair advance collectPair_bounded () () () 0
    2 request (fun ys => ((), finish ys)) (fun _ => rfl) answers scheduled_replies

/-- A zero-call collection returns 17 without querying either port. -/
noncomputable def collectNone : Program Unit Unit Bool (fun _ => Unit)
    (fun _ => Nat) (fun _ => Unit) Reply :=
  fun _ _ _ => collectCalls 0 (fun i => Fin.elim0 i) (fun _ => ((), 17))

lemma collectNone_bounded : collectNone.Bounded 0 := by
  intro s o u
  exact callBound_return 0 _

/-- Empty collection retains the initial inside counter nine. -/
theorem empty_result : collectNone.combine advance collectNone_bounded ((), 9) () () =
    (((), 9), 17) := by
  exact Program.combine_eq_of_collectCalls collectNone advance collectNone_bounded () () () 9
    0 (fun i => Fin.elim0 i) (fun _ => ((), 17)) (fun _ => rfl) (fun i => Fin.elim0 i)
    (by simpa only [List.ofFn_zero] using replies_nil (automatonSystem advance 9))

#print axioms Program.combine_eq_of_collectCalls
#print axioms collected_result
#print axioms empty_result

end Tests.CollectAttachment
