module

public import RandomSystems.Typed.DSL.Collect
public import RandomSystems.Converter.ProgramTrace

/-!
# Attaching an ordered collection

`Program.combine_eq_of_collectCalls` computes the combined step from a scheduled reply tuple.
Collection supplies its own trace consistency and terminal result; the inside automaton supplies
its actual replies. The generic completed-trace law retains the resulting inside state.
-/

@[expose] public section

namespace SystemAlgebra.Program

open SystemAlgebra.DSL

/-- Collecting actual inside replies returns `finish ys` and retains the inside query fold. -/
lemma combine_eq_of_collectCalls
    -- `P` carries program state `S`; `stepR` updates the retained inside state `R`.
    {S R O J : Type}
    -- `O` and `J` label outside and inside ports; `U`/`V` and `X`/`Y` carry their queries/replies.
    {U V : O → Type} {X Y : J → Type}
    (P : Program S O J U V X Y) (stepR : R → (j : J) → X j → R × Y j)
    -- `bounded` certifies the existing total attachment presentation.
    {b : ℕ} (bounded : P.Bounded b) (s : S) (o : O) (u : U o) (r : R)
    -- `request` specifies this invocation's calls; `finish` combines their typed replies.
    (n : ℕ) (request : Fin n → Σ j, X j)
    (finish : ((i : Fin n) → Y (request i).1) → S × V o)
    (body : ∀ h, P s o u h = collectCalls n request finish h)
    -- `ys` are the actual replies from the same inside state, in the scheduled order.
    (ys : (i : Fin n) → Y (request i).1)
    (replies : Replies (automatonSystem stepR r) (List.ofFn request)
      (List.ofFn fun i => (⟨(request i).1, ys i⟩ : Σ j, Y j))) :
    P.combine stepR bounded (s, r) o u =
      (((finish ys).1, stateAfter stepR r (List.ofFn request)), (finish ys).2) := by
  let h := List.ofFn fun i => (request i, (⟨(request i).1, ys i⟩ : Σ j, Y j))
  have consistent : P.Consistent s o u h := by
    change ExchangesOf (P s o u) h
    rw [funext body]
    exact collectCalls_exchangesOf n request finish ys
  have returned : P s o u h = .inl (finish ys) :=
    (body h).trans (collectCalls_reply n request finish ys)
  have actual : Replies (automatonSystem stepR r) (h.map Prod.fst) (h.map Prod.snd) := by
    simpa only [h, List.map_ofFn, Function.comp_def] using replies
  simpa only [h, List.map_ofFn, Function.comp_def] using
    P.combine_eq_of_consistent_replies stepR bounded s o u r h consistent actual returned

end SystemAlgebra.Program
