module

public import RandomSystems.Converter.ProgramAttachment

/-!
# Completed invocation traces

`Program.invoke_eq_of_consistent_replies` evaluates an invocation from its exchange trace:
the body must issue each recorded query, the inside automaton must return each recorded reply,
and the body must then return. The inside state is the fold of those same queries.
`Program.combine_eq_of_consistent_replies` carries this local contract to the existing
attachment presentation, including adaptive bodies and invocations without inside calls.
-/

@[expose] public section

namespace SystemAlgebra.Program

variable
  -- `P` has state `S`, outside ports `O`, and inside ports `J`.
  {S O J R : Type}
  -- `U o`/`V o` and `X j`/`Y j` are outside and inside query/reply types.
  {U V : O → Type} {X Y : J → Type}
  (P : Program S O J U V X Y)
  -- `stepR` updates the retained inside state `R` and answers its queried port.
  (stepR : R → (j : J) → X j → R × Y j)

/-- A completed consistent trace determines both final states and the outside reply. -/
lemma invoke_eq_of_consistent_replies
    -- `s` and `r` are the initial states; `o(u)` starts this outside invocation.
    (s : S) (o : O) (u : U o) (r : R)
    -- `h` records the inside exchanges chosen by the body and answered by this automaton.
    (h : List ((Σ j, X j) × (Σ j, Y j)))
    (consistent : P.Consistent s o u h)
    (replies : Replies (automatonSystem stepR r) (h.map Prod.fst) (h.map Prod.snd))
    -- `a` contains the next program state and outside reply after the last exchange.
    {a : S × V o} (returned : P s o u h = .inl a) :
    P.invoke stepR s o u h.length r [] =
      some ((a.1, stateAfter stepR r (h.map Prod.fst)), a.2) := by
  have resumed : ∀ remaining prior, h = prior ++ remaining →
      P.invoke stepR s o u remaining.length
        (stateAfter stepR r (prior.map Prod.fst)) prior =
          some ((a.1, stateAfter stepR r (h.map Prod.fst)), a.2) := by
    intro remaining
    induction remaining with
    | nil =>
      intro prior hshape
      have same : h = prior := by simpa only [List.append_nil] using hshape
      subst prior
      simp only [List.length_nil, invoke, returned, Sum.elim_inl]
    | cons z remaining ih =>
      intro prior hshape
      -- The body requests this next exchange; the automaton supplies its recorded reply.
      have following : P.Consistent s o u (prior ++ z :: remaining) :=
        hshape ▸ consistent
      have issued := (following prior.length (by
        simp only [List.length_append, List.length_cons]
        omega)).1
      rw [List.take_left' rfl,
        List.getElem_append_right (Nat.le_refl _)] at issued
      simp only [Nat.sub_self, List.getElem_cons_zero] at issued
      have answered := replies.eq_some_of_eq_append hshape
      rw [automatonSystem_snoc] at answered
      have reply := Part.some_injective answered
      have rest : h = (prior ++ [z]) ++ remaining := by
        simpa only [List.append_assoc, List.singleton_append] using hshape
      -- Advance the same retained inside state, then continue on the remaining exchanges.
      simp only [List.length_cons, invoke, issued]
      rw [reply]
      simpa only [List.map_append, List.map_singleton, stateAfter_snoc] using
        ih (prior ++ [z]) rest
  simpa only [List.nil_append, List.map_nil, stateAfter_nil] using resumed h [] rfl

/-- The bounded attachment presentation has the result certified by a completed trace. -/
lemma combine_eq_of_consistent_replies
    -- `bounded` supplies the bound required by the existing total `combine` presentation.
    {b : ℕ} (bounded : P.Bounded b)
    -- `s`, `r`, and `o(u)` start the same invocation as the trace `h` below.
    (s : S) (o : O) (u : U o) (r : R)
    (h : List ((Σ j, X j) × (Σ j, Y j)))
    (consistent : P.Consistent s o u h)
    (replies : Replies (automatonSystem stepR r) (h.map Prod.fst) (h.map Prod.snd))
    -- `a` is the terminal program state and outside reply.
    {a : S × V o} (returned : P s o u h = .inl a) :
    P.combine stepR bounded (s, r) o u =
      ((a.1, stateAfter stepR r (h.map Prod.fst)), a.2) :=
  combine_eq_of_invoke stepR bounded
    (P.invoke_eq_of_consistent_replies stepR s o u r h consistent replies returned)

end SystemAlgebra.Program
