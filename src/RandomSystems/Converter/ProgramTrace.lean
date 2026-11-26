module

public import RandomSystems.Converter.ProgramAttachment
public import RandomSystems.System.Interconnection

/-!
# Program traces

`Program.invoke_eq_of_consistent_replies` evaluates an invocation from its exchange trace:
the body must issue each recorded query, the inside automaton must return each recorded reply,
and the body must then return. The inside state is the fold of those same queries.
`Program.combine_eq_of_consistent_replies` carries this local contract to the existing
attachment presentation, including adaptive bodies and invocations without inside calls.
`DDC.exists_after_busy_of_mem_insideQueries` locates every issued query at a reached input
prefix, including a query whose inside reply is still pending.
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

namespace SystemAlgebra.DDC

/-- Every issued inside query occurs as the pending query of a reached input prefix. -/
lemma exists_after_busy_of_mem_insideQueries
    -- `S` carries retained state; `O` and `J` are outside and inside ports.
    {S O J : Type}
    -- `U`, `V` are outside query/reply families; `X`, `Y` are their inside counterparts.
    {U V : O → Type} {X Y : J → Type}
    -- `P` is the body, initialized in `s`; `h` records converter inputs and outputs.
    {P : Program S O J U V X Y} {s : S}
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (replies : Replies (DDC.ofProgram s P) (h.map Prod.fst) (h.map Prod.snd))
    -- `q` is an inside query already emitted in `h`, whether answered or still pending.
    {q : Σ j, X j} (issued : q ∈ insideQueries (h.map Prod.snd)) :
    ∃ xs, xs <+: h.map Prod.fst ∧ ∃ o s', ∃ u : U o, ∃ exchanges,
      P.after s xs = some (.busy o s' u exchanges q) := by
  -- Locate the tagged output in the original transcript.
  have tagged := (mem_restrict_iff
    (A := optF (Σ o, V o) (fun _ : Unit => Σ j, X j))
    (some ()) q ((h.map Prod.snd).map splitIn)).mp issued
  obtain ⟨y, hy, same⟩ := List.mem_map.mp tagged
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
  have output : z.2 = (⟨⟨some (), q.1⟩, q.2⟩ : Σ l, twoFam V X l) := by
    rcases z with ⟨x, ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩⟩ <;> cases same; rfl
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp hz
  -- The reply at this occurrence comes from one step of the existing compiler.
  have value := replies.eq_some_of_eq_append shape
  have member : z.2 ∈ DDC.ofProgram s P (before.map Prod.fst ++ [z.1]) := by
    rw [value]
    exact Part.mem_some _
  obtain ⟨m, m', reached, advances⟩ := (mem_ofProgram_snoc s P _ _ _).mp member
  have next : P.after s (before.map Prod.fst ++ [z.1]) = some m' :=
    (Program.after_snoc_eq_some P s _ _ m').mpr ⟨m, z.2, reached, advances⟩
  refine ⟨before.map Prod.fst ++ [z.1], ?_, ?_⟩
  · refine ⟨after.map Prod.fst, ?_⟩
    rw [shape, List.map_append, List.map_cons, List.append_assoc, List.singleton_append]
  · -- An inside output leaves the compiler waiting for that same query.
    rcases Program.step_cases P advances with ⟨s', o, u, _, _, emitted⟩ |
      ⟨o, s', u, hs, pending, v, _, _, emitted⟩
    · rcases Program.emit_cases P s' o u [] with ⟨s'', v, _, result⟩ | ⟨q', _, result⟩
      · rw [result, output] at emitted
        cases emitted
      · rw [result, output] at emitted
        have queryEq : q = q' := eq_of_heq
          (Sigma.mk.inj_iff.mp (congrArg (splitIn ∘ Prod.snd) emitted)).2
        subst q'
        have modeEq : m' = _ := congrArg Prod.fst emitted
        exact ⟨o, s', u, [], next.trans (congrArg some modeEq)⟩
    · rcases Program.emit_cases P s' o u (hs ++ [(pending, ⟨pending.1, v⟩)]) with
        ⟨s'', v', _, result⟩ | ⟨q', _, result⟩
      · rw [result, output] at emitted
        cases emitted
      · rw [result, output] at emitted
        have queryEq : q = q' := eq_of_heq
          (Sigma.mk.inj_iff.mp (congrArg (splitIn ∘ Prod.snd) emitted)).2
        subst q'
        have modeEq : m' = _ := congrArg Prod.fst emitted
        exact ⟨o, s', u, _, next.trans (congrArg some modeEq)⟩

end SystemAlgebra.DDC
