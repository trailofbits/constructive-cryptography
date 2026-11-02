module

public import RandomSystems.Typed.Automaton
public import RandomSystems.Typed.PresentedGame

/-!
# Automata with hidden monotone conditions

`PDG.ofAutomaton` retains one state drawn from `initial`, updates it with `step`, and monitors
`bad s` on the input history, where `s` is the initial draw. `TypedGame.ofAutomaton` presents
this normalized law as a typed game. The bit is not returned to the caller
[1, remark after Definition 3.23, p. 71] and stays true once reached
[1, Definition 3.22, p. 71]. Visible replies may still reveal whether it is set.

`TypedGame.visible_ofAutomaton` identifies its visible system with `TypedSystem.ofAutomaton`:
monitoring changes only the hidden bit. `PDG.ofAutomaton_badProbability` and
`PDG.ofAutomaton_goodProbability` pull condition and transcript events back to `initial`.
`TypedGame.ofAutomaton_unsetProbability` gives the complementary unset probability on admitted
query lists. `TypedGame.ofAutomaton_mass_unsetMBOs` identifies the all-unset cumulative
law with visible replies jointly with the final condition being false, when the condition
is initially false.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

-- `A` fixes the ports, alphabets and admitted histories; `S` carries the retained state.
variable (A : Interface) {S : Type}
    -- `step s i x = (s', y)` updates the current state and replies at the queried port.
    (step : S → (i : A.I) → A.X i → S × A.Y i)
    -- `initial` samples the starting state; `bad s` reads input histories at that initial draw.
    (initial : ProbDist S) (bad : S → MC (Σ i, A.X i))

/-- Sample `s ← initial`, run its automaton on `A.domain`, and set the hidden bit when
`bad s` holds on the input history. This is a normalized law over discrete games.
[1, Definition 3.22, p. 71]: “aᵢ = 1 implies aⱼ = 1 for j ≥ i”. -/
noncomputable def PDG.ofAutomaton :
    ProbDist {g : DDG (Σ i, A.X i) (Σ i, A.Y i) // HasDomain A.inputDomain g.1.1} :=
  initial.map fun s =>
    ⟨(⟨(A.automatonDDS step s).1, (A.automatonDDS step s).2.1⟩, bad s),
      HasDomain.ofInputs (A.automatonDDS step s).2.2.2⟩

/-- Hiding the condition leaves the original automaton's cumulative law on `A.domain`. -/
lemma PDG.ofAutomaton_visible :
    (TypedSystem.ofAutomaton A step initial).1 =
      PDS.behavior (PDG.underlying (PDG.ofAutomaton A step initial bad).1)
        (PDG.underlying_probability (PDG.ofAutomaton A step initial bad).2) := by
  apply RandomSystem.ext
  intro h
  rw [TypedSystem.ofAutomaton_mass, PDS.behavior_mass, behaviorMass, PDG.underlying,
    PDG.ofAutomaton, ProbDist.map_val, mass_fTransform, mass_fTransform]
  -- Forgetting the condition leaves exactly the same domain-restricted automaton.
  rfl

/-- On fixed queries `xs`, the condition has its mass under the initial law. -/
lemma PDG.ofAutomaton_badProbability
    -- `xs` is the query history, including the empty or an unadmitted history.
    (xs : List (Σ i, A.X i)) :
    PDG.badProbability (PDG.ofAutomaton A step initial bad).1 xs =
      initial.1.mass (fun s => (bad s).1 xs) := by
  rw [PDG.badProbability, PDG.ofAutomaton, ProbDist.map_val, mass_fTransform]

/-- A visible transcript with the condition unset has the joint mass of these two events. -/
lemma PDG.ofAutomaton_goodProbability
    -- `h` pairs each tagged query with its tagged visible reply.
    (h : List ((Σ i, A.X i) × Σ i, A.Y i)) :
    PDG.goodProbability (PDG.ofAutomaton A step initial bad).1 h = initial.1.mass (fun s =>
      Replies (filterDom A.domain (automatonSystem step s))
        (h.map Prod.fst) (h.map Prod.snd) ∧ ¬ (bad s).1 (h.map Prod.fst)) := by
  rw [PDG.goodProbability, PDG.ofAutomaton, ProbDist.map_val, mass_fTransform]
  -- The automaton presentation supplies the visible replies; `bad s` supplies the other event.
  rfl

/-- The automaton on `A.domain` with `bad s` as its hidden monotone condition, for one initial
state `s ← initial`. Visible replies and retained updates are exactly those of `step`. -/
noncomputable def TypedGame.ofAutomaton : TypedGame A :=
  ofPDG (PDG.ofAutomaton A step initial bad).1 (PDG.ofAutomaton A step initial bad).2
    (PDG.ofAutomaton_visible A step initial bad)

/-- If the condition is initially false, the cumulative mass with every MBO unset is the
initial-law mass of visible replies jointly with the final condition being false. -/
lemma TypedGame.ofAutomaton_mass_unsetMBOs
    -- `hzero` rules out an initially reached event on every possible initial state.
    (hzero : ∀ s ∈ initial.1.support, ¬ (bad s).1 [])
    -- `h` is the visible query/reply transcript.
    (h : List ((Σ i, A.X i) × Σ i, A.Y i)) :
    (TypedGame.ofAutomaton A step initial bad).1.1 (unsetMBOs h) =
      initial.1.mass (fun s => Replies (filterDom A.domain (automatonSystem step s))
        (h.map Prod.fst) (h.map Prod.snd) ∧ ¬ (bad s).1 (h.map Prod.fst)) := by
  -- Before any query the mass is one; afterwards monotonicity reduces all bits to the last.
  rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
  · rw [unsetMBOs, List.map_nil, RandomSystem.mass_nil]
    symm
    exact initial.mass_eq_one_of_support _ (fun s hs => ⟨replies_nil _, hzero s hs⟩)
  · change (PDG.behavior (PDG.ofAutomaton A step initial bad).1
      (PDG.ofAutomaton A step initial bad).2) _ = _
    rw [PDG.behavior_apply, PDG.ofAutomaton, ProbDist.map_val, mass_fTransform]
    apply mass_congr
    intro s
    simp only [List.concat_eq_append, unsetMBOs, List.map_map, Function.comp_def]
    simpa only [List.map_map, Function.comp_def, Interface.automatonDDS] using
      DDG.replies_withMBO_unset_iff
      (⟨(A.automatonDDS step s).1, (A.automatonDDS step s).2.1⟩, bad s)
      (xs := (h ++ [z]).map Prod.fst)
      (by rw [List.map_append, List.map_singleton]
          exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
      ((h ++ [z]).map Prod.snd)

/-- On admitted queries, the MBO is unset with one minus the probability of `bad`. -/
lemma TypedGame.ofAutomaton_unsetProbability
    -- `xs` is admitted by `A.domain`, so every sampled automaton answers all of its queries.
    {xs : List (Σ i, A.X i)} (hxs : A.domain xs) :
    (TypedGame.ofAutomaton A step initial bad).1.1.unsetProbability xs =
      1 - initial.1.mass (fun s => (bad s).1 xs) := by
  change (PDG.behavior (PDG.ofAutomaton A step initial bad).1
    (PDG.ofAutomaton A step initial bad).2).unsetProbability xs = _
  rw [PDG.unsetProbability_behavior _ A.nonempty_prefix hxs, PDG.ofAutomaton_badProbability]

/-- The monitor changes only the hidden bit, leaving the automaton's visible system intact. -/
lemma TypedGame.visible_ofAutomaton :
    (TypedGame.ofAutomaton A step initial bad).visible =
      TypedSystem.ofAutomaton A step initial :=
  visible_ofPDG _ _ _

end SystemAlgebra
