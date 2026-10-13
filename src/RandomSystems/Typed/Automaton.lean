import RandomSystems.Typed.SystemParallel

/-!
# Automata as typed systems

An automaton whose initial state is sampled from a law is a typed system: the behavior of its
deterministic systems on the interface's domain, one for each initial state (Maurer 2002,
Definition 2, with the randomness in the initial state). Parallel composition runs two such
automata side by side from independent initial states.

## Main definitions

* `Interface.automatonDDS T step s`: the deterministic system of the automaton started in `s`
* `TypedSystem.ofAutomaton T step initial`: the automaton with initial state sampled from
  `initial`

## Main results

* `TypedSystem.ofAutomaton_mass`: a transcript has the mass of the initial states from which
  the automaton gives it
* `TypedSystem.parallel_ofAutomaton`: parallel automata are the automaton running both side by
  side
-/

namespace SystemAlgebra

open Probability Interface

variable {S : Type} (T : Interface) (step : S → (i : T.I) → T.X i → S × T.Y i)

/-- The deterministic system of the automaton started in `s`, on `T`'s domain. -/
noncomputable def Interface.automatonDDS (s : S) : {r : InterfaceSystem T.I T.X T.Y //
    IsDDS r ∧ RepliesAtQueriedInterface r ∧ ∀ h, (r h).Dom ↔ T.domain h} :=
  ⟨filterDom T.domain (automatonSystem step s),
    (automatonSystem_isDDS step s).filterDom _ T.nonempty_prefix.2,
    fun h x y hy => automatonSystem_replies step s h x y ((filterDom_mem_iff _ _ _ _).mp hy).2,
    fun h => by
      rw [filterDom_dom, automatonSystem_dom]
      exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => T.nonempty_prefix.1 (he ▸ hd)⟩⟩⟩

/-- **The typed system of an automaton** with its initial state sampled from `initial`. -/
noncomputable def TypedSystem.ofAutomaton (initial : Distribution.ProbDist S) : TypedSystem T :=
  TypedSystem.ofPDS ⟨Distribution.fTransform (automatonDDS T step) initial.1,
    Distribution.fTransform_isProbDist _ initial.2⟩

/-- A transcript has the mass of the initial states from which the automaton gives it. -/
lemma TypedSystem.ofAutomaton_mass (initial : Distribution.ProbDist S)
    (h : List ((Σ i, T.X i) × (Σ i, T.Y i))) :
    (TypedSystem.ofAutomaton T step initial).1 h = initial.1.mass fun s =>
      Replies (filterDom T.domain (automatonSystem step s)) (h.map Prod.fst) (h.map Prod.snd) := by
  change behaviorMass _ _ _ = _
  rw [behaviorMass, Distribution.mass_fTransform]
  rfl

/-- **Parallel automata** are the automaton running both side by side from independent initial
states. -/
lemma TypedSystem.parallel_ofAutomaton {A B : Interface} {S T : Type}
    (f : S → (i : A.I) → A.X i → S × A.Y i) (g : T → (j : B.I) → B.X j → T × B.Y j)
    (P : Distribution.ProbDist S) (Q : Distribution.ProbDist T) :
    parallel (ofAutomaton A f P) (ofAutomaton B g Q) =
      ofAutomaton (tensor A B) (parallelStep f g)
        ⟨Distribution.prod P.1 Q.1, Distribution.prod_isProbDist _ _ P.2 Q.2⟩ := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [parallel_mass_of_presentations _ _ P.1 Q.1
      (fun s => filterDom A.domain (automatonSystem f s))
      (fun t => filterDom B.domain (automatonSystem g t))
      (ofAutomaton_mass A f P) (ofAutomaton_mass B g Q),
    ofAutomaton_mass]
  refine Distribution.mass_congr _ fun st => ?_
  rw [parallel_automatonSystem f g A.nonempty_prefix B.nonempty_prefix]

end SystemAlgebra
