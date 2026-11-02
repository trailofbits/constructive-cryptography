module

public import Probability.Kernel
public import RandomSystems.Typed.SystemParallel

/-!
# Automata as typed systems

`TypedSystem.ofAutomaton T step initial` draws an initial state once, then
updates it with `step` on the domain of `T`. This is a random automaton
[1, Definition 2, p. 6: "specifying the internal randomness and the initial state"].

`ofAutomaton_mass` gives its cumulative probability at a transcript `h`:

```text
Pr[h] = Pr[s ← initial : automatonSystem step s answers h on T.domain].
```

`Interface.automatonDDS_eq_ofFunction` identifies a retained function with its existing DDS,
including unadmitted histories.

`ofAutomaton_map_congr` compares two state representations initialized from the same law:
pointwise equality for each draw yields equality of typed systems. `parallel_ofAutomaton`
assembles two automata using `parallelStep` and the independent initial law `prodProbDist P Q`.
A bisimulation for each draw yields an equation of typed systems, which rewrites under
attachment and parallel composition.

## References

1. U. Maurer. Indistinguishability of Random Systems. In *Advances in Cryptology —
   EUROCRYPT 2002*, LNCS 2332, pp. 110–132, Springer, 2002. Page numbers refer to the preprint.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Interface

-- `S` carries retained states; `T` gives query/reply types and the admitted input histories.
variable {S : Type} (T : Interface)
    -- At port `i`, `step s i x = (s', y)` updates the state and returns the reply.
    (step : S → (i : T.I) → T.X i → S × T.Y i)

/-- Start in `s`, apply `step` to each query, and admit exactly `T.domain`.
Thus `(automatonDDS T step s).1 = filterDom T.domain (automatonSystem step s)`. -/
noncomputable def Interface.automatonDDS (s : S) : {r : InterfaceSystem T.I T.X T.Y //
    IsDDS r ∧ RepliesAtQueriedInterface r ∧ ∀ h, (r h).Dom ↔ T.domain h} :=
  ⟨filterDom T.domain (automatonSystem step s),
    (automatonSystem_isDDS step s).filterDom _ T.nonempty_prefix.2,
    fun h x y hy => automatonSystem_replies step s h x y ((filterDom_mem_iff _ _ _ _).mp hy).2,
    fun h => by
      rw [filterDom_dom, automatonSystem_dom]
      exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => T.nonempty_prefix.1 (he ▸ hd)⟩⟩⟩

/-- An automaton retaining `k` and replying with `f k` is exactly the function's DDS on
`A.domain`, including unadmitted histories. -/
lemma Interface.automatonDDS_eq_ofFunction
    -- `A` supplies the domain and alphabets; `K` carries retained parameters.
    (A : Interface) {K : Type}
    -- `f k i x` is the parameter's reply at port `i`; `k` stays unchanged.
    (f : K → ∀ i, A.X i → A.Y i) (k : K) :
    (A.automatonDDS (fun k i x => (k, f k i x)) k).1 =
      (DDS.ofFunction A.domain A.nonempty_prefix (fun x => ⟨x.1, f k x.1 x.2⟩)).1 := by
  classical
  -- Every input leaves the retained parameter unchanged.
  have hs (xs : List (Σ i, A.X i)) : stateAfter (fun k i x => (k, f k i x)) k xs = k := by
    induction xs using List.reverseRecOn with
    | nil => rfl
    | append_singleton xs x ih => exact (stateAfter_snoc _ _ _ _).trans ih
  -- Both DDSs answer the latest input exactly on the declared domain.
  funext xs
  simp only [Interface.automatonDDS, filterDom, automatonSystem, hs, DDS.ofFunction]

/-- Sample `s ← initial` once and update it with `step`; later queries draw nothing.
The resulting typed system has interface and domain `T`. -/
noncomputable def TypedSystem.ofAutomaton
    -- `initial` supplies the law of the retained starting state `s : S`.
    (initial : Distribution.ProbDist S) : TypedSystem T :=
  TypedSystem.ofPDS ⟨Distribution.fTransform (automatonDDS T step) initial.1,
    Distribution.fTransform_isProbDist _ initial.2⟩

/-- `Pr[h]` is the `initial`-mass of states whose automaton answers the transcript `h`. -/
lemma TypedSystem.ofAutomaton_mass
    -- `initial` is the law of the starting state `s : S`.
    (initial : Distribution.ProbDist S)
    -- `h` pairs the `k`-th tagged query with the `k`-th tagged reply on `T`.
    (h : List ((Σ i, T.X i) × (Σ i, T.Y i))) :
    (TypedSystem.ofAutomaton T step initial).1 h = initial.1.mass fun s =>
      Replies (filterDom T.domain (automatonSystem step s)) (h.map Prod.fst) (h.map Prod.snd) := by
  -- Pull the transcript event back from deterministic systems to their initial states.
  change behaviorMass _ _ _ = _
  rw [behaviorMass, Distribution.mass_fTransform]
  rfl

/-- Pointwise equality of initialized automata gives equality of their sampled typed systems.
The same law and domain are used for both representations. -/
lemma TypedSystem.ofAutomaton_map_congr
    -- `A` fixes the ports and admitted histories; `Ω` carries draws; `S`, `S'` carry states.
    {A : Interface} {Ω S S' : Type}
    -- `step` and `step'` turn a state and a query at port `i` into a new state and reply.
    (step : S → (i : A.I) → A.X i → S × A.Y i)
    (step' : S' → (i : A.I) → A.X i → S' × A.Y i)
    -- `P` is the law of one draw `ω : Ω`; `init`, `init'` build the corresponding states.
    (P : Distribution.ProbDist Ω) (init : Ω → S) (init' : Ω → S')
    -- `same` equates the deterministic systems for every retained draw `ω`.
    (same : ∀ ω, automatonSystem step (init ω) = automatonSystem step' (init' ω)) :
    ofAutomaton A step (Distribution.ProbDist.map init P) =
      ofAutomaton A step' (Distribution.ProbDist.map init' P) := by
  -- Each transcript has the mass of draws whose initialized automaton produces it.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  simp only [ofAutomaton_mass, Distribution.ProbDist.map, Distribution.mass_fTransform]
  -- The component equation equates those events under the same law `P`.
  apply Distribution.mass_congr
  intro ω
  rw [same]

/-- Parallel composition uses `parallelStep f g` and independent initial law `prodProbDist P Q`.
A query changes only the state of its selected component. -/
lemma TypedSystem.parallel_ofAutomaton
    -- `A`, `B` are the component interfaces; `S`, `T` carry their retained states.
    {A B : Interface} {S T : Type}
    -- `f`, `g` update their component state and return a reply at the queried port.
    (f : S → (i : A.I) → A.X i → S × A.Y i) (g : T → (j : B.I) → B.X j → T × B.Y j)
    -- `P`, `Q` independently initialize the two states, each retained across later queries.
    (P : Distribution.ProbDist S) (Q : Distribution.ProbDist T) :
    parallel (ofAutomaton A f P) (ofAutomaton B g Q) =
      ofAutomaton (tensor A B) (parallelStep f g) (Distribution.prodProbDist P Q) := by
  -- Both cumulative laws are measured over the same independent starting states `(s, t)`.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [parallel_mass_of_presentations _ _ P.1 Q.1
      (fun s => filterDom A.domain (automatonSystem f s))
      (fun t => filterDom B.domain (automatonSystem g t))
      (ofAutomaton_mass A f P) (ofAutomaton_mass B g Q),
    ofAutomaton_mass]
  -- At each `(s, t)`, parallel deterministic automata follow exactly `parallelStep f g`.
  refine Distribution.mass_congr _ fun st => ?_
  rw [parallel_automatonSystem f g A.nonempty_prefix B.nonempty_prefix]

end SystemAlgebra
