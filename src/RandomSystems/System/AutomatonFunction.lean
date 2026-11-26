module

public import RandomSystems.System.Automaton
public import RandomSystems.PDS.Filter

/-!
# Retained functions as deterministic automata

`filterDom_automatonSystem_eq_ofFunction` identifies an automaton retaining a parameter `k`
with the existing DDS for the function it selects. Both presentations use the same declared
domain, including refusal outside that domain. Ports, parameters and message alphabets may
be infinite. The typed presentation in `RandomSystems.Typed.Automaton` uses this identity.
-/

@[expose] public section

namespace SystemAlgebra

/-- Retaining `k` and replying with `f k` gives the same DDS as evaluating that fixed function. -/
lemma filterDom_automatonSystem_eq_ofFunction
    -- `I` labels ports, `K` carries retained parameters, and `X i`, `Y i` carry messages at `i`.
    {I K : Type} {X Y : I → Type}
    -- `E` is the input domain; `hE` excludes empty input and admits nonempty prefixes.
    (E : List (Σ i, X i) → Prop)
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    -- `f k i x` is the reply selected by the unchanged retained value `k`.
    (f : K → ∀ i, X i → Y i) (k : K) :
    filterDom E (automatonSystem (fun k i x => (k, f k i x)) k) =
      (DDS.ofFunction E hE (fun x => ⟨x.1, f k x.1 x.2⟩)).1 := by
  -- The state fold retains the same parameter after every input prefix.
  have retained (xs : List (Σ i, X i)) :
      stateAfter (fun k i x => (k, f k i x)) k xs = k :=
    List.foldl_fixed' (fun _ => rfl) xs
  funext xs
  simp only [filterDom, automatonSystem, retained, DDS.ofFunction]

end SystemAlgebra
