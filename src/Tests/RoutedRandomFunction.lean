module

public import RandomSystems.Typed.RandomFunction

/-!
# Retained table routing

Two caller ports share a Boolean table. Repeating one caller's query preserves the table law;
two different caller tags sent to the same entry violate the collision-free hypothesis.
-/

@[expose] public section

namespace Tests.RoutedRandomFunction

open SystemAlgebra Probability.Distribution

/-- Two callers each submit a Boolean query and receive a Boolean reply; at most two calls. -/
abbrev callers := Interface.queryBudget Bool (fun _ => Bool) (fun _ => Bool) 2

/-- Ignore the caller tag when choosing the retained table entry. -/
def entry (x : Σ i, callers.X i) : Bool := x.2

/-- Both calls read the same entry, so the router law applies to their repeated input. -/
example (x : Σ i, callers.X i) (y z : Σ i, callers.Y i) :
    (TypedSystem.sample (ProbDist.piDep fun _ : Bool => 𝒰[Bool]).1
      (fun table => TypedSystem.ofFunction (A := callers)
        (fun i v => table (entry ⟨i, v⟩)))).1 [(x, y), (x, z)] =
    (TypedSystem.sample
      (ProbDist.piDep fun _ : Σ i, callers.X i => (𝒰[Bool]).map id).1
      (fun table => TypedSystem.ofFunction (A := callers)
        (fun i v => table ⟨i, v⟩))).1 [(x, y), (x, z)] := by
  apply TypedSystem.sample_piDep_comp_mass_eq (fun _ => 𝒰[Bool]) entry (fun _ => id)
  intro a ha b hb _
  have hax : a = x := by simpa only [List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, or_self, Set.mem_ofPred_eq] using ha
  have hbx : b = x := by simpa only [List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, or_self, Set.mem_ofPred_eq] using hb
  exact hax.trans hbx.symm

/-- Distinct caller-tagged inputs sent to one entry trigger a collision. -/
example : ¬ Set.InjOn entry
    ({⟨false, false⟩, ⟨true, false⟩} : Set (Σ i, callers.X i)) := by
  intro hinj
  have he := hinj (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _)) rfl
  have hb : false = true := congrArg Sigma.fst he
  cases hb

#print axioms TypedSystem.sample_piDep_comp_mass_eq
#print axioms TypedConverter.routing_smul_sample_piDep_mass_eq

end Tests.RoutedRandomFunction
