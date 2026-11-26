module

public import RandomSystems.Typed.Functional
public import RandomSystems.Typed.Automaton
public import RandomSystems.Typed.Filter

/-!
# Functional DDS presentations

Two ports return `Fin 2` and `Fin 3`. Their common domain admits at most two queries, all with
input `false`. The same certified DDS gives the functional system's replies and zero mass on
excluded inputs.
-/

@[expose] public noncomputable section

namespace Tests.FunctionalPresentation

open SystemAlgebra

/-- At most two queries, each `false`; port `i` has reply type `Fin (if i then 3 else 2)`. -/
abbrev queries : Interface :=
  (Interface.queryBudget Bool (fun _ => Bool) (fun i => Fin (if i then 3 else 2)) 2).restrict
    (fun xs => ∀ x ∈ xs, x.2 = false)
    (fun _ _ hp hd x hx => hd x (hp.subset hx))

/-- Port `false` returns 1 in `Fin 2`; port `true` returns 2 in `Fin 3`. -/
def reply : ∀ i, queries.X i → queries.Y i
  | false, _ => 1
  | true, _ => 2

/-- A fixed unit-state component implements those replies on exactly the restricted domain. -/
def presentation := queries.automatonDDS (fun (_ : Unit) i x => ((), reply i x)) ()

/-- The generic law consumes only the certified DDS and its raw functional realization. -/
lemma presentation_eq :
    TypedSystem.ofDeterministic presentation.1 presentation.2 = TypedSystem.ofFunction reply :=
  TypedSystem.ofDeterministic_eq_ofFunction reply presentation.1 presentation.2
    (Interface.automatonDDS_eq_ofFunction queries (fun (_ : Unit) => reply) ())

/-- One legal query at each port has probability one, despite their different reply types. -/
lemma admitted_mass :
    (TypedSystem.ofDeterministic presentation.1 presentation.2).1
      [(⟨false, false⟩, ⟨false, 1⟩), (⟨true, false⟩, ⟨true, 2⟩)] = 1 := by
  rw [presentation_eq]
  apply TypedSystem.ofFunction_mass_eq_one
  · right
    simp [queries, Interface.restrict, Interface.queryBudget]
  · simp [reply]

/-- A syntactically valid query outside the declared input domain has probability zero. -/
lemma excluded_mass :
    (TypedSystem.ofDeterministic presentation.1 presentation.2).1
      [(⟨true, true⟩, ⟨true, 2⟩)] = 0 := by
  apply (TypedSystem.ofDeterministic presentation.1 presentation.2).1.mass_eq_zero_of_not_admitted
    (h := []) (x := ⟨true, true⟩)
  intro admitted
  exact Bool.noConfusion (admitted.2 ⟨true, true⟩ (List.mem_singleton_self _))

#print axioms TypedSystem.ofDeterministic_eq_ofFunction
#print axioms presentation_eq
#print axioms admitted_mass
#print axioms excluded_mass

end Tests.FunctionalPresentation
