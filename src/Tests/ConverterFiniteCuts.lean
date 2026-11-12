module

public import RandomSystems.Converter.FiniteCuts
public import Tests.DirectCalls

/-! The certified two-query call retains exact domains after positive and zero outside cuts. -/

@[expose] public section

namespace SystemAlgebra.Tests.ConverterFiniteCuts

open DirectCalls

/-- The existing two-query Boolean call on its one-query outside domain. -/
noncomputable abbrev toggle :=
  callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall (boolInterface 1).domain

/-- Every cutoff of the actual call has the exact intersected domains. -/
lemma toggle_cut (q : ℕ) :
    IsDDCFrom (fun xs => (boolInterface 2).domain xs ∧ xs.length ≤ 2)
      (fun us => (boolInterface 1).domain us ∧ us.length ≤ q) 2
      (filterDom (fun xs => (outsideInputs xs).length ≤ q) toggle) :=
  toggleCall_isDDCFrom.filterDom_of_insideQueriesBounded
    (toggleCall_isDDCFrom.insideQueriesBounded_of_domain (fun _ hx => hx.2)) monotone_const q

/-- Domain preservation uses the existing contract with explicit prefix closure of the cutoff. -/
lemma toggle_cut_mapsDomain :
    MapsDomain (fun xs => (boolInterface 2).domain xs ∧ xs.length ≤ 2)
      (fun us => (boolInterface 1).domain us ∧ us.length ≤ 1)
      (filterDom (fun xs => (outsideInputs xs).length ≤ 1) toggle) := by
  apply (toggle_cut 1).mapsDomain
  refine ⟨fun h => (boolInterface 1).nonempty_prefix.1 h.1, ?_⟩
  intro p h hp hn hh
  exact ⟨(boolInterface 1).nonempty_prefix.2 hp hn hh.1, hp.length_le.trans hh.2⟩

/-- A zero outside horizon is still certified on the exact empty outside domain. -/
example : IsDDCFrom (fun xs => (boolInterface 2).domain xs ∧ xs.length ≤ 2)
    (fun us => (boolInterface 1).domain us ∧ us.length ≤ 0) 2
    (filterDom (fun xs => (outsideInputs xs).length ≤ 0) toggle) := toggle_cut 0

/-- The zero-horizon converter has no answer to its first outside input. -/
lemma zero_no_reply :
    ¬ (filterDom (fun xs => (outsideInputs xs).length ≤ 0) toggle
      [⟨⟨none, ()⟩, false⟩]).Dom := by
  rw [filterDom_dom]
  rintro ⟨bound, _⟩
  simp only [outsideInputs_outside, List.length_cons, List.length_nil] at bound
  exact Nat.not_succ_le_zero 0 bound

#print axioms SystemAlgebra.IsDDCFrom.filterDom_of_insideQueriesBounded
#print axioms toggle_cut
#print axioms toggle_cut_mapsDomain
#print axioms zero_no_reply

end SystemAlgebra.Tests.ConverterFiniteCuts
