module

public import RandomSystems.Converter.QueryBound
public import Tests.SerialAccounting

/-! Existing forwarding and direct calls retain bounds on partial transcripts and exact domains. -/

@[expose] public section

namespace SystemAlgebra.Tests.ConverterQueryBound

open DirectCalls SerialAccounting

/-- Restricting Boolean identity to one input preserves its total-query bound. -/
example : InsideQueriesBounded
    (filterDom (fun xs => xs.length ≤ 1)
      (idConverter Unit (fun _ => Bool) (fun _ => Bool))) id :=
  insideQueriesBounded_id.of_le (fun xs y hy => (filterDom_mem_iff _ _ xs y).mp hy |>.2)

/-- The actual pending query rules out a zero total-query bound. -/
lemma pending_not_zero : ¬ InsideQueriesBounded (canon natRule) (fun _ => 0) := by
  intro bound
  have count := bound interrupted interrupted_replies
  simp only [interrupted, List.map_cons, List.map_nil, insideQueries_inside,
    List.length_cons, List.length_nil] at count
  exact Nat.not_succ_le_zero 0 count

/-- Two existing two-call converters have a four-query bound and preserve their exact domains. -/
lemma two_calls_bound_and_domain :
    let β := callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
      (boolInterface 1).domain
    let α := callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
      (boolInterface 2).domain
    InsideQueriesBounded (trim (serialM β α)) (fun _ => 4) ∧
      MapsDomain (boolInterface 4).domain (boolInterface 1).domain (trim (serialM β α)) := by
  have outer := toggleCall_isDDCFrom_queryBudget 1
  have inner := toggleCall_isDDCFrom_queryBudget 2
  constructor
  · exact InsideQueriesBounded.comp outer inner
      (outer.insideQueriesBounded_of_domain (fun _ hx => hx.2))
      (inner.insideQueriesBounded_of_domain (fun _ hx => hx.2)) monotone_const
  · exact (outer.comp inner).mapsDomain (boolInterface 1).nonempty_prefix

#print axioms SystemAlgebra.InsideQueriesBounded.of_le
#print axioms SystemAlgebra.insideQueriesBounded_id
#print axioms SystemAlgebra.IsDDCFrom.insideQueriesBounded_of_domain
#print axioms SystemAlgebra.InsideQueriesBounded.comp
#print axioms pending_not_zero
#print axioms two_calls_bound_and_domain

end SystemAlgebra.Tests.ConverterQueryBound
