module

public import RandomSystems.PDS.FiniteCuts

/-! Deterministic cuts preserve raw partial replies and restrict an existing bounded evaluator. -/

@[expose] public section

namespace Tests.DeterministicFiniteCuts

open SystemAlgebra

/-- A partial system answers only at length two, including histories whose first query is silent. -/
def isolatedReply : System Unit Bool :=
  fun xs => if xs.length = 2 then Part.some true else Part.none

/-- A cut retains the original off-tree reply rather than trimming the partial system. -/
lemma cut_retains_isolated_reply : cutSystem isolatedReply 2 [(), ()] = Part.some true := by
  rw [cutSystem_apply_of_length_le _ _ _ (by rfl)]
  rfl

/-- The shorter cut leaves the same length-two history undefined. -/
lemma cut_removes_later_reply : cutSystem isolatedReply 1 [(), ()] = Part.none :=
  cutSystem_apply_of_bound_lt _ _ _ (by exact Nat.lt_succ_self 1)

/-- The evaluator admits each nonempty Boolean query history through length three. -/
def echoDomain : Domain Bool Bool :=
  Domain.ofInputs (fun xs => xs ≠ [] ∧ xs.length ≤ 3) 3 (fun _ hx => hx.2)

/-- The fixed evaluator returns the current Boolean query unchanged. -/
noncomputable def echo : DDS Bool Bool :=
  DDS.ofFunction (fun xs => xs ≠ [] ∧ xs.length ≤ 3)
    ⟨fun h => h.1 rfl, fun hp hn hh => ⟨hn, hp.length_le.trans hh.2⟩⟩ id

/-- The evaluator answers exactly its declared bounded domain. -/
lemma echo_hasDomain : HasDomain echoDomain echo.1 :=
  HasDomain.ofInputs (DDS.ofFunction_dom _ _ _)

/-- The domain certificate gives the explicit finiteness premise needed for raw cut identity. -/
lemma bounded_echo_cut : cutSystem echo.1 3 = echo.1 :=
  cutSystem_eq_self _ _ (echo_hasDomain.finite echo.2)

/-- The evaluator remains a DDS after observing just one query. -/
example : IsDDS (cutSystem echo.1 1) := echo.2.cutSystem 1

/-- The one-query cut retains the exact transcript-dependent domain contract. -/
example : HasDomain (cutDomain echoDomain 1) (cutSystem echo.1 1) :=
  echo_hasDomain.cutSystem 1

#print axioms SystemAlgebra.cutSystem_cutSystem
#print axioms SystemAlgebra.HasDomain.cutSystem
#print axioms SystemAlgebra.HasDomain.finite
#print axioms SystemAlgebra.cutSystem_eq_self
#print axioms cut_retains_isolated_reply
#print axioms bounded_echo_cut

end Tests.DeterministicFiniteCuts
