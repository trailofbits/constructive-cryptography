module

public import RandomSystems.Converter.ProgramTrace
public import Tests.ProgramCostDomain

/-!
# Pending program queries

The existing forwarder emits `7` before receiving an inside reply. The query witness identifies
a reached prefix with that pending query. A return-only program emits no inside request.
-/

@[expose] public section

namespace Tests.ProgramIssuedQuery

open SystemAlgebra SystemAlgebra.DSL
open Tests.ProgramCostDomain

/-- The single outside input is `7`; the sole converter output is the pending inside query `7`. -/
lemma pending_query_has_prefix :
    let u : Σ l : Two Unit Unit, twoFam (fun _ => ℕ) (fun _ => ℕ) l := ⟨⟨none, ()⟩, 7⟩
    ∃ xs, xs <+: [u] ∧ ∃ o state, ∃ n : ℕ, ∃ exchanges,
      forward.after () xs = some (.busy o state n exchanges ⟨(), 7⟩) := by
  intro u
  let v : Σ l : Two Unit Unit, twoFam (fun _ => ℕ) (fun _ => ℕ) l :=
    ⟨⟨some (), ()⟩, 7⟩
  have replied : Replies (DDC.ofProgram () forward) [u] [v] :=
    (DDC.replies_ofProgramOn (h := [(u, v)]) pending_cost.1).1
  apply DDC.exists_after_busy_of_mem_insideQueries (h := [(u, v)]) replied
  rw [List.map_cons, List.map_nil, insideQueries_inside]
  exact List.mem_singleton_self _

example : forward.after () [⟨⟨none, ()⟩, 7⟩] =
    some (.busy () () 7 [] ⟨(), 7⟩) := rfl

/-- Return the current input `n` immediately, retaining unit state and making no inside call. -/
def direct : Program Unit Unit Unit (fun _ => ℕ) (fun _ => ℕ)
    (fun _ => ℕ) (fun _ => ℕ) :=
  fun state _ n => returnProg (state, n)

/-- The direct reply is a legal converter transcript, with an empty inside-query history. -/
lemma direct_reply :
    let u : Σ l : Two Unit Unit, twoFam (fun _ => ℕ) (fun _ => ℕ) l := ⟨⟨none, ()⟩, 7⟩
    Replies (DDC.ofProgram () direct) [u] [u] ∧ insideQueries [u] = [] := by
  intro u
  refine ⟨?_, insideQueries_outside () 7⟩
  apply (replies_snoc (xs := []) (ys := [])).mpr
  refine ⟨replies_nil _, ?_⟩
  rfl

#print axioms SystemAlgebra.DDC.exists_after_busy_of_mem_insideQueries
#print axioms pending_query_has_prefix
#print axioms direct_reply

end Tests.ProgramIssuedQuery
