import RandomSystems.Typed.QueryRouting

/-!
# Input-dependent routing regression

The first Boolean of an outside payload selects the inside port; the second Boolean becomes
the inside query. A label-only renaming cannot express this value-dependent choice.
-/

namespace SystemAlgebra.Tests.QueryRouting

def outside : Interface := Interface.queryBudget Unit (fun _ => Bool × Bool) (fun _ => Bool) 1
def inside : Interface := Interface.queryBudget Bool (fun _ => Bool) (fun _ => Bool) 1

def request (u : Σ o, outside.X o) : Σ j, inside.X j := ⟨u.2.1, u.2.2⟩
def answer (u : Σ o, outside.X o) (r : Σ j, inside.Y j) : outside.Y u.1 := r.2

/-- The value-dependent request preserves the exact one-query domain. -/
lemma request_domain (us : List (Σ o, outside.X o)) (hu : outside.domain us) :
    inside.domain (us.map request) := by
  exact ⟨fun he => hu.1 (List.map_eq_nil_iff.mp he),
    (List.length_map request).trans_le hu.2⟩

/-- The direct router has its exact domain certificate, including the payload-to-port map. -/
theorem certified : IsDDCFrom inside.domain outside.domain 1
    (routingConverter request answer outside.domain) :=
  routingConverter_isDDCFrom request answer outside.nonempty_prefix request_domain

/-- A routed identity oracle returns the query's Boolean at the original outside port. -/
example : TypedConverter.ofDDC (routingConverter request answer outside.domain) certified •
    TypedSystem.ofFunction (A := inside) (fun (_ : Bool) (x : Bool) => x) =
    TypedSystem.ofFunction (A := outside) (fun (_ : Unit) (u : Bool × Bool) => u.2) := by
  have hg : (fun o u => answer ⟨o, u⟩
      ⟨(request ⟨o, u⟩).1, (request ⟨o, u⟩).2⟩) =
      (fun (_ : Unit) (u : Bool × Bool) => u.2) := by
    funext o u
    rfl
  rw [← hg]
  exact TypedConverter.ofDDC_routingConverter_smul_ofFunction request answer certified
    (fun (_ : Bool) (x : Bool) => x)

end SystemAlgebra.Tests.QueryRouting
