import RandomSystems.Converter.QueryRouting
import RandomSystems.Typed.CallFunctional

/-!
# Typed realization of input-dependent routing

The systems-level router moves a port choice from an input value into the inside port label.
Its typed attachment forwards the request and returns the translated answer at the original
outside port. The answer translation is explicit, so output alphabets may be heterogeneous.
-/

namespace SystemAlgebra.TypedConverter

/-- A certified router attached to a fixed inside function computes the routed outside
function. The certificate includes the exact request-map domain obligation. -/
lemma ofDDC_routingConverter_smul_ofFunction {A B : Interface}
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    (ha : IsDDCFrom B.domain A.domain 1
      (routingConverter request answer A.domain))
    (f : ∀ j, B.X j → B.Y j) :
    ofDDC (routingConverter request answer A.domain) ha • TypedSystem.ofFunction f =
      TypedSystem.ofFunction (fun o u => answer ⟨o, u⟩
        ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩) := by
  -- The systems-level completed-call witness supplies every admitted outside history.
  apply ofDDC_smul_ofFunction ha f
    (fun o u => answer ⟨o, u⟩
      ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩)
    (fun u => [request u])
  intro us hUs
  simpa only [List.map_singleton, Sigma.eta] using
    replies_routingConverter_ofFunction request answer A.nonempty_prefix.2 f us hUs

end SystemAlgebra.TypedConverter
