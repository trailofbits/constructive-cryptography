import RandomSystems.Converter.QueryRouting
import RandomSystems.Typed.CallFunctional

/-!
# Typed realization of input-dependent routing

The router of `RandomSystems.Converter.QueryRouting`, attached to the fixed function `f` on the
inside interface `B`, is the fixed function `g` on the outside interface `A`. With
`(j,x) = request u`, the router computes `g(u) = answer u (j, f_j(x))`. The explicit answer map
lets the reply alphabets `B.Y j` differ from `A.Y o` and from each other.

```text
                ┌───────────────────────┐            ┌────────────┐
  o(v)      ──► │ (j,x) = request u     │ ── j(x) ─► │            │
                │ retain u = (o,v)      │            │ y = f_j(x) │
  o ⇒ g(u)  ◄── │ g(u) = answer u (j,y) │ ◄─ j ⇒ y ─ │            │
                └───────────────────────┘            └────────────┘
```

## Main results

* `TypedConverter.ofDDC_routingConverter_smul_ofFunction`: `α • ofFunction f = ofFunction g`

Source: CR18, Definition 3.9.
-/

namespace SystemAlgebra.TypedConverter

/-- **The router attached to a fixed function**: if `(j,x) = request u`, the router `α` on the
outside domain `A.domain`, attached to `f`, is the function `g(u) = answer u (j, f_j(x))`:
`α • ofFunction f = ofFunction g`. The domain guarantee `ha` comes from
`routingConverter_isDDCFrom` with `F = A.domain`, `E = B.domain`, given
`F us → E (us.map request)`.

CR18, Definition 3.9, printed p. 62: “Whenever α outputs (in, x), then x is given as input
to s⊥, and if y ∈ Y ∪ {⊥} is the output of s⊥, then y is given as input to α. Whenever α
outputs (out, v), then v is defined to be the output of αs ...” -/
lemma ofDDC_routingConverter_smul_ofFunction {A B : Interface}
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    (ha : IsDDCFrom B.domain A.domain 1
      (routingConverter request answer A.domain))
    (f : ∀ j, B.X j → B.Y j) :
    ofDDC (routingConverter request answer A.domain) ha • TypedSystem.ofFunction f =
      TypedSystem.ofFunction (fun o u => answer ⟨o, u⟩
        ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩) := by
  -- A DDC that answers every admitted history like `g`, querying `f` at `[request u]`,
  -- turns `f` into `g` (the typed attachment law `ofDDC_smul_ofFunction`).
  apply ofDDC_smul_ofFunction ha f
    (fun o u => answer ⟨o, u⟩
      ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩)
    (fun u => [request u])
  -- The completed transcript of each admitted history is `replies_routingConverter_ofFunction`.
  intro us hUs
  simpa only [List.map_singleton, Sigma.eta] using
    replies_routingConverter_ofFunction request answer A.nonempty_prefix.2 f us hUs

end SystemAlgebra.TypedConverter
