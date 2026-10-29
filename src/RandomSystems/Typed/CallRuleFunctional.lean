import RandomSystems.Converter.CallRuleTranscript
import RandomSystems.Typed.CallFunctional

/-!
# Direct calls against fixed functions

A certified direct-call converter `callConverter call A.domain` whose rule follows a schedule
`queries u` against the fixed inside function `f` and returns `g u` computes `g` from `f`. The
schedule depends on `f` and `u`; each inside query may depend on the earlier replies of its
invocation.

```text
  schedule of call  →  transcript of callConverter            replies_callConverter_of_schedule
                    →  ofDDC … • ofFunction f = ofFunction g  ofDDC_smul_ofFunction
```

## Main results

* `ofDDC_callConverter_smul_ofFunction`: the typed equation, through the existing deterministic
  attachment
-/

namespace SystemAlgebra.TypedConverter

/-- A certified direct-call DDC computes `g` from `f` when, against the replies of `f`, its rule
issues the queries `queries u` and then returns `g u`. Jost, Definition 2.2.2, printed
pp. 17–18: “Upon an input at an outside interface, the converter is allowed to make a bounded
number of queries to the inside interfaces ... before returning a value at the queried
interface.” The certificate `ha` supplies that bound and the domain obligations; the schedule
equations supply the fixed-function behavior. -/
lemma ofDDC_callConverter_smul_ofFunction {A B : Interface}
    (call : (u : Σ o, A.X o) → List (Σ j, B.Y j) → A.Y u.1 ⊕ (Σ j, B.X j))
    {bound : Nat}
    (ha : IsDDCFrom B.domain A.domain bound (callConverter call A.domain))
    (f : ∀ j, B.X j → B.Y j) (g : ∀ o, A.X o → A.Y o)
    (queries : (Σ o, A.X o) → List (Σ j, B.X j))
    (hquery : ∀ u n (hn : n < (queries u).length),
      call u (((queries u).take n).map fun x => ⟨x.1, f x.1 x.2⟩) =
        .inr (queries u)[n])
    (hreturn : ∀ u, call u ((queries u).map fun x => ⟨x.1, f x.1 x.2⟩) =
      .inl (g u.1 u.2)) :
    ofDDC (callConverter call A.domain) ha • TypedSystem.ofFunction f =
      TypedSystem.ofFunction g := by
  -- Every outside history in the domain has the scheduled transcript of the converter.
  apply ofDDC_smul_ofFunction ha f g queries
  intro us hUs
  exact replies_callConverter_of_schedule call A.domain A.nonempty_prefix.2 f g queries
    hquery hreturn us hUs

end SystemAlgebra.TypedConverter
