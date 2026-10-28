import RandomSystems.Converter.CallRuleTranscript
import RandomSystems.Typed.CallFunctional

/-!
# Fixed-function realization of direct calls

The direct call rule is a complete-history DDC. A pointwise schedule against a fixed inside
function gives the completed-call transcript needed by the existing typed attachment theorem.
-/

namespace SystemAlgebra.TypedConverter

/-- A certified direct-call DDC computes the indicated outside function when each inside reply
comes from `f`. Jost, Definition 2.2.2, printed pp. 17–18: “Upon an input at an outside interface,
the converter is allowed to make a bounded number of queries to the inside interfaces ... before
returning a value at the queried interface.” The certificate `ha` supplies that bound and the
domain obligations; the pointwise equations supply the actual fixed-function behavior. -/
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
  -- The outside domain passes through the restricted canonical call transcript.
  apply ofDDC_smul_ofFunction ha f g queries
  intro us hUs
  exact replies_callConverter_of_schedule call A.domain A.nonempty_prefix.2 f g queries
    hquery hreturn us hUs

end SystemAlgebra.TypedConverter
