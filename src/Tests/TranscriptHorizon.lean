import ConstructiveCryptography.Notation

/-! # Strategy prefixes and completed observation horizons

The prefix rule checks a query directly after its preceding replies. A two-query environment
provides a positive one-exchange transcript and a negative transcript past its truncation
limit. The final check reads the fixed-domain-horizon formula through the selected CC distance,
with compatibility and the environment's global stopping bound still explicit.
-/

namespace SystemAlgebra.Tests.TranscriptHorizon

open Probability
open scoped SystemAlgebra

/-- Every exchange prefix identifies the strategy's next query without indexing the transcript. -/
example {A B : Type} {σ : List B →. A} {h pre : List (A × B)} {x : A} {y : B}
    (hc : FollowsStrategy σ h) (hp : pre ++ [(x, y)] <+: h) :
    x ∈ σ (pre.map Prod.snd) := hc pre (x, y) hp

/-- Query `false`, then `true`, ignoring replies; one exchange remains valid at the limit `1`. -/
example : FollowsStrategy (DDE.limitQueries (DDE.ofQueries [false, true]) 1).1
    [(false, true)] := by
  apply FollowsStrategy.limitQueries_iff.mpr
  refine ⟨FollowsStrategy.snoc_iff.mpr ⟨FollowsStrategy.nil, ?_⟩, le_rfl⟩
  exact Part.mem_some _

/-- The same environment cut after one query cannot produce a two-exchange transcript. -/
example : ¬ FollowsStrategy (DDE.limitQueries (DDE.ofQueries [false, true]) 1).1
    [(false, true), (true, false)] := by
  intro hc
  have hl := (FollowsStrategy.limitQueries_iff.mp hc).2
  exact Nat.not_succ_le_self 1 hl

/-- A zero-query limit stops even on reply histories where the original environment continues. -/
example {A B : Type} (E : DDE A B) (ys : List B) :
    (DDE.limitQueries E 0).1 ys = Part.none := by
  simp only [DDE.limitQueries, limitQueries, Nat.not_lt_zero, if_false]

/-- The typed CC distance needs only the interface domain bound; the permitted environments
remain compatible with the domain and globally stop within that bound. -/
example {A : Interface} (R S : TypedSystem A) :
    Δ R S =
      ⨆ (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (_ : QueryBounded A.inputDomain.bound E)
        (_ : A.inputDomain.Compatible E),
        ENNReal.ofReal (statDist (R.1.sLaw E.1 A.inputDomain.bound)
          (S.1.sLaw E.1 A.inputDomain.bound)) :=
  RandomSystem.transcriptDistance_eq_iSup_domainBound R.2 S.2

end SystemAlgebra.Tests.TranscriptHorizon
