module

public import Probability.PinnedProduct
public import RandomSystems.Typed.Functional
public import RandomSystems.Typed.ProbAutomaton

/-!
# Random functions with prescribed coordinate laws

`randomFunction A μ` draws one table with independent entries `f i x ∼ μ i x`, then
answers every admitted query `i(x)` with the retained value `f i x`. The domain is `A.domain`.
Thus repeating an input reads the same draw, while distinct coordinates are independent.
`randomFunction.lazy` samples a coordinate only when first queried and records its reply.
`randomFunction.completionLaw` fills the other entries with their independent laws;
the correspondence is proved in `Commons.Definitions.RandomFunction.Laws`.
`Commons.URF.eq_randomFunction` in `Commons.Definitions.Ideal` identifies uniform coordinates
with the existing uniform random function.

This is the finite-alphabet form of [1, Definition 6, p. 12]: "each O(x) for x ∈ D is
sampled independently", with a specified law at each coordinate.

## References

1. G. Herold, D. Khovratovich, M. Kudinov, S. Tessaro, B. Wagner.
   *Aborting Random Oracles: How to Build them, How to Use them.* 2026. ePrint 2026/016.
-/

@[expose] public section

namespace Commons

open SystemAlgebra Probability Probability.Distribution

/-- Draw `f ∼ ⨂ᵢ ⨂ₓ μ i x` once; answer every admitted `i(x)` with `f i x`. -/
noncomputable def randomFunction
    -- `A` supplies ports, finite query/reply alphabets and the admitted input histories.
    (A : Interface)
    -- `μ i x` is the normalized law of the retained reply at port `i` and input `x`.
    (μ : ∀ i, A.X i → ProbDist (A.Y i)) : TypedSystem A :=
  TypedSystem.sample (ProbDist.piDep (fun i => ProbDist.piDep (μ i))).1
    TypedSystem.ofFunction

namespace randomFunction

-- `A` fixes ports and finite alphabets; `μ i x` is the retained entry law at input `i(x)`.
variable (A : Interface) (μ : ∀ i, A.X i → ProbDist (A.Y i))

open Classical in
/-- Return the recorded value with certainty on a hit, and draw from `μ i x` on a miss. -/
noncomputable def replyLaw
    -- `table i` records the replies already chosen at port `i`.
    (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i) : ProbDist (A.Y i) :=
  ((table i).lookup x).elim (μ i x) ProbDist.single

/-- Sample the reply law and record `(x,y)` at the queried port exactly on a miss. -/
noncomputable def tableLaw : ProbStep (∀ i, List (A.X i × A.Y i)) A.I A.X A.Y :=
  ProbStep.recordReplies (replyLaw A μ)

/-- Start with empty records; each new input draws its reply once from its coordinate law.
[1, Remark 2, p. 12]: "lazy sampling" retains the reply for subsequent queries. -/
noncomputable def lazy : TypedSystem A :=
  TypedSystem.ofProbAutomaton A (tableLaw A μ) (ProbDist.single (fun _ => []))

open Classical in
/-- Complete a record table with independent `μ` entries, pinning every recorded reply. -/
noncomputable def completionLaw
    -- `table` prescribes the already observed coordinates of the completed function.
    (table : ∀ i, List (A.X i × A.Y i)) :
    ProbDist (∀ q : Σ i, A.X i, A.Y q.1) :=
  ProbDist.pinnedProduct (fun q : Σ i, A.X i => μ q.1 q.2)
    (fun q => (table q.1).lookup q.2)

end randomFunction

end Commons
