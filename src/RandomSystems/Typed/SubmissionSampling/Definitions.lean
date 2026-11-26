module

public import RandomSystems.Typed.Submission

/-!
# Sampled submission solvers

`Submission.distinguisher x` submits `x`, receives its acknowledgment, and stops with decision
`false`. The game scores its hidden event independently of that decision.
`TypedSolver.submission P` selects this observer once with `P.map Submission.distinguisher`.
Thus a product-valued submission preserves every correlation in the supplied law `P`.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

/-- Ask for `x` once, then stop and output `false`:
`envProbe (DDE.ofQueries [⟨(), x⟩]) (fun _ => False)`. -/
noncomputable def Submission.distinguisher
    -- `X` is the finite submission alphabet; `x` is the submitted value.
    {X : Type} [Fintype X] (x : X) :
    {D : DDD (Interface.submission X).I (Interface.submission X).X
      (Interface.submission X).Y // IsDDD D ∧
        (Interface.submission X).inputDomain.DecisionCompatible D} :=
  ⟨envProbe (DDE.ofQueries [⟨(), x⟩]) (fun _ => False),
    envProbe_isDDD (DDE.ofQueries_queryBounded
      (X := Σ _ : Unit, X) (Y := Σ _ : Unit, Unit) [⟨(), x⟩]),
    Domain.envProbe_decisionCompatible (by
      intro R hR h query follows possible submitted
      rw [Interface.queryBudget_inputDomain_iff]
      -- Every query of the singleton observer occurs before its first reply.
      simpa only [List.length_map, List.length_cons, List.length_nil] using
        DDE.ofQueries_queryBounded (X := Σ _ : Unit, X) (Y := Σ _ : Unit, Unit)
          [⟨(), x⟩]
          (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨query, submitted⟩)) _⟩

/-- Draw `x ∼ P` once, submit it, receive `()`, and stop.

```text
x ∼ P ── submit x ──▶ game ── () ──▶ stop
```
-/
noncomputable def TypedSolver.submission
    -- `P` is the joint law of the submitted value in the finite alphabet `X`.
    {X : Type} [Fintype X] (P : ProbDist X) : TypedSolver (Interface.submission X) :=
  TypedSolver.ofDistinguisher (P.map Submission.distinguisher)

end SystemAlgebra
