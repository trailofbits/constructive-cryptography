module

public import Commons.Definitions.Ideal
public import RandomSystems.Typed.QueryRouting
public import RandomSystems.Typed.SamplingAlgebra

/-!
# Shared access to a retained function

`Evaluation.share` routes two evaluation callers to one function with their combined query
allowance. `share_smul_ofFunction` identifies its two views of a fixed function.
`randomFunction_eq_sample` presents the one-port random function by its single retained table.
Together these laws keep that table shared when the callers observe different functions of it.

```text
  eval(z), allowance q ─┐    ┌──────────────────────┐
                       ├───►│ one retained f : D → X │
  eval(z), allowance r ─┘    └──────────────────────┘
                               allowance q + r
```
-/

@[expose] public section

namespace Commons.Evaluation

open SystemAlgebra Probability Probability.Distribution

-- `D` is the finite input alphabet and `X` the finite reply alphabet.
variable (D X : Type) [Fintype D] [Fintype X]

/-- The single-port resource draws `f ∼ ∏ z, μ z` once and answers `eval(z)` with `f z`. -/
lemma randomFunction_eq_sample
    -- `q` bounds admitted queries; `μ z` is the law of the retained reply at `z`.
    (q : ℕ) (μ : D → ProbDist X) :
    randomFunction (Evaluation D X q) (fun _ => μ) =
      TypedSystem.sample (ProbDist.piDep μ).1
        (fun f => TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f)) := by
  classical
  have selected : (ProbDist.piDep (fun _ : Evaluation.Port => ProbDist.piDep μ)).map
      (fun f => f .eval) = ProbDist.piDep μ := by
    apply Subtype.ext
    change fTransform _ (piDep _) = _
    rw [piDep_eq_pi]
    exact congrArg Subtype.val (ProbDist.map_pi_apply
      (fun _ : Evaluation.Port => ProbDist.piDep μ) .eval)
  -- Selecting the only port leaves its entire retained input table.
  calc
    _ = TypedSystem.sample (ProbDist.piDep (fun _ : Evaluation.Port => ProbDist.piDep μ)).1
        (fun f => TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f .eval)) := by
      apply congrArg (TypedSystem.sample _)
      funext f
      congr 1
    _ = TypedSystem.sample
        ((ProbDist.piDep (fun _ : Evaluation.Port => ProbDist.piDep μ)).map
          (fun f => f .eval)).1
        (fun f => TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f)) :=
      (TypedSystem.sample_fTransform (fun f : Evaluation.Port → D → X => f .eval)
        (ProbDist.piDep (fun _ : Evaluation.Port => ProbDist.piDep μ)).1
        (fun f : D → X => TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f))).symm
    _ = _ := congrArg (fun law : ProbDist (D → X) => TypedSystem.sample law.1
      (fun f => TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f))) selected

/-- Route both callers' `eval(z)` to the same inside `eval(z)`, preserving the reply.
The outside allowances are `q,r`; their shared inside allowance is `q+r`. -/
noncomputable def share (q r : ℕ) :
    TypedConverter ((Evaluation D X q).tensor (Evaluation D X r))
      (Evaluation D X (q + r)) :=
  TypedConverter.routingAt
    (fun | ⟨.inl _, z⟩ => ⟨.eval, z⟩ | ⟨.inr _, z⟩ => ⟨.eval, z⟩)
    (fun u y => match u with | ⟨.inl _, _⟩ => y | ⟨.inr _, _⟩ => y)
    (fun _ admitted => Interface.queryBudget_domain_map _ (le_refl (q + r)) admitted)

/-- Sharing a fixed `f` gives two evaluation views of that same function. -/
lemma share_smul_ofFunction (q r : ℕ) (f : D → X) :
    share D X q r • TypedSystem.ofFunction (A := Evaluation D X (q + r)) (fun _ => f) =
      TypedSystem.parallel
        (TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f))
        (TypedSystem.ofFunction (A := Evaluation D X r) (fun _ => f)) := by
  rw [share, TypedConverter.routingAt_smul_ofFunction, TypedSystem.parallel_ofFunction]
  congr 1
  funext i z
  cases i <;> rfl

end Commons.Evaluation
