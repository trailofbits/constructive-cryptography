module

public import Commons.Definitions.ConditionalRandomFunction
public import Probability.ConditionalProduct

/-!
# Equality of observed and reconstructed random functions

`reconstruct_eq_observe` identifies the two joint-access assemblies from their coordinate
joint laws. `lookup_smul_parallel_ofFunction` evaluates the two calls on fixed functions;
the sampled presentations then apply `ProbDist.map_prod_piDep_pair_eq_of_jointLaw` once.
A common outside filter preserves this equality by attachment congruence.

## References

1. G. Herold, D. Khovratovich, M. Kudinov, S. Tessaro, and B. Wagner.
   Aborting Random Oracles: How to Build them, How to Use them.
   Cryptology ePrint Archive, Paper 2026/016, July 17, 2026.
-/

@[expose] public section

namespace Commons.ConditionalRandomFunction

open SystemAlgebra Probability Probability.Distribution CategoryTheory
open scoped SystemAlgebra CategoryTheory

-- `D`, `X`, and `O` carry inputs, latent replies, and observations.
variable (D X O : Type) [Fintype D] [Fintype X] [Fintype O]

/-- The two point-law calls compute the private entry indexed by the observed reply. -/
lemma lookup_smul_parallel_ofFunction (q : ℕ) (f : D → O) (ψ : D × O → X) :
    lookup D X O q • TypedSystem.parallel
      (TypedSystem.ofFunction (A := Evaluation D O q) (fun _ => f))
      (TypedSystem.ofFunction (A := Evaluation (D × O) X (2 * q)) (fun _ => ψ)) =
    TypedSystem.ofFunction (A := Evaluation D X q) (fun _ z => ψ (z, f z)) := by
  change lookup D X O q • TypedSystem.parallel
    (TypedSystem.ofMemoryless (Evaluation D O q) (fun _ z => ProbDist.single (f z)))
    (TypedSystem.ofMemoryless (Evaluation (D × O) X (2 * q))
      (fun _ zo => ProbDist.single (ψ zo))) =
    TypedSystem.ofMemoryless (Evaluation D X q) (fun _ z => ProbDist.single (ψ (z, f z)))
  rw [TypedSystem.parallel_ofMemoryless]
  unfold lookup
  apply TypedConverter.ofPreservingProgram_smul_ofMemoryless _ _ _ _ _ _ _ _ rfl
  intro state port z
  cases port
  rcases state with _ | ⟨⟩
  · rw [lookupCalls.memorylessReplyLaw_eval_initial]
    simp only [RandomSystem.parallelLaw, ProbDist.single, bindK_single, one_smul,
      fTransform_single]
  · rw [lookupCalls.memorylessReplyLaw_eval_resumed]
    simp only [RandomSystem.parallelLaw, ProbDist.single, bindK_single, one_smul,
      fTransform_single]

variable {D X O}

/-- Fixed observed replies are shared with the public caller while private entries stay retained. -/
lemma reconstruct_smul_ofFunction (q r : ℕ)
    -- `κ z o` is the private entry law; `f` fixes the observed table shared by both callers.
    (κ : D → O → ProbDist X)
    (f : D → O) :
    reconstruct q r κ •
      TypedSystem.ofFunction (A := Evaluation D O (q + r)) (fun _ => f) =
    TypedSystem.sample (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2)).1
      (fun ψ => (TypedSystem.ofFunction (A := Evaluation D X q) (fun _ z => ψ (z, f z)) ∥
          TypedSystem.ofFunction (A := Evaluation D O r) (fun _ => f))) := by
  let observedQ := TypedSystem.ofFunction (A := Evaluation D O q) (fun _ => f)
  let observedR := TypedSystem.ofFunction (A := Evaluation D O r) (fun _ => f)
  let privateSystem := randomFunction (Evaluation (D × O) X (2 * q))
    (fun _ zo => κ zo.1 zo.2)
  calc
    (reconstruct q r κ •
        TypedSystem.ofFunction (A := Evaluation D O (q + r)) (fun _ => f) :
        TypedSystem ((Evaluation D X q).tensor (Evaluation D O r))) =
      ((lookup D X O q ≫ TypedConverter.rightContext _ privateSystem) ⊗ₘ
          (𝟙 (Evaluation D O r))) • (observedQ ∥ observedR) := by
      rw [reconstruct, Interface.comp_smul, Evaluation.share_smul_ofFunction]
      rfl
    _ = (lookup D X O q • (observedQ ∥ privateSystem)) ∥ observedR := by
      cc_normalize
      rw [TypedConverter.attach_rightContext]
    _ = TypedSystem.sample (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2)).1 (fun ψ =>
        (lookup D X O q • (observedQ ∥ TypedSystem.ofFunction
          (A := Evaluation (D × O) X (2 * q)) (fun _ => ψ))) ∥ observedR) := by
      rw [show privateSystem = _ from
        Evaluation.randomFunction_eq_sample (D × O) X (2 * q) (fun zo => κ zo.1 zo.2)]
      cc_normalize
    _ = _ := by
      apply congrArg (TypedSystem.sample (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2)).1)
      funext ψ
      exact congrArg (fun R => TypedSystem.parallel R observedR)
        (lookup_smul_parallel_ofFunction D X O q f ψ)

/-- Coordinate conditional laws reconstruct the joint latent/observed function resource. -/
lemma reconstruct_eq_sample (q r : ℕ)
    -- `μ z` and `ν z` are the latent and observed laws; `κ z o` reconstructs the latent reply.
    (μ : D → ProbDist X) (ν : D → ProbDist O)
    (κ : D → O → ProbDist X) (F : D → X → O)
    -- `coordinate` identifies the full joint law of observation `F z x` and latent reply `x`.
    (coordinate : ∀ z, ProbDist.jointLaw (ν z) (κ z) = (μ z).map (fun x => (F z x, x))) :
    reconstruct q r κ •
      randomFunction (Evaluation D O (q + r)) (fun _ => ν) =
    TypedSystem.sample (ProbDist.piDep μ).1
      (fun x => (TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => x) ∥
          TypedSystem.ofFunction (A := Evaluation D O r) (fun _ z => F z (x z)))) := by
  let joint := (fun pair : (D → X) × (D → O) =>
        (TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => pair.1) ∥
          TypedSystem.ofFunction (A := Evaluation D O r) (fun _ => pair.2)))
  rw [Evaluation.randomFunction_eq_sample, TypedConverter.smul_sample]
  calc
    _ = TypedSystem.sample (ProbDist.piDep ν).1 (fun f =>
        TypedSystem.sample (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2)).1
          (fun ψ => joint ((fun z => ψ (z, f z)), f))) := by
      apply congrArg (TypedSystem.sample (ProbDist.piDep ν).1)
      funext f
      exact reconstruct_smul_ofFunction q r κ f
    -- Combine the independent observed-table and private-table draws.
    _ = TypedSystem.sample
        (prodProbDist (ProbDist.piDep ν)
          (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2))).1
        (fun pair => joint ((fun z => pair.2 (z, pair.1 z)), pair.1)) :=
      (TypedSystem.sample_prod (ProbDist.piDep ν).1
        (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2)).1
        (fun pair : (D → O) × (D × O → X) =>
          joint ((fun z => pair.2 (z, pair.1 z)), pair.1))).symm
    _ = TypedSystem.sample
        ((prodProbDist (ProbDist.piDep ν)
          (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2))).map
          (fun pair => ((fun z => pair.2 (z, pair.1 z)), pair.1))).1 joint :=
      (TypedSystem.sample_fTransform
        (fun pair : (D → O) × (D × O → X) =>
          ((fun z => pair.2 (z, pair.1 z)), pair.1))
        (prodProbDist (ProbDist.piDep ν)
          (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2))).1 joint).symm
    -- Replace their joint output law using the coordinate reconstruction contracts.
    _ = TypedSystem.sample ((ProbDist.piDep μ).map
        (fun x => (x, fun z => F z (x z)))).1 joint :=
      congrArg (fun law : ProbDist ((D → X) × (D → O)) =>
        TypedSystem.sample law.1 joint)
        (ProbDist.map_prod_piDep_pair_eq_of_jointLaw μ ν κ F coordinate)
    _ = _ := TypedSystem.sample_fTransform (fun x : D → X => (x, fun z => F z (x z)))
      (ProbDist.piDep μ).1 joint

/-- Fixing the latent table supplies both the table and its pointwise observations. -/
lemma observe_smul_ofFunction (q r : ℕ) (F : D → X → O) (f : D → X) :
    observe q r F • TypedSystem.ofFunction (A := Evaluation D X (q + r)) (fun _ => f) =
      (TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f) ∥
          TypedSystem.ofFunction (A := Evaluation D O r) (fun _ z => F z (f z))) := by
  have routed : observeReply r F •
      TypedSystem.ofFunction (A := Evaluation D X r) (fun _ => f) =
      TypedSystem.ofFunction (A := Evaluation D O r) (fun _ z => F z (f z)) :=
    TypedConverter.routingAt_smul_ofFunction (A := Evaluation D O r)
      (B := Evaluation D X r) id (fun u x => F u.2 x)
      (fun xs admitted => by simpa only [List.map_id] using admitted) (fun _ => f)
  calc
    (observe q r F • TypedSystem.ofFunction (A := Evaluation D X (q + r)) (fun _ => f) :
        TypedSystem ((Evaluation D X q).tensor (Evaluation D O r))) =
      ((𝟙 (Evaluation D X q)) ⊗ₘ observeReply r F) •
        (TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f) ∥
          TypedSystem.ofFunction (A := Evaluation D X r) (fun _ => f)) := by
      rw [observe, Interface.comp_smul, Evaluation.share_smul_ofFunction]
      rfl
    _ = _ := by
      cc_normalize
      exact congrArg (fun R => TypedSystem.parallel
        (TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f)) R) routed

/-- Sampling the latent resource once retains the same draw in both access arms. -/
lemma observe_eq_sample (q r : ℕ) (μ : D → ProbDist X) (F : D → X → O) :
    observe q r F • randomFunction (Evaluation D X (q + r)) (fun _ => μ) =
      TypedSystem.sample (ProbDist.piDep μ).1
        (fun f => (TypedSystem.ofFunction (A := Evaluation D X q) (fun _ => f) ∥
          TypedSystem.ofFunction (A := Evaluation D O r) (fun _ z => F z (f z)))) := by
  rw [Evaluation.randomFunction_eq_sample, TypedConverter.smul_sample]
  apply congrArg (TypedSystem.sample (ProbDist.piDep μ).1)
  funext f
  exact observe_smul_ofFunction q r F f

/-- Conditional reconstruction preserves both accessible arms jointly.
[1, Theorem 3, p. 18]: "the two are identically distributed".
The coordinate laws permit input-dependent distributions and observations. -/
theorem reconstruct_eq_observe (q r : ℕ)
    -- `μ z` is the latent law; `ν z` is the observed law; `κ z o` reconstructs given `o`.
    (μ : D → ProbDist X) (ν : D → ProbDist O) (κ : D → O → ProbDist X)
    -- `F z` maps the latent reply to its observation at input `z`.
    (F : D → X → O)
    -- `coordinate` identifies the complete observation/latent joint law at each input.
    (coordinate : ∀ z, ProbDist.jointLaw (ν z) (κ z) = (μ z).map (fun x => (F z x, x))) :
    reconstruct q r κ •
      randomFunction (Evaluation D O (q + r)) (fun _ => ν) =
    observe q r F • randomFunction (Evaluation D X (q + r)) (fun _ => μ) :=
  (reconstruct_eq_sample q r μ ν κ F coordinate).trans (observe_eq_sample q r μ F).symm

end Commons.ConditionalRandomFunction
