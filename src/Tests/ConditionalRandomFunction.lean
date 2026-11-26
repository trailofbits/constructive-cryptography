module

public import Commons.Definitions.ConditionalRandomFunction.Laws
public import RandomSystems.Typed.Filter
public import Tests.Conditioning
public import Tests.EvaluationSharing

/-!
# Conditional reconstruction with shared observations

A biased first bit and an independent fair second bit form the latent reply. Observing only
its first bit merges two outcomes. The unobserved `none` branch has an explicit fallback.
The same outer filter restricts both joint-access assemblies.
-/

@[expose] public section

namespace Commons.Tests.ConditionalRandomFunction

open SystemAlgebra Probability Probability.Distribution
open Commons.ConditionalRandomFunction
open scoped SystemAlgebra

/-- The first bit is true with probability `1/6`; the second bit is independent and fair. -/
noncomputable def latent : ProbDist (Bool × Bool) :=
  prodProbDist (ConditioningTests.biased.map (fun n => n == 2)) (ProbDist.uniform Bool)

/-- Observe the first bit; the second bit remains latent and `none` is unreachable. -/
def observation (x : Bool × Bool) : Option Bool := some x.1

/-- Reconstruct the reply conditioned on its first bit; `none` uses `(true,false)`. -/
noncomputable def conditional (o : Option Bool) : ProbDist (Bool × Bool) :=
  latent.conditionOn (fun x => observation x = o) (ProbDist.single (true, false))

/-- The concrete kernel preserves the joint observation/reply law. -/
lemma coordinate : ProbDist.jointLaw (latent.map observation) conditional =
    latent.map (fun x => (observation x, x)) :=
  ProbDist.jointLaw_conditionOn_eq_map latent observation _

/-- Two distinct latent replies have the same observation. -/
example : observation (false, false) = observation (false, true) := rfl

/-- The empty fiber keeps the selected fallback. -/
example : conditional none = ProbDist.single (true, false) := by
  apply ProbDist.conditionOn_of_mass_eq_zero
  apply mass_eq_zero_of_forall_not
  intro x
  simp only [observation, reduceCtorEq, not_false_eq_true]

/-- The two resources permit arbitrary interleaving within their same caller allowances. -/
theorem reconstruction (q r : ℕ) :
    reconstruct (D := Bool) q r (fun _ => conditional) •
      randomFunction (Evaluation Bool (Option Bool) (q + r))
        (fun _ _ => latent.map observation) =
    observe q r (fun _ => observation) •
      randomFunction (Evaluation Bool (Bool × Bool) (q + r)) (fun _ _ => latent) :=
  reconstruct_eq_observe q r (fun _ => latent) (fun _ => latent.map observation)
    (fun _ => conditional) (fun _ => observation) (fun _ => coordinate)

/-- Two latent queries and one observation query share the input `false`. -/
abbrev access := (Evaluation Bool (Bool × Bool) 2).tensor (Evaluation Bool (Option Bool) 1)

/-- Query latent, observed, then latent again, always at the same input. -/
def interleaved (first last : Bool × Bool) (seen : Option Bool) :
    List ((Σ i, access.X i) × (Σ i, access.Y i)) :=
  [(⟨.inl .eval, false⟩, ⟨.inl .eval, first⟩),
    (⟨.inr .eval, false⟩, ⟨.inr .eval, seen⟩),
    (⟨.inl .eval, false⟩, ⟨.inl .eval, last⟩)]

lemma interleaved_admitted (first last : Bool × Bool) (seen : Option Bool) :
    access.domain ((interleaved first last seen).map Prod.fst) := by
  norm_num [interleaved, Interface.parallelDomain, parallelInputs, sumAlphabet,
    SystemAlgebra.restrict, Interface.queryBudget]

/-- One latent table supplies both access arms throughout all three calls. -/
noncomputable def direct : TypedSystem access :=
  observe 2 1 (fun _ => observation) •
    randomFunction (Evaluation Bool (Bool × Bool) 3) (fun _ _ => latent)

/-- The transcript depends on one retained coordinate, including its repeated latent reply. -/
lemma interleaved_mass (first last : Bool × Bool) (seen : Option Bool) :
    direct.1 (interleaved first last seen) =
      latent.1.mass (fun x => x = first ∧ observation x = seen ∧ x = last) := by
  have presented := observe_eq_sample 2 1 (fun _ : Bool => latent) (fun _ => observation)
  change direct = _ at presented
  simp only [Interface.cc_parallel_eq, TypedSystem.parallel_ofFunction] at presented
  have evaluated := congrArg (fun R : TypedSystem access => R.1 (interleaved first last seen))
    presented
  rw [evaluated, TypedSystem.sample_ofFunction_mass_eq]
  have selected : (ProbDist.piDep (fun _ : Bool => latent)).map (fun f => f false) = latent := by
    rw [show ProbDist.piDep (fun _ : Bool => latent) = ProbDist.pi (fun _ => latent) from
      Subtype.ext (piDep_eq_pi _)]
    exact ProbDist.map_pi_apply (fun _ : Bool => latent) false
  calc
    _ = (ProbDist.piDep (fun _ : Bool => latent)).1.mass
        (fun f => f false = first ∧ observation (f false) = seen ∧ f false = last) := by
      apply mass_congr
      intro f
      constructor
      · intro matching
        have replies := matching.2
        simp only [interleaved, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
          at replies
        exact ⟨replies.1.symm, replies.2.1.symm, replies.2.2.symm⟩
      · intro replies
        refine ⟨Or.inr (interleaved_admitted first last seen), ?_⟩
        simp only [interleaved, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
        exact ⟨replies.1.symm, replies.2.1.symm, replies.2.2.symm⟩
    _ = ((ProbDist.piDep (fun _ : Bool => latent)).map (fun f => f false)).1.mass
        (fun x => x = first ∧ observation x = seen ∧ x = last) :=
      (mass_fTransform (fun f : Bool → Bool × Bool => f false)
        (ProbDist.piDep (fun _ : Bool => latent)).1
        (fun x => x = first ∧ observation x = seen ∧ x = last)).symm
    _ = _ := congrArg (fun law : ProbDist (Bool × Bool) => law.1.mass
      (fun x => x = first ∧ observation x = seen ∧ x = last)) selected

/-- Repeating an input cannot change its latent reply, even across an observed query. -/
example : direct.1 (interleaved (false, false) (false, true) (some false)) = 0 := by
  rw [interleaved_mass]
  apply mass_eq_zero_of_forall_not
  rintro x ⟨first, _, last⟩
  have impossible := first.symm.trans last
  cases impossible

/-- The consistent interleaving has positive mass `5/12`; the two latent replies use one draw. -/
example : direct.1 (interleaved (false, false) (false, false) (some false)) = 5 / 12 := by
  rw [interleaved_mass]
  have event : (fun x : Bool × Bool =>
      x = (false, false) ∧ observation x = some false ∧ x = (false, false)) =
      (fun x => x = (false, false)) := by
    funext x
    apply propext
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩
  rw [event, mass_singleton]
  norm_num [latent, prodProbDist_val, prod_apply, ProbDist.map_val,
    ConditioningTests.biased, fTransform_add, fTransform_single, ProbDist.uniform, uniform_apply]

/-- The reconstructed assembly has the same cumulative mass on this admitted interleaving. -/
example (first last : Bool × Bool) (seen : Option Bool) :
    ((reconstruct 2 1 (fun _ => conditional) •
      randomFunction (Evaluation Bool (Option Bool) 3)
        (fun _ _ => latent.map observation)) : TypedSystem access).1
      (interleaved first last seen) =
      latent.1.mass (fun x => x = first ∧ observation x = seen ∧ x = last) := by
  exact (congrArg (fun R : TypedSystem access => R.1 (interleaved first last seen))
    (reconstruction 2 1)).trans (interleaved_mass first last seen)

/-- Splitting shared access into independent draws changes a concrete cross-arm mass. -/
example : EvaluationSharing.shared.1 (EvaluationSharing.replies true false) = 0 ∧
    EvaluationSharing.independent.1 (EvaluationSharing.replies true false) = 1 / 4 := by
  rw [EvaluationSharing.shared_mass, EvaluationSharing.independent_mass,
    uniform_mass_eq_card_filter]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

/-- Both sides retain the same outside input restriction. -/
example (q r : ℕ)
    (admit : List (Σ i, ((Evaluation Bool (Bool × Bool) q).tensor
      (Evaluation Bool (Option Bool) r)).X i) → Prop)
    (closed : ∀ xs ys, xs <+: ys → admit ys → admit xs) :
    TypedConverter.filter _ admit closed •
      (reconstruct q r (fun _ => conditional) •
        randomFunction (Evaluation Bool (Option Bool) (q + r))
          (fun _ _ => latent.map observation)) =
    TypedConverter.filter _ admit closed •
      (observe q r (fun _ => observation) •
        randomFunction (Evaluation Bool (Bool × Bool) (q + r)) (fun _ _ => latent)) :=
  congrArg (TypedConverter.attach (TypedConverter.filter _ admit closed)) (reconstruction q r)

#print axioms Commons.ConditionalRandomFunction.lookup
#print axioms Commons.ConditionalRandomFunction.reconstruct_eq_observe
#print axioms reconstruction
#print axioms interleaved_mass

end Commons.Tests.ConditionalRandomFunction
