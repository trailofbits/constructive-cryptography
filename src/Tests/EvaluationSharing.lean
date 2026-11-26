module

public import Commons.Definitions.EvaluationSharing

/-!
# Shared and independent evaluation draws

Two callers ask the same unit input once. A shared fair bit gives `(true,true)` mass `1/2`
and `(true,false)` mass `0`; independent fair bits give `(true,false)` mass `1/4`.
-/

@[expose] public section

namespace Commons.Tests.EvaluationSharing

open SystemAlgebra Probability Probability.Distribution

/-- One evaluation call with a unit input and Boolean reply. -/
abbrev arm := Evaluation Unit Bool 1

/-- One retained fair bit, answering every admitted call with that bit. -/
noncomputable def fair (q : ℕ) : TypedSystem (Evaluation Unit Bool q) :=
  TypedSystem.sample (uniform Bool) fun b => TypedSystem.ofFunction (fun _ _ => b)

/-- On a one-element input alphabet, the random-function draw is exactly one fair bit. -/
lemma fair_eq_randomFunction (q : ℕ) :
    fair q = randomFunction (Evaluation Unit Bool q) (fun _ _ => ProbDist.uniform Bool) := by
  classical
  have selected : (ProbDist.piDep (fun _ : Unit => ProbDist.uniform Bool)).map
      (fun f => f ()) = ProbDist.uniform Bool := by
    apply Subtype.ext
    change fTransform _ (piDep _) = _
    rw [piDep_eq_pi]
    exact congrArg Subtype.val (ProbDist.map_pi_apply (fun _ : Unit => ProbDist.uniform Bool) ())
  symm
  calc
    _ = TypedSystem.sample (ProbDist.piDep (fun _ : Unit => ProbDist.uniform Bool)).1
        (fun f => TypedSystem.ofFunction (A := Evaluation Unit Bool q) (fun _ => f)) :=
      Evaluation.randomFunction_eq_sample Unit Bool q (fun _ => ProbDist.uniform Bool)
    _ = TypedSystem.sample (ProbDist.piDep (fun _ : Unit => ProbDist.uniform Bool)).1
        (fun f => TypedSystem.ofFunction (A := Evaluation Unit Bool q) (fun _ _ => f ())) := by
      apply congrArg (TypedSystem.sample _)
      funext f
      congr 1
    _ = TypedSystem.sample
        ((ProbDist.piDep (fun _ : Unit => ProbDist.uniform Bool)).map (fun f => f ())).1
        (fun b => TypedSystem.ofFunction (A := Evaluation Unit Bool q) (fun _ _ => b)) :=
      (TypedSystem.sample_fTransform (fun f : Unit → Bool => f ())
        (ProbDist.piDep (fun _ : Unit => ProbDist.uniform Bool)).1
        (fun b => TypedSystem.ofFunction (A := Evaluation Unit Bool q) (fun _ _ => b))).symm
    _ = _ := congrArg (fun P : ProbDist Bool => TypedSystem.sample P.1
      (fun b => TypedSystem.ofFunction (A := Evaluation Unit Bool q) (fun _ _ => b))) selected

/-- Both caller ports route to the same retained bit. -/
noncomputable def shared : TypedSystem (arm.tensor arm) :=
  Evaluation.share Unit Bool 1 1 • fair 2

/-- The two arms retain separate independent fair bits. -/
noncomputable def independent : TypedSystem (arm.tensor arm) :=
  TypedSystem.parallel (fair 1) (fair 1)

/-- The left caller receives `b`, then the right caller receives `c`. -/
def replies (b c : Bool) :
    List ((Σ i, (arm.tensor arm).X i) × (Σ i, (arm.tensor arm).Y i)) :=
  [(⟨.inl .eval, ()⟩, ⟨.inl .eval, b⟩),
    (⟨.inr .eval, ()⟩, ⟨.inr .eval, c⟩)]

lemma replies_admitted (b c : Bool) : (arm.tensor arm).domain ((replies b c).map Prod.fst) := by
  norm_num [replies, Interface.parallelDomain, parallelInputs, sumAlphabet,
    SystemAlgebra.restrict, Interface.queryBudget]

lemma shared_presentation : shared = TypedSystem.sample (uniform Bool)
    (fun b => TypedSystem.ofFunction (A := arm.tensor arm)
      (fun i _ => match i with | .inl _ => b | .inr _ => b)) := by
  rw [shared, fair, TypedConverter.smul_sample]
  apply congrArg (TypedSystem.sample (uniform Bool))
  funext b
  refine (Evaluation.share_smul_ofFunction Unit Bool 1 1 (fun _ => b)).trans ?_
  rw [TypedSystem.parallel_ofFunction]
  congr 1
  funext i x
  cases i <;> rfl

/-- Sharing leaves one draw in scope across the two calls. -/
lemma shared_mass (b c : Bool) : shared.1 (replies b c) =
    (uniform Bool).mass (fun k => b = k ∧ c = k) := by
  rw [shared_presentation, TypedSystem.sample_ofFunction_mass_eq]
  apply mass_congr
  intro k
  constructor
  · intro matching
    simpa only [replies, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using matching.2
  · intro answers
    refine ⟨Or.inr (replies_admitted b c), ?_⟩
    simpa only [replies, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using answers

/-- One distinct draw is retained in each arm. -/
lemma independent_presentation : independent =
    TypedSystem.sample ((uniform Bool).prod (uniform Bool)) (fun bc =>
      TypedSystem.ofFunction (A := arm.tensor arm)
        (fun i _ => match i with | .inl _ => bc.1 | .inr _ => bc.2)) := by
  rw [independent, fair, TypedSystem.parallel_sample_left]
  rw [TypedSystem.sample_prod]
  apply congrArg (TypedSystem.sample (uniform Bool))
  funext b
  rw [TypedSystem.parallel_sample_right]
  apply congrArg (TypedSystem.sample (uniform Bool))
  funext c
  refine (TypedSystem.parallel_ofFunction (A := arm) (B := arm)
    (fun _ _ => b) (fun _ _ => c)).trans ?_
  congr 1
  funext i x
  cases i <;> rfl

lemma independent_mass : independent.1 (replies true false) = 1 / 4 := by
  rw [independent_presentation, TypedSystem.sample_ofFunction_mass_eq]
  calc
    _ = ((uniform Bool).prod (uniform Bool)).mass
        (fun bc => bc.1 = true ∧ bc.2 = false) := by
      apply mass_congr
      intro bc
      constructor
      · intro matching
        simpa only [replies, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and, eq_comm] using matching.2
      · intro answers
        refine ⟨Or.inr (replies_admitted true false), ?_⟩
        simpa only [replies, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and, eq_comm] using answers
    _ = (uniform Bool).mass (fun b => b = true) *
        (uniform Bool).mass (fun c => c = false) :=
      mass_prod_and (uniform Bool) (uniform Bool) (fun b : Bool => b = true)
        (fun c : Bool => c = false)
    _ = 1 / 4 := by
      rw [mass_singleton, mass_singleton, uniform_apply, uniform_apply]
      norm_num

/-- Shared equal replies retain probability `1/2`; independence changes the cross-arm law. -/
example : shared.1 (replies true false) = 0 ∧
    shared.1 (replies true true) = 1 / 2 ∧
    independent.1 (replies true false) = 1 / 4 := by
  rw [shared_mass, shared_mass, independent_mass, uniform_mass_eq_card_filter,
    uniform_mass_eq_card_filter]
  norm_num [Finset.filter_insert, Finset.filter_singleton]

#print axioms Evaluation.randomFunction_eq_sample
#print axioms Evaluation.share_smul_ofFunction
#print axioms fair_eq_randomFunction
#print axioms shared_mass
#print axioms independent_mass

end Commons.Tests.EvaluationSharing
