module

public import Commons.Definitions.GenericGroup.Dense
public import Commons.Definitions.AbstractModel.ExtractionGame.Laws
public import Mathlib.Data.ZMod.Basic

/-!
# Dense generic-group model checks

The instance on `ZMod 5` uses addition and `1`, retains one permutation across observations,
and permits a terminal guess with zero ordinary calls. That fixed guess wins with mass `1/5`.
-/

@[expose] public noncomputable section

namespace Tests.GenericGroupDense

open Commons.GenericGroup Commons.AbstractModel SystemAlgebra
open Probability Probability.Distribution

/-- Register values and observation labels are residues modulo five. -/
abbrev model := denseModel (ZMod 5)

example (π : Equiv.Perm (ZMod 5)) (values : Fin 2 → ZMod 5) :
    model.operate π .add values = values 0 + values 1 := rfl

example (π : Equiv.Perm (ZMod 5)) (values : Fin 0 → ZMod 5) :
    model.operate π .one values = 1 := rfl

/-- Two observations of `x` both use the retained permutation `π`. -/
def repeatedObservation (π : Equiv.Perm (ZMod 5)) (x : ZMod 5) :
    List ((Σ i, (model.observationInterface (ZMod 5) 2).X i) ×
      (Σ i, (model.observationInterface (ZMod 5) 2).Y i)) :=
  [(⟨(), fun _ => x⟩, ⟨(), π x⟩), (⟨(), fun _ => x⟩, ⟨(), π x⟩)]

lemma same_permutation_replies (π : Equiv.Perm (ZMod 5)) (x : ZMod 5) :
    (model.observations 2 π).1 (repeatedObservation π x) = 1 := by
  apply TypedSystem.ofFunction_mass_eq_one
  · right
    exact ⟨List.cons_ne_nil _ _, le_rfl⟩
  · intro z hz
    simp only [repeatedObservation, List.mem_cons, List.not_mem_nil, or_false,
      or_self] at hz
    subst z
    rfl

/-- The same `(π,x)` sample owns both register interpretation and all observations. -/
example : (denseGame (ZMod 5) (ι := Bool) false 2).visible =
    TypedSystem.sample (denseLaw (ZMod 5)).1 (fun z =>
      model.registersConverter false 2 (model.operate z.1) z.2 • model.observations 2 z.1) :=
  model.extractionGame_visible false 2 (denseLaw (ZMod 5))

/-- Observe the initial register, without changing its contents. -/
def observe : model.Command Bool := ⟨.query (), fun _ => false⟩

/-- The ordinary observation uses the one-call allowance; submission uses no ordinary call. -/
lemma observation_then_submission : model.Admitted false 1 [observe, ⟨.submit, (0 : ZMod 5)⟩] := by
  apply (admitted_snoc_iff false 1 [observe] ⟨.submit, (0 : ZMod 5)⟩).mpr
  refine ⟨Or.inr ?_, ?_, ?_, ?_⟩
  · apply (admitted_snoc_iff false 1 [] observe).mpr
    simp [observe, ordinary, reads, initialized]
  · change (1 : ℕ) ≤ 1
    exact le_rfl
  · simp [observe, ordinary]
  · simp only [reads, Finset.empty_subset]

/-- An observation cannot use a zero ordinary-call allowance. -/
example : ¬ model.Admitted false 0 [observe] := by
  intro admitted
  have count := admitted.2.1
  change (1 : ℕ) ≤ 0 at count
  omega

/-- A fixed terminal guess succeeds on one of the five uniformly sampled original secrets. -/
lemma zero_query_score (guess : ZMod 5) :
    (denseGame (ZMod 5) (ι := Bool) false 0).1.1.winProbability
      (envProbe (DDE.ofQueries [⟨.submit, guess⟩]) (fun _ => False))
      (envProbe_isDDD (DDE.ofQueries_queryBounded
        (X := model.Command Bool) (Y := Σ i, model.Output i) [⟨.submit, guess⟩])) =
        1 / (Fintype.card (ZMod 5) : ℝ) := by
  classical
  refine (model.extractionGame_winProbability_submit false 0
    (denseLaw (ZMod 5)) guess (fun _ => False)).trans ?_
  rw [denseLaw, prodProbDist_val,
    mass_prod_snd _ _ (fun x : ZMod 5 => x = guess)]
  simp only [ProbDist.uniform, weight_uniform, one_mul, mass_singleton, uniform_apply]

example : (1 : ℝ) / Fintype.card (ZMod 5) = 1 / 5 := by
  norm_num

#print axioms Commons.GenericGroup.denseModel
#print axioms Commons.GenericGroup.denseLaw
#print axioms Commons.GenericGroup.denseGame
#print axioms same_permutation_replies
#print axioms observation_then_submission
#print axioms zero_query_score

end Tests.GenericGroupDense
