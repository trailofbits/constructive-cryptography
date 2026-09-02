import RandomSystems.Technique.ConditionalEquivalence.Advantage
import RandomSystems.Technique.ConditionalEquivalence.FunctionEvaluator
import RandomSystems.Uniform

/-!
# XOR of two uniform random functions

This module models two independent uniform random functions as the product law
`Distribution.prod (Distribution.uniform (X → Y)) (Distribution.uniform (X → Y))`.
The output type is a finite additive commutative group, and pointwise addition models XOR;
thus the result applies directly to bit-vector outputs with their usual XOR group.  This is an
optional specialization of Jost's abstract output alphabet rather than extra structure imposed on
Random Systems: the group law is needed only by this construction.  The construction samples
`(f, g)` independently and answers `x` with `f x + g x`.

The proof uses the repository's one-sided conditional-equivalence route: the construction is the
underlying system of an initially-false function game, that game is conditionally equivalent to a
single URF, and the corresponding blind game has winning probability zero.
-/

open Probability

namespace RandomSystems

universe u v

namespace PDS

/-- The random system obtained by sampling two independent uniform functions and adding their
answers pointwise.  Additive notation is the carrier-generic model of XOR. -/
noncomputable def xorUniformFunctions (X : Type u) (Y : Type v)
    [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y] : PDS X Y :=
  Distribution.fTransform
    (fun pair : (X → Y) × (X → Y) =>
      System.functionEvaluator (fun x => pair.1 x + pair.2 x))
    (Distribution.prod (Distribution.uniform (X → Y))
      (Distribution.uniform (X → Y)))

/-- The XOR of two independent uniform random functions has zero distinguishing advantage from a
single uniform random function.  The proof is by one-sided blind conditional equivalence. -/
theorem advantage_xorUniformFunctions_urf_le_zero
    (X : Type u) (Y : Type v)
    [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y] :
    PDS.advantage (xorUniformFunctions X Y) (PDS.urf X Y) ≤ 0 := by
  -- Independent sampling is the product of the two uniform function laws.
  let source : Distribution ((X → Y) × (X → Y)) :=
    Distribution.prod (Distribution.uniform (X → Y))
      (Distribution.uniform (X → Y))
  let output : ((X → Y) × (X → Y)) → X → Y :=
    fun pair x => pair.1 x + pair.2 x
  let never : System.MC X := ⟨fun _ => false, by simp⟩
  let condition : ((X → Y) × (X → Y)) → System.MC X := fun _ => never
  let game : PDG X Y := PDG.ofFunction source output condition
  -- Keeping the first function and adding it into the second is a permutation of pairs.
  let addEquiv : ((X → Y) × (X → Y)) ≃ ((X → Y) × (X → Y)) :=
    { toFun := fun pair => (pair.1, pair.1 + pair.2)
      invFun := fun pair => (pair.1, -pair.1 + pair.2)
      left_inv := by intro pair; rcases pair with ⟨f, g⟩; simp
      right_inv := by intro pair; rcases pair with ⟨f, g⟩; simp }
  -- The independent product is a probability distribution.
  have sourceProbability : source.isProbDist := by
    exact Distribution.prod_isProbDist _ _
      Distribution.uniform_isProbDist Distribution.uniform_isProbDist
  -- Permuting a uniform pair and projecting its second coordinate leaves a uniform function.
  have outputUniform : Distribution.fTransform output source =
      Distribution.uniform (X → Y) := by
    calc
      Distribution.fTransform output source =
          Distribution.fTransform output
            (Distribution.uniform ((X → Y) × (X → Y))) := by
              rw [show source = Distribution.uniform ((X → Y) × (X → Y)) by
                simp [source, Distribution.prod_uniform]]
      _ = Distribution.fTransform
            (Prod.snd ∘ (addEquiv : ((X → Y) × (X → Y)) →
              ((X → Y) × (X → Y))))
            (Distribution.uniform ((X → Y) × (X → Y))) := by rfl
      _ = Distribution.fTransform Prod.snd
            (Distribution.fTransform addEquiv
              (Distribution.uniform ((X → Y) × (X → Y)))) := by
              rw [Distribution.fTransform_comp]
      _ = Distribution.fTransform Prod.snd
            (Distribution.uniform ((X → Y) × (X → Y))) := by
              rw [Distribution.fTransform_equiv_uniform]
      _ = Distribution.uniform (X → Y) := by
              exact Distribution.fTransform_snd_uniform
                (A' := X → Y) (B' := X → Y)
  -- With an always-false condition, equality of function-event masses gives one-sided CE.
  have equivalent : ConditionalEquivalence.ConditionallyEquivalent game (PDS.urf X Y) := by
    dsimp only [game]
    apply ConditionalEquivalence.ofFunction_of_mass_eq source
      (Distribution.uniform (X → Y)) output (fun f => f) condition
    · intro value supported
      simp [condition, never]
    · exact Distribution.uniform_isProbDist
    · intro queries answers
      have conditionMass :
          source.mass (fun value => (condition value).1 queries = false) = 1 := by
        calc
          _ = source.mass (fun _ => True) :=
            Distribution.mass_congr source (by
              intro value
              simp [condition, never])
          _ = source.weight := Distribution.mass_true source
          _ = 1 := sourceProbability.weight_eq
      rw [conditionMass, mul_one, ← outputUniform, Distribution.mass_fTransform]
      apply Distribution.mass_congr
      intro value
      simp [condition, never]
  -- Blindness hides all replies; the always-false condition makes every win impossible.
  have blindBound : PDG.supWinProb (PDG.blind game) ≤ 0 := by
    apply PDG.supWinProb_le le_rfl
    intro winner
    unfold PDG.winProb PDG.blind game PDG.ofFunction
    rw [Distribution.mass_fTransform, Distribution.mass_fTransform]
    apply le_of_eq
    apply Distribution.mass_eq_zero_of_forall_not
    intro value
    simp [System.Wins, System.gameTr, System.DDG.blind,
      System.DDG.ofFunction, condition, never]
  -- The one-sided CE endpoint turns the blind winning bound into distinguishing advantage.
  have bound :=
    PDS.advantage_le_of_conditionallyEquivalent_of_supWinProb_blind_le
      game (PDS.urf X Y) {queries : List X | queries ≠ []}
      (PDG.isProbDist_ofFunction source output condition sourceProbability)
      (PDS.isProbDist_urf X Y)
      (PDG.hasDomain_ofFunction source output condition)
      (PDS.hasDomain_urf X Y) equivalent 0 blindBound
  -- Forgetting the game condition recovers the public XOR construction.
  have underlying : game.underlying = xorUniformFunctions X Y := by
    simpa [game, source, output, condition, xorUniformFunctions] using
      (PDG.underlying_ofFunction source output condition)
  simpa only [underlying] using bound

end PDS

end RandomSystems
