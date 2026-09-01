/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems

/-!
# Selected standalone Random Systems surface

This module imports only the standalone `RandomSystems` root and checks its
uniform-object surface. An ordinary XOR permutation is exposed as a DDS, the
uniform permutation law forms a normalized common-domain presentation, and
the generic event, distance, parallel, and finite-partition surfaces remain
available without importing converters or Constructive Cryptography.
-/

namespace RandomSystems.Tests.SelectedSurface

open RandomSystems
open Probability
open scoped CryptoNotation ENNReal NNReal BigOperators
  RandomSystems.ConditionalEquivalence

/-- XOR by a fixed bit, viewed as a permutation. -/
def xorPermutation (key : Bool) : Equiv.Perm Bool where
  toFun input := Bool.xor input key
  invFun output := Bool.xor output key
  left_inv input := by cases input <;> cases key <;> rfl
  right_inv output := by cases output <;> cases key <;> rfl

/-- The corresponding stateless deterministic discrete system. -/
noncomputable def xorDDS (key : Bool) : System.DDS Bool Bool :=
  System.functionEvaluator (xorPermutation key)

/-- A function evaluator answers from the latest query in its history. -/
example (key input : Bool)
    (admitted : [input] ∈ System.dom (xorDDS key)) :
    System.output (xorDDS key) [input] admitted =
      Bool.xor input key := by
  unfold xorDDS
  rfl

/-- The named uniform-permutation PDS is a probability law on one common
domain. -/
noncomputable def uniformPermutationPresentation :
    CommonDomain.ProbabilityPresentation Bool Bool where
  law := ⟨PDS.urp Bool, PDS.isProbDist_urp Bool⟩
  fixedDomain := ⟨{history : List Bool | history ≠ []}, PDS.hasDomain_urp Bool⟩

/-- Quotienting the normalized presentation requires no construction layer. -/
noncomputable def uniformPermutationSystem :
    CommonDomain.ProbabilityRandomSystem Bool Bool :=
  CommonDomain.ProbabilityRandomSystem.ofPresentation
    uniformPermutationPresentation

/-- Generic event notation is available from the standalone root. -/
example :
    0 ≤ Pr[permutation true = permutation true |
      permutation ←$ Distribution.uniform (Equiv.Perm Bool)] :=
  Distribution.uniform_nonNeg.mass_nonneg _

/-- The pair-specific distance vanishes on the uniform-permutation PDS. -/
example : PDS.advantage (PDS.urp Bool) (PDS.urp Bool) = 0 :=
  PDS.advantage_self _

/-- Independent ordered parallel stays within the normalized common-domain
surface. -/
noncomputable def twoUniformPermutations :
    CommonDomain.ProbabilityPresentation (Bool ⊕ Bool) (Bool ⊕ Bool) :=
  CommonDomain.ProbabilityPresentation.parallel
    uniformPermutationPresentation uniformPermutationPresentation

example : CommonDomain.ProbabilityPresentation.Equivalent
    twoUniformPermutations twoUniformPermutations :=
  CommonDomain.ProbabilityPresentation.equivalent_refl _

/-- The H-coefficient API supports an arbitrary finite partition of an
otherwise unrestricted finite-support carrier. -/
example {A ι : Type*} [Fintype ι] [DecidableEq ι]
    (real ideal : Distribution A) (cell : A → ι) (eps : ι → NNReal)
    (realNonnegative : real.NonNeg) (idealNonnegative : ideal.NonNeg)
    (sameWeight : real.weight = ideal.weight)
    (ratio : ∀ sample,
      (1 - eps (cell sample)) * ideal sample ≤ real sample) :
    statDist real ideal ≤
      ∑ i, (eps i : ℝ) * ideal.mass (fun sample => cell sample = i) :=
  hTechnique_partition_finiteSupport real ideal cell eps realNonnegative
    idealNonnegative sameWeight ratio

/-! ## Deterministic proof automation -/

example {A X Y : Type*} (source : Distribution A)
    (function : A → X → Y) (condition : A → System.MC X)
    (probability : source.isProbDist) :
    (PDG.ofFunction source function condition).isProbDist := by
  rs_routine

example {A X Y : Type*} (source : Distribution A)
    (function : A → X → Y) (condition : A → System.MC X) :
    PDG.HasDomain (PDG.ofFunction source function condition)
      {queries : List X | queries ≠ []} := by
  rs_routine

example {A X Y : Type*} (source : Distribution A)
    (function : A → X → Y) (condition : A → System.MC X) :
    (PDG.ofFunction source function condition).underlying =
      Distribution.fTransform
        (fun value => System.functionEvaluator (function value)) source := by
  rs_normalize

example {X Y : Type*} (predicate : List X → Prop)
    (prefixClosed : PrefixClosed predicate) (game : PDG X Y) :
    (PDG.filterDom predicate prefixClosed game).underlying =
      PDS.filterDom predicate prefixClosed game.underlying := by
  rs_normalize

example {X Y : Type*} (predicate : List X → Prop)
    (prefixClosed : PrefixClosed predicate) (game : PDG X Y)
    (probability : game.isProbDist) :
    (PDG.filterDom predicate prefixClosed game).underlying.isProbDist := by
  rs_routine

example {X Y : Type*} (predicate : List X → Prop)
    (prefixClosed : PrefixClosed predicate) (game : PDG X Y)
    (domain : Set (List X)) (hasDomain : PDG.HasDomain game domain) :
    PDS.HasDomain (PDG.filterDom predicate prefixClosed game).underlying
      {history | history ∈ domain ∧ predicate history} := by
  rs_routine

example {X Y : Type*} (game : PDG X Y) (target : PDS X Y)
    (domain : Set (List X)) (epsilon : ℝ)
    (gameProbability : game.isProbDist)
    (targetProbability : target.isProbDist)
    (gameDomain : PDG.HasDomain game domain)
    (targetDomain : PDS.HasDomain target domain)
    (equivalent :
      RandomSystems.ConditionalEquivalence.ConditionallyEquivalent game target)
    (winning : PDG.supWinProb (PDG.blind game) ≤ epsilon) :
    PDS.advantage game.underlying target ≤ epsilon := by
  rs_conditional_equivalence domain using equivalent, winning

example {X Y : Type*} (game : PDG X Y) (target : PDS X Y)
    (domain : Set (List X))
    (gameProbability : game.isProbDist)
    (targetProbability : target.isProbDist)
    (gameDomain : PDG.HasDomain game domain)
    (targetDomain : PDS.HasDomain target domain)
    (equivalent : game |≡ target) :
    game ≡ᵍ PDG.enhance_with_MBO target game :=
  ConditionalEquivalence.equivalentAsGames_enhance_with_MBO_of_conditionallyEquivalent
    game target domain gameProbability targetProbability
    gameDomain targetDomain equivalent

/-- error: rs_routine could not close the goal -/
#guard_msgs (substring := true) in
example {X Y : Type*} (game : PDG X Y) : game.isProbDist := by
  rs_routine

/-- error: rs_routine could not close the goal -/
#guard_msgs (substring := true) in
example {X Y : Type*} (system : PDS X Y) (domain : Set (List X)) :
    PDS.HasDomain system domain := by
  rs_routine

/-- error: rs_routine could not close the goal -/
#guard_msgs (substring := true) in
example {X Y : Type*} (game : PDG X Y) (target : PDS X Y)
    (epsilon : ℝ) :
    PDS.advantage game.underlying target ≤ epsilon := by
  rs_routine

/-- error: rs_routine could not close the goal -/
#guard_msgs (substring := true) in
example {X Y : Type*} (game : PDG X Y) (target : PDS X Y)
    (domain : Set (List X)) (epsilon : ℝ)
    (gameProbability : game.isProbDist)
    (targetProbability : target.isProbDist)
    (equivalent :
      RandomSystems.ConditionalEquivalence.ConditionallyEquivalent game target)
    (winning : PDG.supWinProb (PDG.blind game) ≤ epsilon) :
    PDS.advantage game.underlying target ≤ epsilon := by
  rs_conditional_equivalence domain using equivalent, winning

/-- trace: [Meta.Tactic.simp.rewrite] PDG.underlying_filterDom -/
#guard_msgs (substring := true) in
example {X Y : Type*} (predicate : List X → Prop)
    (prefixClosed : PrefixClosed predicate) (game : PDG X Y) :
    (PDG.filterDom predicate prefixClosed game).underlying =
      PDS.filterDom predicate prefixClosed game.underlying := by
  rs_normalize?

end RandomSystems.Tests.SelectedSurface
