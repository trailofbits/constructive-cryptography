/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Counting
import RandomSystems.Filter
import RandomSystems.Technique.HCoefficient
import RandomSystems.Uniform

set_option autoImplicit false

/-!
# The sum of two independent uniform permutations

## Model

Patarin, *A Proof of Security in O(2^n) for the Xor of Two Random
Permutations* (extended ICITS 2008 version), printed p. 1, records the earlier
result that “the Xor of k independent PRP gives a PRF with security at least in
O(2^{k/(k+1)n})”; `k = 2` is the cubic regime formalized below.  His Theorem 2
(printed p. 4) gives the coefficient-H step by counting permutation pairs that
realize each transcript.

For a finite additive commutative group `G`, `sumUrp G` samples a pair
`(π, σ)` uniformly from `Equiv.Perm G × Equiv.Perm G` and exposes the function
`x ↦ π x + σ x` through `System.functionEvaluator`.  Uniformity on the product
is the repository's finite-law expression of independence.  This generalizes
Patarin's XOR interface: the counting uses only additive cancellation and
commutativity.  Both real and ideal systems are restricted with
`PDS.filterQueries q`, so `PDS.advantage` ranges over the ordinary compatible,
stopping fixed-interface environments while exposing at most `q` queries.

Jost's interface discipline requires a fixed query/response interface here but
neither supplies nor requires an operation on it.  The additive commutative
group is therefore an explicit, scheme-specific specialization, and no
converter or Constructive Cryptography structure is used.
-/

noncomputable section

open scoped NNReal BigOperators

namespace RandomSystems

open Probability
open Classical

universe u

namespace PDS

variable (G : Type u) [Fintype G] [DecidableEq G] [AddCommGroup G]

/-! ## Representatives -/

/-- The pointwise sum of two independently sampled uniform permutations. -/
def sumUrp : PDS G G :=
  Distribution.fTransform
    (fun pair : Equiv.Perm G × Equiv.Perm G =>
      System.functionEvaluator (fun x => pair.1 x + pair.2 x))
    (Distribution.uniform (Equiv.Perm G × Equiv.Perm G))

/-! ## TranscriptExtension -/

private def goodAssignments {r : ℕ} (outputs : Fin r → G) :
    Finset (Fin r → G) :=
  Finset.univ.filter fun first =>
    Function.Injective first ∧
      Function.Injective (fun i => outputs i - first i)


omit [Fintype G] in
private theorem mem_image_sub_iff_mem_range_sub {n : ℕ}
    (values : Fin n → G) (target value : G) :
    value ∈ (Finset.univ : Finset (Fin n)).image (fun i => target - values i) ↔
      target - value ∈ Set.range values := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
  constructor
  · rintro ⟨i, equal⟩
    exact ⟨i, ((sub_eq_iff_comm).mp equal).symm⟩
  · rintro ⟨i, equal⟩
    exact ⟨i, sub_eq_iff_comm.mp equal.symm⟩

private theorem prod_sub_two_mul_le_card_goodAssignments
    (r : ℕ) (outputs : Fin r → G) :
    ∏ k ∈ Finset.range r, (Fintype.card G - 2 * k) ≤
      (goodAssignments G outputs).card := by
  induction r with
  | zero =>
      simp only [Finset.prod_range_zero]
      apply Finset.one_le_card.mpr
      refine ⟨Fin.elim0, ?_⟩
      rw [goodAssignments, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      let smallerOutputs : Fin n → G := Fin.init outputs
      -- Forget the last coordinate of every admissible assignment.
      have mapsTo : ∀ assignment ∈ goodAssignments G outputs,
          Fin.init assignment ∈ goodAssignments G smallerOutputs := by
        intro assignment hAssignment
        rw [goodAssignments, Finset.mem_filter] at hAssignment
        rw [goodAssignments, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · exact hAssignment.2.1.comp (Fin.castSucc_injective n)
        · exact hAssignment.2.2.comp (Fin.castSucc_injective n)
      have fiberBound : ∀ initial ∈ goodAssignments G smallerOutputs,
          Fintype.card G - 2 * n ≤
            ((goodAssignments G outputs).filter fun assignment =>
              Fin.init assignment = initial).card := by
        intro initial hInitial
        rw [goodAssignments, Finset.mem_filter] at hInitial
        -- At step `n`, avoid the `n` used first-permutation values and the
        -- at most `n` values that would repeat a second-permutation value.
        let forbidden : Finset G :=
          Finset.univ.image initial ∪
            Finset.univ.image (fun i : Fin n =>
              outputs (Fin.last n) - (smallerOutputs i - initial i))
        let allowed : Finset G := Finset.univ \ forbidden
        have forbiddenCard : forbidden.card ≤ 2 * n := by
          calc
            forbidden.card ≤
                (Finset.univ.image initial).card +
                  (Finset.univ.image (fun i : Fin n =>
                    outputs (Fin.last n) - (smallerOutputs i - initial i))).card :=
              Finset.card_union_le _ _
            _ ≤ n + n := Nat.add_le_add
              (by simpa using (Finset.card_image_le
                (s := (Finset.univ : Finset (Fin n))) (f := initial)))
              (by simpa using (Finset.card_image_le
                (s := (Finset.univ : Finset (Fin n)))
                (f := fun i : Fin n =>
                  outputs (Fin.last n) - (smallerOutputs i - initial i))))
            _ = 2 * n := (two_mul n).symm
        have allowedCard : Fintype.card G - 2 * n ≤ allowed.card := by
          have forbiddenSubset : forbidden ⊆ (Finset.univ : Finset G) :=
            fun x _ => Finset.mem_univ x
          dsimp [allowed]
          rw [Finset.card_sdiff_of_subset forbiddenSubset, Finset.card_univ]
          exact Nat.sub_le_sub_left forbiddenCard (Fintype.card G)
        have allowedMaps : ∀ value ∈ allowed,
            Fin.snoc initial value ∈
              (goodAssignments G outputs).filter fun assignment =>
                Fin.init assignment = initial := by
          intro value hValue
          have valueNotForbidden := (Finset.mem_sdiff.mp hValue).2
          have valueFresh : ¬ value ∈ Set.range initial := by
            rintro ⟨i, rfl⟩
            apply valueNotForbidden
            exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
          have secondFresh :
              ¬ outputs (Fin.last n) - value ∈
                Set.range (fun i : Fin n => smallerOutputs i - initial i) := by
            intro collision
            apply valueNotForbidden
            apply Finset.mem_union_right
            exact (mem_image_sub_iff_mem_range_sub G
              (fun i : Fin n => smallerOutputs i - initial i)
              (outputs (Fin.last n)) value).2 collision
          have secondSnoc :
              (fun i : Fin (n + 1) => outputs i - (Fin.snoc initial value : Fin (n + 1) → G) i) =
                (Fin.snoc (fun i : Fin n => smallerOutputs i - initial i)
                  (outputs (Fin.last n) - value) : Fin (n + 1) → G) := by
            funext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp
            · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
              rfl
          rw [Finset.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [goodAssignments, Finset.mem_filter]
            refine ⟨Finset.mem_univ _,
              (Fin.snoc_injective_iff.mpr ⟨hInitial.2.1, valueFresh⟩), ?_⟩
            rw [secondSnoc]
            exact Fin.snoc_injective_iff.mpr ⟨hInitial.2.2, secondFresh⟩
          · exact Fin.snoc_comp_castSucc
        have allowedInjective : Set.InjOn
            (fun value => (Fin.snoc initial value : Fin (n + 1) → G))
            (↑allowed : Set G) := by
          intro x _ y _ equal
          have := congrFun equal (Fin.last n)
          simpa using this
        -- Appending an allowed value injects into this prefix fiber.
        have allowedLeFiber : allowed.card ≤
            ((goodAssignments G outputs).filter fun assignment =>
              Fin.init assignment = initial).card :=
          Finset.card_le_card_of_injOn
            (fun value => (Fin.snoc initial value : Fin (n + 1) → G))
            allowedMaps allowedInjective
        exact le_trans allowedCard allowedLeFiber
      -- Multiply the uniform branch lower bound through the induction.
      calc
        ∏ k ∈ Finset.range (n + 1), (Fintype.card G - 2 * k) =
            (Fintype.card G - 2 * n) *
              ∏ k ∈ Finset.range n, (Fintype.card G - 2 * k) := by
                rw [Finset.prod_range_succ]
                ac_rfl
        _ ≤ (Fintype.card G - 2 * n) *
              (goodAssignments G smallerOutputs).card :=
          Nat.mul_le_mul_left _ (ih smallerOutputs)
        _ ≤ (goodAssignments G outputs).card :=
          Finset.mul_card_image_le_card_of_maps_to mapsTo _ fiberBound


private theorem card_perm_pair_sum_fiber_lower_bound
    {r : ℕ} (inputs : Fin r → G) (inputsInjective : Function.Injective inputs)
    (outputs : Fin r → G) :
    (Fintype.card G - r).factorial ^ 2 *
        (∏ k ∈ Finset.range r, (Fintype.card G - 2 * k)) ≤
      ((Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
        (fun pair => ∀ i, pair.1 (inputs i) + pair.2 (inputs i) = outputs i)).card := by
  let admissible := goodAssignments G outputs
  let event :=
    (Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
      (fun pair => ∀ i, pair.2 (inputs i) = outputs i - pair.1 (inputs i))
  let firstValues : Equiv.Perm G × Equiv.Perm G → Fin r → G :=
    fun pair i => pair.1 (inputs i)
  have queryBound : r ≤ Fintype.card G := by
    simpa using Fintype.card_le_of_injective inputs inputsInjective
  have mapsTo : ∀ pair ∈ event, firstValues pair ∈ admissible := by
    intro pair hPair
    dsimp [event] at hPair
    rw [Finset.mem_filter] at hPair
    dsimp [admissible]
    rw [goodAssignments, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, pair.1.injective.comp inputsInjective, ?_⟩
    have secondValues :
        (fun i => outputs i - firstValues pair i) =
          (fun i => pair.2 (inputs i)) := by
      funext i
      exact (hPair.2 i).symm
    rw [secondValues]
    exact pair.2.injective.comp inputsInjective
  -- Partition satisfying permutation pairs by the first permutation's
  -- output tuple on the queried inputs.
  have partition :
      event.card = ∑ assignment ∈ admissible,
        (event.filter fun pair => firstValues pair = assignment).card :=
    Finset.card_eq_sum_card_fiberwise mapsTo
  -- Each admissible tuple extends to `(N-r)!` choices for each permutation.
  have fiberCard : ∀ assignment ∈ admissible,
      (event.filter fun pair => firstValues pair = assignment).card =
        (Fintype.card G - r).factorial ^ 2 := by
    intro assignment hAssignment
    dsimp [admissible] at hAssignment
    rw [goodAssignments, Finset.mem_filter] at hAssignment
    have fiberSet :
        event.filter (fun pair => firstValues pair = assignment) =
          (Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
            (fun pair =>
              (∀ i, pair.1 (inputs i) = assignment i) ∧
                ∀ i, pair.2 (inputs i) = outputs i - assignment i) := by
      ext pair
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hEvent, hFirst⟩
        dsimp [event] at hEvent
        rw [Finset.mem_filter] at hEvent
        refine ⟨fun i => congrFun hFirst i, fun i => ?_⟩
        rw [← congrFun hFirst i]
        exact hEvent.2 i
      · rintro ⟨hFirst, hSecond⟩
        refine ⟨?_, funext hFirst⟩
        dsimp [event]
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun i => ?_⟩
        rw [hSecond i, hFirst i]
    rw [fiberSet]
    calc
      ((Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
          (fun pair =>
            (∀ i, pair.1 (inputs i) = assignment i) ∧
              ∀ i, pair.2 (inputs i) = outputs i - assignment i)).card =
          ((Finset.univ : Finset (Equiv.Perm G)).filter
            (fun first => ∀ i, first (inputs i) = assignment i)).card *
          ((Finset.univ : Finset (Equiv.Perm G)).filter
            (fun second => ∀ i, second (inputs i) = outputs i - assignment i)).card :=
        Counting.card_filter_prod
          (fun first : Equiv.Perm G => ∀ i, first (inputs i) = assignment i)
          (fun second : Equiv.Perm G =>
            ∀ i, second (inputs i) = outputs i - assignment i)
      _ = (Fintype.card G - r).factorial *
          (Fintype.card G - r).factorial := by
        rw [Counting.card_perm_fiber inputs inputsInjective assignment
          hAssignment.2.1 queryBound,
          Counting.card_perm_fiber inputs inputsInjective
            (fun i => outputs i - assignment i) hAssignment.2.2 queryBound]
      _ = (Fintype.card G - r).factorial ^ 2 := by ring
  have assignmentBound := prod_sub_two_mul_le_card_goodAssignments G r outputs
  -- Sum the equal fibers over the greedily counted admissible tuples.
  have eventBound :
      (Fintype.card G - r).factorial ^ 2 *
          (∏ k ∈ Finset.range r, (Fintype.card G - 2 * k)) ≤ event.card := by
    rw [partition]
    calc
      (Fintype.card G - r).factorial ^ 2 *
          (∏ k ∈ Finset.range r, (Fintype.card G - 2 * k)) ≤
          (Fintype.card G - r).factorial ^ 2 * admissible.card :=
        Nat.mul_le_mul_left _ assignmentBound
      _ = ∑ assignment ∈ admissible,
          (Fintype.card G - r).factorial ^ 2 := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            exact Nat.mul_comm _ _
      _ = ∑ assignment ∈ admissible,
          (event.filter fun pair => firstValues pair = assignment).card :=
        Finset.sum_congr rfl fun assignment member => (fiberCard assignment member).symm
  have eventEqual :
      event = (Finset.univ : Finset (Equiv.Perm G × Equiv.Perm G)).filter
        (fun pair => ∀ i, pair.1 (inputs i) + pair.2 (inputs i) = outputs i) := by
    dsimp [event]
    apply Finset.filter_congr
    intro pair _
    constructor
    · intro equal i
      exact add_eq_of_eq_sub' (equal i)
    · intro equal i
      exact ((sub_eq_iff_eq_add').2 (equal i).symm).symm
  rw [← eventEqual]
  exact eventBound


omit [Fintype G] [DecidableEq G] [AddCommGroup G] in
private theorem transcriptSystemFactor_filterQueries_evaluators
    {A : Type*} (law : Distribution A) (toFunction : A → G → G)
    (q : ℕ) (transcript : System.Transcript G G) :
    transcriptSystemFactor
        (filterQueries q
          (Distribution.fTransform
            (fun sample => System.functionEvaluator (toFunction sample)) law))
        transcript =
      if transcript = [] then law.weight
      else if transcript.length ≤ q then
        law.mass (fun sample => ∀ entry ∈ transcript,
          toFunction sample entry.1 = entry.2)
      else 0 := by
  -- Pull both system pushforwards back to an event on the sampled object.
  unfold transcriptSystemFactor filterQueries filterDom
  rw [Distribution.mass_fTransform, Distribution.mass_fTransform]
  by_cases empty : transcript = []
  · subst transcript
    simp [System.SystemConsistent, Distribution.mass_true]
  · rw [if_neg empty]
    by_cases admitted : transcript.length ≤ q
    · rw [if_pos admitted]
      apply Distribution.mass_congr
      intro sample
      rw [System.systemConsistent_filterDom_iff
        (fun history : List G => history.length ≤ q)
        (prefixClosed_length_le q)
        (System.functionEvaluator (toFunction sample)) transcript empty]
      rw [System.systemConsistent_functionEvaluator_iff]
      simp only [List.length_map, admitted, and_true]
    · rw [if_neg admitted]
      apply Distribution.mass_eq_zero_of_forall_not
      intro sample consistent
      apply admitted
      simpa only [List.length_map] using
        ((System.systemConsistent_filterDom_iff
          (fun history : List G => history.length ≤ q)
          (prefixClosed_length_le q)
          (System.functionEvaluator (toFunction sample)) transcript empty).mp consistent).2

/-! ## BadEvent -/


/-! ## GoodRatio -/

private theorem filterQueries_sumUrp_urf_ratio
    (q : ℕ) (hsize : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (transcript : System.Transcript G G) :
    (1 - (((q : NNReal) ^ 3 / (Fintype.card G : NNReal) ^ 2 : NNReal) : ℝ)) *
        transcriptSystemFactor (filterQueries q (urf G G)) transcript ≤
      transcriptSystemFactor (filterQueries q (sumUrp G)) transcript := by
  rw [urf, sumUrp,
    transcriptSystemFactor_filterQueries_evaluators G
      (Distribution.uniform (G → G)) (fun function => function) q transcript,
    transcriptSystemFactor_filterQueries_evaluators G
      (Distribution.uniform (Equiv.Perm G × Equiv.Perm G))
      (fun pair x => pair.1 x + pair.2 x) q transcript]
  by_cases empty : transcript = []
  · simp only [if_pos empty, Distribution.weight_uniform]
    have epsNonnegative :
        0 ≤ ((((q : NNReal) ^ 3 /
          (Fintype.card G : NNReal) ^ 2 : NNReal) : ℝ)) := by positivity
    linarith
  · rw [if_neg empty, if_neg empty]
    by_cases admitted : transcript.length ≤ q
    · rw [if_pos admitted, if_pos admitted]
      -- Collapse repeated queries to the finite set of distinct inputs.
      let querySet : Finset G := (transcript.map Prod.fst).toFinset
      let enumeration : Fin querySet.card ≃ querySet :=
        (finCongr (Fintype.card_coe querySet).symm).trans
          (Fintype.equivFin querySet).symm
      let inputs : Fin querySet.card → G := fun i => (enumeration i).1
      have inputsInjective : Function.Injective inputs := by
        intro i j equal
        exact enumeration.injective (Subtype.ext equal)
      -- An inconsistent transcript has zero ideal mass; otherwise a reference
      -- function supplies one output for each distinct query.
      by_cases consistent : ∃ function : G → G,
          ∀ entry ∈ transcript, function entry.1 = entry.2
      · obtain ⟨reference, referenceConsistent⟩ := consistent
        let outputs : Fin querySet.card → G := fun i => reference (inputs i)
        have constraints (function : G → G) :
            (∀ entry ∈ transcript, function entry.1 = entry.2) ↔
              (fun i => function (inputs i)) = outputs := by
          have onQuerySet :
              (∀ entry ∈ transcript, function entry.1 = entry.2) ↔
                ∀ x : querySet, function x.1 = reference x.1 := by
            constructor
            · intro functionConsistent x
              have memberMap : x.1 ∈ transcript.map Prod.fst :=
                List.mem_toFinset.mp x.2
              obtain ⟨entry, entryMember, entryQuery⟩ := List.mem_map.mp memberMap
              have queryEqual : entry.1 = x.1 := by simpa using entryQuery
              rw [← queryEqual, functionConsistent entry entryMember,
                referenceConsistent entry entryMember]
            · intro equalOnSet entry entryMember
              have memberSet : entry.1 ∈ querySet := by
                dsimp [querySet]
                rw [List.mem_toFinset]
                exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩
              exact (equalOnSet ⟨entry.1, memberSet⟩).trans
                (referenceConsistent entry entryMember)
          rw [onQuerySet]
          constructor
          · intro equalOnSet
            funext i
            exact equalOnSet (enumeration i)
          · intro equalTuple x
            let i := enumeration.symm x
            have atIndex := congrFun equalTuple i
            simpa [inputs, outputs, i] using atIndex
        have distinctBound : querySet.card ≤ q :=
          le_trans (by
            simpa [querySet] using List.toFinset_card_le (transcript.map Prod.fst))
            (by simpa using admitted)
        have distinctCube : querySet.card ^ 3 ≤ (Fintype.card G) ^ 2 :=
          le_trans (Nat.pow_le_pow_left distinctBound 3) hsize
        have cardPositive : 0 < Fintype.card G := Fintype.card_pos
        -- Count compatible permutation pairs, then apply the normalized
        -- sum-of-permutations ratio bound.
        have pairCount := card_perm_pair_sum_fiber_lower_bound G inputs
          inputsInjective outputs
        have ratioCount := Counting.sop_ratio_counting_bound cardPositive distinctCube
        have defectLeOne :
            (querySet.card : NNReal) ^ 3 /
                (Fintype.card G : NNReal) ^ 2 ≤ 1 := by
          rw [div_le_one₀ (by positivity :
            (0 : NNReal) < (Fintype.card G : NNReal) ^ 2)]
          exact_mod_cast distinctCube
        have ratioReal :
            (1 - (querySet.card : ℝ) ^ 3 /
                (Fintype.card G : ℝ) ^ 2) *
                (1 / (Fintype.card G : ℝ) ^ querySet.card) ≤
              (((((Fintype.card G - querySet.card).factorial) ^ 2 *
                  ∏ k ∈ Finset.range querySet.card,
                    (Fintype.card G - 2 * k)) : ℕ) : ℝ) /
                ((Fintype.card G).factorial : ℝ) ^ 2 := by
          have castRatio :
              (((1 - (querySet.card : NNReal) ^ 3 /
                    (Fintype.card G : NNReal) ^ 2) *
                  (1 / (Fintype.card G : NNReal) ^ querySet.card) : NNReal) : ℝ) ≤
                (((((((Fintype.card G - querySet.card).factorial) ^ 2 *
                    ∏ k ∈ Finset.range querySet.card,
                      (Fintype.card G - 2 * k)) : ℕ) : NNReal) /
                  ((Fintype.card G).factorial : NNReal) ^ 2 : NNReal) : ℝ) := by
            exact_mod_cast ratioCount
          simpa only [NNReal.coe_mul, NNReal.coe_sub defectLeOne,
            NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast,
            NNReal.coe_one, Nat.cast_pow, Nat.cast_mul] using castRatio
        have pairCountReal :
            (((((Fintype.card G - querySet.card).factorial) ^ 2 *
                ∏ k ∈ Finset.range querySet.card,
                  (Fintype.card G - 2 * k)) : ℕ) : ℝ) ≤
              (((Finset.univ :
                Finset (Equiv.Perm G × Equiv.Perm G)).filter
                  (fun pair => ∀ i,
                    pair.1 (inputs i) + pair.2 (inputs i) = outputs i)).card : ℝ) := by
          exact_mod_cast pairCount
        have denominatorNonnegative :
            0 ≤ ((Fintype.card G).factorial : ℝ) ^ 2 := by positivity
        have ratioToFiber :
            (1 - (querySet.card : ℝ) ^ 3 /
                (Fintype.card G : ℝ) ^ 2) *
                (1 / (Fintype.card G : ℝ) ^ querySet.card) ≤
              (((Finset.univ :
                Finset (Equiv.Perm G × Equiv.Perm G)).filter
                  (fun pair => ∀ i,
                    pair.1 (inputs i) + pair.2 (inputs i) = outputs i)).card : ℝ) /
                ((Fintype.card G).factorial : ℝ) ^ 2 :=
          le_trans ratioReal
            (div_le_div_of_nonneg_right pairCountReal denominatorNonnegative)
        have defectMono :
            (querySet.card : ℝ) ^ 3 / (Fintype.card G : ℝ) ^ 2 ≤
              (q : ℝ) ^ 3 / (Fintype.card G : ℝ) ^ 2 := by
          have castBound : (querySet.card : ℝ) ≤ q := by exact_mod_cast distinctBound
          gcongr
        -- The ideal factor is the uniform-function fiber mass.
        have idealMass :
            (Distribution.uniform (G → G)).mass
                (fun function => ∀ entry ∈ transcript,
                  function entry.1 = entry.2) =
              (1 / (Fintype.card G : ℝ)) ^ querySet.card := by
          rw [Distribution.mass_congr _ constraints]
          simpa only [Fintype.card_fin] using
            Counting.uniform_mass_eval_eq inputs inputsInjective outputs
        -- The real factor is the normalized compatible-pair count.
        have pairConstraints (pair : Equiv.Perm G × Equiv.Perm G) :
            (∀ entry ∈ transcript,
                pair.1 entry.1 + pair.2 entry.1 = entry.2) ↔
              ∀ i, pair.1 (inputs i) + pair.2 (inputs i) = outputs i := by
          constructor
          · intro consistentPair i
            exact congrFun
              ((constraints (fun x => pair.1 x + pair.2 x)).mp consistentPair) i
          · intro equalTuple
            exact (constraints (fun x => pair.1 x + pair.2 x)).mpr
              (funext equalTuple)
        have realMass :
            (Distribution.uniform (Equiv.Perm G × Equiv.Perm G)).mass
                (fun pair => ∀ entry ∈ transcript,
                  pair.1 entry.1 + pair.2 entry.1 = entry.2) =
              (((Finset.univ :
                Finset (Equiv.Perm G × Equiv.Perm G)).filter
                  (fun pair => ∀ i,
                    pair.1 (inputs i) + pair.2 (inputs i) = outputs i)).card : ℝ) /
                ((Fintype.card G).factorial : ℝ) ^ 2 := by
          rw [Distribution.mass_congr _ pairConstraints,
            Distribution.uniform_mass_eq_card_filter,
            Fintype.card_prod, Fintype.card_perm]
          push_cast
          ring
        rw [idealMass, realMass]
        calc
          (1 - ((((q : NNReal) ^ 3 /
                (Fintype.card G : NNReal) ^ 2 : NNReal) : ℝ))) *
              (1 / (Fintype.card G : ℝ)) ^ querySet.card ≤
              (1 - (querySet.card : ℝ) ^ 3 /
                (Fintype.card G : ℝ) ^ 2) *
                (1 / (Fintype.card G : ℝ)) ^ querySet.card := by
            have coefficient :
                ((((q : NNReal) ^ 3 /
                  (Fintype.card G : NNReal) ^ 2 : NNReal) : ℝ)) =
                  (q : ℝ) ^ 3 / (Fintype.card G : ℝ) ^ 2 := by norm_num
            rw [coefficient]
            exact mul_le_mul_of_nonneg_right (sub_le_sub_left defectMono 1)
              (by positivity)
          _ = (1 - (querySet.card : ℝ) ^ 3 /
                (Fintype.card G : ℝ) ^ 2) *
                (1 / (Fintype.card G : ℝ) ^ querySet.card) := by
            rw [one_div_pow]
          _ ≤ _ := ratioToFiber
      · have idealZero :
            (Distribution.uniform (G → G)).mass
              (fun function => ∀ entry ∈ transcript,
                function entry.1 = entry.2) = 0 :=
          Distribution.mass_eq_zero_of_forall_not _
            (fun function functionConsistent =>
              consistent ⟨function, functionConsistent⟩)
        rw [idealZero, mul_zero]
        exact (Distribution.uniform_nonNeg.mass_nonneg _)
    · simp only [if_neg admitted, mul_zero, le_refl]

/-! ## BadMass

The one-cell specialization bounds its sole ideal cell by normalization, so
there is no additional bad-event mass term.
-/

/-! ## MainLemma

The private theorem `filterQueries_sumUrp_urf_ratio` is the system-factor ratio
required by the H-coefficient endpoint; `BadMass` contributes no extra term.
-/

/-! ## ConstructionOrReduction -/

/-- The sum of two independent uniform permutations on `G`, restricted to at
most `q` queries, is indistinguishable from a uniform random function with
advantage at most `q³ / |G|²`, provided `q³ ≤ |G|²`.

The proof uses the H-coefficient ratio theorem: after removing repeated
queries, the number of compatible permutation pairs gives the required lower
bound on every transcript-system factor. -/
theorem advantage_filterQueries_sumUrp_urf_le
    (q : ℕ) (hsize : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    advantage (filterQueries q (sumUrp G)) (filterQueries q (urf G G)) ≤
      (q : ℝ) ^ 3 / (Fintype.card G : ℝ) ^ 2 := by
  let eps : NNReal :=
    (q : NNReal) ^ 3 / (Fintype.card G : NNReal) ^ 2
  -- Both filtered systems remain normalized probability laws.
  have realProbability : (filterQueries q (sumUrp G)).isProbDist := by
    unfold filterQueries
    apply isProbDist_filterDom
    unfold sumUrp
    exact Distribution.fTransform_isProbDist _ Distribution.uniform_isProbDist
  have idealProbability : (filterQueries q (urf G G)).isProbDist := by
    unfold filterQueries
    apply isProbDist_filterDom
    exact isProbDist_urf G G
  -- Apply the transcript-factor ratio endpoint of the H-coefficient method.
  have bound := advantage_le_of_ratio
    (filterQueries q (sumUrp G)) (filterQueries q (urf G G)) eps
    realProbability.1 idealProbability.1
    (Distribution.weight_eq_weight_of_isProbDist realProbability idealProbability)
    idealProbability.2
    (filterQueries_sumUrp_urf_ratio G q hsize)
  simpa only [eps, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast] using bound

end PDS

end RandomSystems
