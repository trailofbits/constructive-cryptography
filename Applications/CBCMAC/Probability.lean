/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Applications.CBCMAC.Attachment
import RandomSystems.Converter.CommonDomain.Embedding
import RandomSystems.Filter
import RandomSystems.RandomObjects
import RandomSystems.Technique.HCoefficient

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# CBC probability bound

Maurer 2002, Theorem 6 proof (printed p. 17), conditions on the event that
“all inputs to F are distinct”. Printed p. 18 bounds the resulting collision
probability by `n² 2^{-(l+1)}`.

The fixed-interface proof uses Lanzenberger's transcript factorization from
the proof of Lemma 2.18, Appendix A.1 (printed p. 88), and then crosses the
common-domain embedding once. The application-specific `θ_r` restriction
follows the registered CR18 fallback; no total-completion game model enters
the probability argument.
-/

namespace Applications.CBCMAC

noncomputable section

open Classical
open Probability
open RandomSystems
open RandomSystems.System
open RandomSystems.Ambient
open scoped ENNReal

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

private theorem prefixClosed_totalBlocks_le
    (blockForm : M → List X) (limit : Nat) :
    RandomSystems.PrefixClosed
      (fun messages : List M =>
        CBCCombinatorics.totalBlocks blockForm messages ≤ limit) :=
  -- Total block count is monotone under list-prefix extension.
  fun _ _ isPrefix admitted =>
    (CBCCombinatorics.totalBlocks_mono blockForm isPrefix).trans admitted

private def filterDDS (blockForm : M → List X) (limit : Nat) :
    System.DDS M X → System.DDS M X :=
  System.filterDom
    (fun messages =>
      CBCCombinatorics.totalBlocks blockForm messages ≤ limit)
    (prefixClosed_totalBlocks_le blockForm limit)

private theorem query_history_prefix
    (transcript : System.Transcript M X) (k : Nat)
    (hk : k < transcript.length) :
    List.IsPrefix
      ((transcript.take k).map Prod.fst ++ [transcript[k].1])
      (transcript.map Prod.fst) := by
  -- Append the current entry to the preceding transcript prefix.
  have takeEqual : transcript.take k ++ [transcript[k]] =
      transcript.take (k + 1) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk]
    simp only [Option.toList_some]
  have isPrefix : List.IsPrefix (transcript.take k ++ [transcript[k]])
      transcript := takeEqual ▸ List.take_prefix (k + 1) transcript
  -- Projecting queries preserves that prefix relation.
  have mapped := isPrefix.map (fun entry : M × X => entry.1)
  simpa only [List.map_append, List.map_singleton] using mapped

private theorem transcriptSystemFactor_filterDDS_functionEvaluator
    {A : Type u}
    (blockForm : M → List X) (limit : Nat)
    (toFunction : A → M → X) (source : Distribution A)
    (transcript : System.Transcript M X) :
    RandomSystems.PDS.transcriptSystemFactor
        (Distribution.fTransform (filterDDS blockForm limit)
          (Distribution.fTransform
            (fun value => System.functionEvaluator (toFunction value)) source))
        transcript =
      if CBCCombinatorics.totalBlocks blockForm
          (transcript.map Prod.fst) ≤ limit then
        source.mass (fun value =>
          ∀ entry ∈ transcript, toFunction value entry.1 = entry.2)
      else 0 := by
  -- Flatten the two pushforwards and expose the generic system-factor event.
  rw [Distribution.fTransform_fTransform]
  change RandomSystems.PDS.transcriptSystemFactor
      (Distribution.fTransform
        (fun value => System.filterDom
          (fun messages =>
            CBCCombinatorics.totalBlocks blockForm messages ≤ limit)
          (prefixClosed_totalBlocks_le blockForm limit)
          (System.functionEvaluator (toFunction value))) source)
      transcript = _
  rw [RandomSystems.PDS.transcriptSystemFactor_fTransform_filterDom_functionEvaluator]
  by_cases admitted : CBCCombinatorics.totalBlocks blockForm
      (transcript.map Prod.fst) ≤ limit
  -- If the full query history is admitted, prefix closure removes the domain clauses.
  · rw [if_pos admitted]
    apply Distribution.mass_congr
    intro value
    constructor
    · intro consistent entry member
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem member
      exact (consistent k hk).2
    · intro consistent k hk
      refine ⟨(CBCCombinatorics.totalBlocks_mono blockForm
        (query_history_prefix transcript k hk)).trans admitted, ?_⟩
      exact consistent transcript[k] (List.getElem_mem hk)
  -- Otherwise the last transcript entry contradicts the domain restriction.
  · rw [if_neg admitted]
    apply Distribution.mass_eq_zero_of_forall_not
    intro value consistent
    have nonempty : transcript ≠ [] := by
      intro empty
      subst empty
      simp [CBCCombinatorics.totalBlocks] at admitted
    let k := transcript.length - 1
    -- The last prefix together with its current query is the full query history.
    have hk : k < transcript.length := Nat.sub_lt
      (List.length_pos_iff.mpr nonempty) (by omega)
    have fullHistory :
        (transcript.take k).map Prod.fst ++ [transcript[k].1] =
          transcript.map Prod.fst := by
      have lengthEq : k + 1 = transcript.length := by
        dsimp only [k]
        omega
      calc
        (transcript.take k).map Prod.fst ++ [transcript[k].1] =
            (transcript.take (k + 1)).map Prod.fst := by
          have takeEqual : transcript.take k ++ [transcript[k]] =
              transcript.take (k + 1) := by
            rw [List.take_add_one, List.getElem?_eq_getElem hk]
            simp only [Option.toList_some]
          simpa only [List.map_append, List.map_singleton] using congrArg
            (List.map (fun entry : M × X => entry.1)) takeEqual
        _ = transcript.map Prod.fst := by
          rw [lengthEq, List.take_length]
    apply admitted
    rw [← fullHistory]
    exact (consistent k hk).1

private def restrictedCBCPDS (blockForm : M → List X) (limit : Nat) :
    RandomSystems.PDS M X :=
  Distribution.fTransform (filterDDS blockForm limit)
    (Distribution.fTransform
      (fun function : X → X =>
        System.functionEvaluator fun message : M =>
          CBCCombinatorics.cbc function (blockForm message))
      (Distribution.uniform (X → X)))

private def restrictedIdealFunctionPDS
    (blockForm : M → List X) (limit : Nat) : RandomSystems.PDS M X :=
  Distribution.fTransform (filterDDS blockForm limit)
    (RandomSystems.PDS.urf M X)

private theorem restrictedCBCPDS_nonnegative
    (blockForm : M → List X) (limit : Nat) :
    (restrictedCBCPDS blockForm limit).NonNeg :=
  (Distribution.uniform_nonNeg.fTransform _).fTransform _

private theorem restrictedIdealFunctionPDS_nonnegative
    (blockForm : M → List X) (limit : Nat) :
    (restrictedIdealFunctionPDS blockForm limit).NonNeg :=
  (Distribution.uniform_nonNeg.fTransform _).fTransform _

@[simp]
private theorem restrictedCBCPDS_weight
    (blockForm : M → List X) (limit : Nat) :
    (restrictedCBCPDS blockForm limit).weight = 1 := by
  rw [restrictedCBCPDS, Distribution.weight_fTransform,
    Distribution.weight_fTransform, Distribution.weight_uniform]

@[simp]
private theorem restrictedIdealFunctionPDS_weight
    (blockForm : M → List X) (limit : Nat) :
    (restrictedIdealFunctionPDS blockForm limit).weight = 1 := by
  rw [restrictedIdealFunctionPDS, RandomSystems.PDS.urf,
    Distribution.weight_fTransform, Distribution.weight_fTransform,
    Distribution.weight_uniform]

private theorem advantage_restrictedCBCPDS_restrictedIdealFunctionPDS_le
    [Nontrivial M] (blockForm : M → List X) (limit : Nat)
    (prefixFree : CBCCombinatorics.PrefixFree blockForm) :
    RandomSystems.PDS.advantage
        (restrictedCBCPDS blockForm limit)
        (restrictedIdealFunctionPDS blockForm limit) ≤
      CBCCombinatorics.cbcEpsilon X limit := by
  let epsilonReal : ℝ :=
    (limit : ℝ) ^ 2 / (2 * (Fintype.card X : ℝ))
  have epsilonNonnegative : 0 ≤ epsilonReal := by
    dsimp only [epsilonReal]
    positivity
  let epsilon : NNReal := ⟨epsilonReal, epsilonNonnegative⟩
  -- Lanzenberger's transcript factorization reduces every adaptive DDE to this ratio.
  have advantageBound : RandomSystems.PDS.advantage
      (restrictedCBCPDS blockForm limit)
      (restrictedIdealFunctionPDS blockForm limit) ≤
      (epsilon : ENNReal) := by
    apply RandomSystems.PDS.advantage_le_of_ratio
      (restrictedCBCPDS blockForm limit)
      (restrictedIdealFunctionPDS blockForm limit) epsilon
      (restrictedCBCPDS_nonnegative blockForm limit)
      (restrictedIdealFunctionPDS_nonnegative blockForm limit)
      (by rw [restrictedCBCPDS_weight,
        restrictedIdealFunctionPDS_weight])
      (restrictedIdealFunctionPDS_weight blockForm limit)
    intro transcript
    rw [restrictedCBCPDS, restrictedIdealFunctionPDS,
      RandomSystems.PDS.urf,
      transcriptSystemFactor_filterDDS_functionEvaluator,
      transcriptSystemFactor_filterDDS_functionEvaluator]
    by_cases admitted : CBCCombinatorics.totalBlocks blockForm
        (transcript.map Prod.fst) ≤ limit
    -- For an admitted transcript, compare the two recorded-answer fibres.
    · simp only [admitted, if_pos]
      let messages := transcript.map Prod.fst
      by_cases realizable : ∃ answers : M → X,
          ∀ entry ∈ transcript, answers entry.1 = entry.2
      -- A consistent answer function rewrites transcript entries as message fibres.
      · obtain ⟨answers, answersMatch⟩ := realizable
        have answerEvent (function : M → X) :
            (∀ entry ∈ transcript, function entry.1 = entry.2) ↔
              ∀ query ∈ messages, function query = answers query := by
          constructor
          · intro equal query member
            obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
            exact (equal entry entryMember).trans
              (answersMatch entry entryMember).symm
          · intro equal entry entryMember
            exact (equal entry.1
              (List.mem_map.mpr ⟨entry, entryMember, rfl⟩)).trans
                (answersMatch entry entryMember)
        have realEvent :
            (Distribution.uniform (X → X)).mass (fun function =>
                ∀ entry ∈ transcript,
                  CBCCombinatorics.cbc function (blockForm entry.1) =
                    entry.2) =
              (Distribution.uniform (X → X)).mass (fun function =>
                ∀ query ∈ messages,
                  CBCCombinatorics.cbc function (blockForm query) =
                    answers query) :=
          Distribution.mass_congr _ fun function =>
            answerEvent (fun query =>
              CBCCombinatorics.cbc function (blockForm query))
        have idealEvent :
            (Distribution.uniform (M → X)).mass (fun function =>
                ∀ entry ∈ transcript, function entry.1 = entry.2) =
              (Distribution.uniform (M → X)).mass (fun function =>
                ∀ query ∈ messages, function query = answers query) :=
          Distribution.mass_congr _ answerEvent
        rw [realEvent, idealEvent]
        let realMass := (Distribution.uniform (X → X)).mass (fun function =>
          ∀ query ∈ messages,
            CBCCombinatorics.cbc function (blockForm query) = answers query)
        let idealMass := (Distribution.uniform (M → X)).mass (fun function =>
          ∀ query ∈ messages, function query = answers query)
        let badMass := (Distribution.uniform (X → X)).mass (fun function =>
          CBCCombinatorics.cbcBad function blockForm messages)
        let goodMass := (Distribution.uniform (X → X)).mass (fun function =>
          ¬ CBCCombinatorics.cbcBad function blockForm messages)
        have goodFactorization :
            (Distribution.uniform (X → X)).mass (fun function =>
                (∀ query ∈ messages,
                  CBCCombinatorics.cbc function (blockForm query) =
                    answers query) ∧
                ¬ CBCCombinatorics.cbcBad function blockForm messages) =
              idealMass * goodMass := by
          simpa only [idealMass, goodMass] using
            CBCCombinatorics.mass_cbc_outputs_and_not_cbcBad_on_list_eq
              blockForm prefixFree messages answers
        -- Forgetting the good-event conjunct can only increase real mass.
        have goodPart_le : idealMass * goodMass ≤ realMass := by
          rw [← goodFactorization]
          exact Distribution.mass_mono Distribution.uniform_nonNeg
            (fun _ member => member.1)
        -- Maurer's collision count bounds the bad mass by the public budget.
        have badMass_le : badMass ≤ epsilonReal := by
          apply (CBCCombinatorics.mass_cbcBad_le blockForm limit messages
            (by simpa only [messages] using admitted)).trans
          have denominatorPositive :
              (0 : ℝ) < 2 * Fintype.card X := by
            have cardPositive : (0 : ℝ) < Fintype.card X := by
              exact_mod_cast Fintype.card_pos
            positivity
          have limitNonnegative : (0 : ℝ) ≤ limit := by positivity
          dsimp only [epsilonReal]
          gcongr
          nlinarith
        -- Good and bad functions partition the normalized round-function law.
        have goodMass_eq : badMass + goodMass = 1 := by
          simpa only [badMass, goodMass, Distribution.weight_uniform] using
            Distribution.mass_add_compl (Distribution.uniform (X → X))
              (fun function =>
                CBCCombinatorics.cbcBad function blockForm messages)
        have idealMass_nonnegative : 0 ≤ idealMass :=
          Distribution.uniform_nonNeg.mass_nonneg _
        -- Multiply the lower bound on good mass by the ideal transcript mass.
        calc
          (1 - (epsilon : ℝ)) * idealMass ≤ goodMass * idealMass := by
            change (1 - epsilonReal) * idealMass ≤ goodMass * idealMass
            apply mul_le_mul_of_nonneg_right _ idealMass_nonnegative
            linarith
          _ = idealMass * goodMass := by ring
          _ ≤ realMass := goodPart_le
      -- If no answer function realizes the transcript, its ideal fibre is empty.
      · have idealZero :
            (Distribution.uniform (M → X)).mass (fun function =>
              ∀ entry ∈ transcript, function entry.1 = entry.2) = 0 :=
          Distribution.mass_eq_zero_of_forall_not _ fun function equal =>
            realizable ⟨function, equal⟩
        rw [idealZero, mul_zero]
        exact Distribution.uniform_nonNeg.mass_nonneg _
    -- An over-limit transcript has zero system factor on both sides.
    · simp [admitted]
  -- The nonnegative real budget embeds as the stated `ENNReal` budget.
  rw [CBCCombinatorics.cbcEpsilon]
  exact advantageBound.trans_eq (ENNReal.ofReal_eq_coe_nnreal
    epsilonNonnegative).symm

private theorem restrictedCBCPDS_isProbDist
    (blockForm : M → List X) (limit : Nat) :
    (restrictedCBCPDS blockForm limit).isProbDist := by
  constructor
  · exact restrictedCBCPDS_nonnegative blockForm limit
  · exact restrictedCBCPDS_weight blockForm limit

private theorem restrictedIdealFunctionPDS_isProbDist
    (blockForm : M → List X) (limit : Nat) :
    (restrictedIdealFunctionPDS blockForm limit).isProbDist := by
  constructor
  · exact restrictedIdealFunctionPDS_nonnegative blockForm limit
  · exact restrictedIdealFunctionPDS_weight blockForm limit

/-- The common domain of the two restricted fixed-interface PDSs. -/
private def restrictedDomain (blockForm : M → List X) (limit : Nat) :
    Set (List M) :=
  {history | history ≠ [] ∧
    CBCCombinatorics.totalBlocks blockForm history ≤ limit}

private theorem dom_filterDDS_functionEvaluator
    (blockForm : M → List X) (limit : Nat) (function : M → X) :
    System.dom
        (filterDDS blockForm limit (System.functionEvaluator function)) =
      restrictedDomain blockForm limit := by
  unfold filterDDS restrictedDomain
  ext history
  rw [System.mem_dom_filterDom, System.dom_functionEvaluator]
  rfl

private theorem restrictedCBCPDS_hasDomain
    (blockForm : M → List X) (limit : Nat) :
    RandomSystems.PDS.HasDomain
      (restrictedCBCPDS blockForm limit)
      (restrictedDomain blockForm limit) := by
  rw [restrictedCBCPDS]
  intro system supported
  obtain ⟨source, sourceSupported, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform _ _ supported
  obtain ⟨function, _, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform
      (fun function : X → X =>
        System.functionEvaluator fun message : M =>
          CBCCombinatorics.cbc function (blockForm message))
      (Distribution.uniform (X → X)) sourceSupported
  exact dom_filterDDS_functionEvaluator blockForm limit _

private theorem restrictedIdealFunctionPDS_hasDomain
    (blockForm : M → List X) (limit : Nat) :
    RandomSystems.PDS.HasDomain
      (restrictedIdealFunctionPDS blockForm limit)
      (restrictedDomain blockForm limit) := by
  rw [restrictedIdealFunctionPDS]
  intro system supported
  obtain ⟨source, sourceSupported, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform _ _ supported
  rw [RandomSystems.PDS.urf] at sourceSupported
  obtain ⟨function, _, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform
      (fun function : M → X => System.functionEvaluator function)
      (Distribution.uniform (M → X)) sourceSupported
  exact dom_filterDDS_functionEvaluator blockForm limit function

private def presentationAtDomain
    (law : Distribution.ProbDist (System.DDS M X))
    {domain : Set (List M)}
    (hasDomain : RandomSystems.PDS.HasDomain law.1 domain) :
    {presentation : CommonDomain.Presentation M X //
      presentation.domain = domain} :=
  ⟨{ law := law.1
     nonnegative := law.2.nonNeg
     domain := domain
     hasDomain := hasDomain }, rfl⟩

private theorem embed_restricted_function_of_admitted
    (blockForm : M → List X) (limit : Nat) (function : M → X)
    (history : Ambient.History (Interface.single M X))
    (admitted :
      CBCCombinatorics.totalBlocks blockForm history.queries ≤ limit) :
    CommonDomain.embedDDS
        (filterDDS blockForm limit
          (System.functionEvaluator function)) history =
      some (function history.last) := by
  -- The admitted complete history belongs to the restricted partial DDS.
  apply (CommonDomain.embedDDS_eq_some_iff _ history _).2
  have inDomain : history.queries ∈
      System.dom
        (filterDDS blockForm limit (System.functionEvaluator function)) := by
    unfold filterDDS
    rw [System.mem_dom_filterDom, System.dom_functionEvaluator]
    exact ⟨history.nonempty, admitted⟩
  refine ⟨inDomain, ?_⟩
  -- On that domain, filtering preserves the function evaluator's answer.
  change System.output
      (filterDDS blockForm limit (System.functionEvaluator function))
      history.queries inDomain = function history.last
  unfold filterDDS at inDomain ⊢
  rw [System.output_filterDom, System.output_functionEvaluator]
  rfl

private theorem applySystem_theta_embed_restricted_function
    (blockForm : M → List X) (limit : Nat) (function : M → X) :
    applySystem (theta blockForm limit)
        (CommonDomain.embedDDS
          (filterDDS blockForm limit
            (System.functionEvaluator function))) =
      applySystem (theta blockForm limit) (DDS.ofFunction function) := by
  -- Evaluate the `θ_r` restriction on both systems.
  rw [applySystem_theta, applySystem_theta]
  apply DDS.ext
  intro history
  by_cases admitted :
      CBCCombinatorics.totalBlocks blockForm history.queries ≤ limit
  -- On admitted histories, the embedding returns the function value.
  · simp only [admitted, if_pos]
    exact embed_restricted_function_of_admitted blockForm limit function
      history admitted
  · simp [admitted]

private theorem apply_theta_restricted_function_law
    {A : Type u} (blockForm : M → List X) (limit : Nat)
    (toFunction : A → M → X) (source : Distribution A) :
    Distribution.fTransform (applySystem (theta blockForm limit))
        (Distribution.fTransform CommonDomain.embedDDS
          (Distribution.fTransform
            (filterDDS blockForm limit)
            (Distribution.fTransform
              (fun value => System.functionEvaluator (toFunction value))
              source))) =
      Distribution.fTransform (applySystem (theta blockForm limit))
      (Distribution.fTransform
          (fun value => DDS.ofFunction (toFunction value)) source) := by
  -- Flatten the nested pushforwards to compare their pointwise attached DDSs.
  rw [Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  -- Theta makes the embedded restricted evaluator agree with the total evaluator.
  intro value _
  simpa only [Function.comp_apply] using
    applySystem_theta_embed_restricted_function blockForm limit
      (toFunction value)

private theorem apply_theta_embed_restrictedCBCPDS
    (blockForm : M → List X) (limit : Nat) :
    PDS.apply (theta blockForm limit)
        (CommonDomain.embedPDS
          ⟨restrictedCBCPDS blockForm limit,
            restrictedCBCPDS_isProbDist blockForm limit⟩) =
      PDS.apply (theta blockForm limit) (cbcPDS blockForm) := by
  -- Compare the normalized laws after applying the same restriction.
  apply Subtype.ext
  change Distribution.fTransform (applySystem (theta blockForm limit))
      (Distribution.fTransform CommonDomain.embedDDS
        (restrictedCBCPDS blockForm limit)) = _
  rw [restrictedCBCPDS]
  -- Theta identifies the embedded restricted evaluator with the total CBC law.
  simpa only [cbcPDS] using apply_theta_restricted_function_law blockForm limit
    (fun function : X → X => fun message : M =>
      CBCCombinatorics.cbc function (blockForm message))
    (Distribution.uniform (X → X))

private theorem apply_theta_embed_restrictedIdealFunctionPDS
    (blockForm : M → List X) (limit : Nat) :
    PDS.apply (theta blockForm limit)
        (CommonDomain.embedPDS
          ⟨restrictedIdealFunctionPDS blockForm limit,
            restrictedIdealFunctionPDS_isProbDist blockForm limit⟩) =
      PDS.apply (theta blockForm limit) (idealFunction (M := M) (X := X)) := by
  -- Compare the normalized laws after applying the same restriction.
  apply Subtype.ext
  change Distribution.fTransform (applySystem (theta blockForm limit))
      (Distribution.fTransform CommonDomain.embedDDS
        (restrictedIdealFunctionPDS blockForm limit)) = _
  rw [restrictedIdealFunctionPDS]
  rw [RandomSystems.PDS.urf]
  -- Theta identifies the embedded restricted evaluator with the total ideal law.
  simpa only [idealFunction, PDS.uniformFunction] using
    apply_theta_restricted_function_law blockForm limit
    (fun function : M → X => function) (Distribution.uniform (M → X))

private theorem advantage_embedPDS_eq_Adv_of_hasDomain
    (left right : Distribution.ProbDist (System.DDS M X))
    {domain : Set (List M)}
    (leftDomain : RandomSystems.PDS.HasDomain left.1 domain)
    (rightDomain : RandomSystems.PDS.HasDomain right.1 domain) :
    Ambient.PDS.advantage
        (CommonDomain.embedPDS left) (CommonDomain.embedPDS right) =
      CommonDomain.Presentation.Adv
        (presentationAtDomain left leftDomain)
        (presentationAtDomain right rightDomain) := by
  let leftPresentation : CommonDomain.ProbabilityPresentation M X :=
    { law := left
      fixedDomain := ⟨domain, leftDomain⟩ }
  let rightPresentation : CommonDomain.ProbabilityPresentation M X :=
    { law := right
      fixedDomain := ⟨domain, rightDomain⟩ }
  have probabilitySupportNonempty : ∀
      law : Distribution.ProbDist (System.DDS M X),
      law.1.support.Nonempty := by
    intro law
    rw [Finsupp.support_nonempty_iff]
    intro equalZero
    have weightOne := law.2.weight_eq
    rw [equalZero] at weightOne
    simp [Distribution.weight] at weightOne
  obtain ⟨leftSystem, leftSupported⟩ := probabilitySupportNonempty left
  obtain ⟨rightSystem, rightSupported⟩ := probabilitySupportNonempty right
  have leftDomain_eq : leftPresentation.domain = domain :=
    (leftPresentation.hasDomain leftSystem leftSupported).symm.trans
      (leftDomain leftSystem leftSupported)
  have rightDomain_eq : rightPresentation.domain = domain :=
    (rightPresentation.hasDomain rightSystem rightSupported).symm.trans
      (rightDomain rightSystem rightSupported)
  have commonDomain : leftPresentation.domain = rightPresentation.domain :=
    leftDomain_eq.trans rightDomain_eq.symm
  change Ambient.PDS.advantage
      (CommonDomain.embedPDS left) (CommonDomain.embedPDS right) =
    RandomSystems.PDS.advantage left.1 right.1
  simpa only [CommonDomain.Presentation.Adv] using
    CommonDomain.advantage_embedPDS_eq_Adv_of_domain_eq
      leftPresentation rightPresentation commonDomain

/-- Maurer 2002, Theorem 6 (printed p. 17), specifies `n` as “the total number
of blocks of all k messages issued by the distinguisher.” This proves its
`C(R)`-versus-ideal collision leg, where `d(n) = 0`, for the normalized
finite-message PDSs restricted by `θ_r`. -/
theorem cbcPDS_advantage_le [Nontrivial M]
    (blockForm : M → List X) (limit : Nat)
    (prefixFree : CBCCombinatorics.PrefixFree blockForm) :
    Ambient.PDS.advantage
        (PDS.apply (theta blockForm limit) (cbcPDS blockForm))
        (PDS.apply (theta blockForm limit)
          (idealFunction (M := M) (X := X))) ≤
      CBCCombinatorics.cbcEpsilon X limit := by
  -- Package the two common-domain probability laws.
  let realLaw : Distribution.ProbDist (System.DDS M X) :=
    ⟨restrictedCBCPDS blockForm limit,
      restrictedCBCPDS_isProbDist blockForm limit⟩
  let idealLaw : Distribution.ProbDist (System.DDS M X) :=
    ⟨restrictedIdealFunctionPDS blockForm limit,
      restrictedIdealFunctionPDS_isProbDist blockForm limit⟩
  have realApplication :
      PDS.apply (theta blockForm limit)
          (CommonDomain.embedPDS realLaw) =
        PDS.apply (theta blockForm limit) (cbcPDS blockForm) := by
    -- Theta identifies the embedded restricted CBC law with the public CBC law.
    simpa only [realLaw] using
      apply_theta_embed_restrictedCBCPDS blockForm limit
  have idealApplication :
      PDS.apply (theta blockForm limit)
          (CommonDomain.embedPDS idealLaw) =
        PDS.apply (theta blockForm limit)
          (idealFunction (M := M) (X := X)) := by
    -- Theta identifies the embedded restricted ideal law with the public ideal law.
    simpa only [idealLaw] using
      apply_theta_embed_restrictedIdealFunctionPDS blockForm limit
  -- Apply data processing, the common-domain bridge, and the fixed-interface bound.
  calc
    Ambient.PDS.advantage
        (PDS.apply (theta blockForm limit) (cbcPDS blockForm))
        (PDS.apply (theta blockForm limit)
          (idealFunction (M := M) (X := X))) ≤
      CommonDomain.Presentation.Adv
        (presentationAtDomain realLaw
          (restrictedCBCPDS_hasDomain blockForm limit))
        (presentationAtDomain idealLaw
          (restrictedIdealFunctionPDS_hasDomain blockForm limit)) :=
      by
        -- Attachment by theta is non-expanding on the ambient quotient.
        rw [← realApplication, ← idealApplication]
        calc
          Ambient.PDS.advantage
              (PDS.apply (theta blockForm limit)
                (CommonDomain.embedPDS realLaw))
              (PDS.apply (theta blockForm limit)
                (CommonDomain.embedPDS idealLaw)) ≤
            Ambient.PDS.advantage
              (CommonDomain.embedPDS realLaw)
              (CommonDomain.embedPDS idealLaw) :=
            Ambient.PDS.advantage_apply_le
              (theta blockForm limit)
              (CommonDomain.embedPDS realLaw)
              (CommonDomain.embedPDS idealLaw)
          _ = CommonDomain.Presentation.Adv
              (presentationAtDomain realLaw
                (restrictedCBCPDS_hasDomain blockForm limit))
              (presentationAtDomain idealLaw
                (restrictedIdealFunctionPDS_hasDomain blockForm limit)) :=
            advantage_embedPDS_eq_Adv_of_hasDomain
              realLaw idealLaw
              (restrictedCBCPDS_hasDomain blockForm limit)
              (restrictedIdealFunctionPDS_hasDomain blockForm limit)
    _ ≤ CBCCombinatorics.cbcEpsilon X limit := by
      change RandomSystems.PDS.advantage
          (restrictedCBCPDS blockForm limit)
          (restrictedIdealFunctionPDS blockForm limit) ≤
        CBCCombinatorics.cbcEpsilon X limit
      exact advantage_restrictedCBCPDS_restrictedIdealFunctionPDS_le
        blockForm limit prefixFree

/-- CR18, Theorem 6.1 (printed p. 126), assumes that “the block-former of the
CBC-converter is prefix-free.”  The normalized finite-message real and ideal
PDSs satisfy its collision bound; the probabilistic leg is Maurer 2002,
Theorem 6. -/
theorem realPDS_advantage_le [Nontrivial M]
    (blockForm : M → List X) (limit : Nat)
    (prefixFree : CBCCombinatorics.PrefixFree blockForm) :
    Ambient.PDS.advantage (realPDS blockForm limit)
        (idealPDS blockForm limit) ≤
      CBCCombinatorics.cbcEpsilon X limit := by
  -- Replace the assembled real PDS by its direct block-restricted CBC law.
  rw [realPDS_eq]
  -- Apply the theorem-driven CBC advantage bound.
  exact cbcPDS_advantage_le blockForm limit prefixFree

end

end Applications.CBCMAC
