/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Applications.CBCCombinatorics
import RandomSystems.Converter.Filter
import RandomSystems.Converter.RandomSystem

set_option autoImplicit false

/-!
# CBC-MAC random-system objects

Maurer 2002, Figure 6 (printed p. 17), defines the construction by “applying
the CBC feedback construction with a random function (or more generally a
random automaton) F, and taking the last output”.

The argument `blockForm` is the block sequence after the source's prefix-free
encoding and zero padding; this module does not implement that encoding.  The
finite type `M` is the repository's bounded-message specialization needed by
the normalized finite-support PDS carrier.  Replacing bitwise XOR by an
arbitrary additive commutative group is a repository generalization.

The CBC DDC and the application-specific restrictions are functions on
complete histories. Rejection by a partial round-function DDS is forwarded as
outer rejection; this is a repository extension of the source's total random
function case.
-/

namespace Applications.CBCMAC

noncomputable section

open Probability (Distribution)
open RandomSystems.Ambient

universe u

variable {X M : Type u}

/-- Extract all successful answers, returning `none` when any attempted inner
query was rejected. -/
def answerValues : List (Option X) → Option (List X)
  | [] => some []
  | none :: _ => none
  | some answer :: remaining =>
      (answerValues remaining).map (answer :: ·)

@[simp]
theorem answerValues_nil : answerValues ([] : List (Option X)) = some [] :=
  rfl

@[simp]
theorem answerValues_none (remaining : List (Option X)) :
    answerValues (none :: remaining) = none :=
  rfl

@[simp]
theorem answerValues_some (answer : X) (remaining : List (Option X)) :
    answerValues (some answer :: remaining) =
      (answerValues remaining).map (answer :: ·) :=
  rfl

theorem answerValues_eq_some_iff {answers : List (Option X)}
    {values : List X} :
    answerValues answers = some values ↔ answers = values.map some := by
  -- Traverse the attempted replies and distinguish rejection from success.
  induction answers generalizing values with
  | nil => simp
  | cons answer remaining inductionHypothesis =>
      cases answer with
      | none =>
          constructor
          · simp
          · intro equal
            cases values <;> cases equal
      | some answer =>
          cases values with
          | nil => simp
          | cons value values =>
              simp [answerValues, inductionHypothesis, and_comm]

theorem answerValues_map_some (values : List X) :
    answerValues (values.map some) = some values :=
  -- Every reply in the list is successful.
  answerValues_eq_some_iff.mpr rfl

theorem answerValues_eq_none_of_mem_none {answers : List (Option X)}
    (containsRejection : none ∈ answers) :
    answerValues answers = none := by
  -- Locate the rejected reply by induction on the history.
  induction answers with
  | nil => simp at containsRejection
  | cons answer remaining inductionHypothesis =>
      cases answer with
      | none => rfl
      | some answer =>
          simp only [List.mem_cons, reduceCtorEq, false_or] at containsRejection
          simp [answerValues, inductionHypothesis containsRejection]

/-- CBC's response after the displayed inner replies of the current message.
The first missing inner answer closes the round with rejection. -/
def response [AddMonoid X] (blockForm : M → List X)
    (message : M) (answers : List (Option X)) : X ⊕ Option X :=
  match answerValues answers with
  | none => Sum.inr none
  | some values =>
      if values.length < (blockForm message).length then
        Sum.inl (values.getLastD 0 +
          (blockForm message).getD values.length 0)
      else
        Sum.inr (some (values.getLastD 0))

/-- At the uniform block bound CBC must close the current outer round. -/
def closeResponse [AddMonoid X] (_ : M)
    (answers : List (Option X)) : Option X :=
  (answerValues answers).map (fun values => values.getLastD 0)

/-- Maurer 2002, Figure 6 (printed p. 17), defines `C(F)` by “applying the CBC
feedback construction with a random function” and “taking the last output”.
This is its bounded-inner-query DDC presentation. -/
def cbc [Fintype M] [AddMonoid X] (blockForm : M → List X) :
    DDC (Interface.single M X) (Interface.single X X) :=
  DDC.ofBoundedInnerQueries (CBCCombinatorics.blockBound blockForm)
    (fun message answers _ => response blockForm message answers)
    closeResponse

/-- The literal complete-history graph of the CBC converter. -/
theorem mem_cbc_iff [Fintype M] [AddMonoid X]
    (blockForm : M → List X)
    (history : DDC.History
      (Interface.single M X) (Interface.single X X))
    (result : DDC.Response history) :
    result ∈ cbc blockForm history ↔
      DDC.Raw.Admissible (cbc blockForm).toFun history ∧
        result = DDC.boundedInnerQueryResponse
          (CBCCombinatorics.blockBound blockForm)
          (fun message answers _ => response blockForm message answers)
          closeResponse history := by
  -- Unfold the bounded-inner-query constructor's complete-history graph.
  rw [cbc, DDC.mem_ofBoundedInnerQueries_iff]

/-- On every admissible received history, the CBC converter has exactly its
displayed complete-history response. -/
theorem response_mem_cbc [Fintype M] [AddMonoid X]
    (blockForm : M → List X)
    (history : DDC.History
      (Interface.single M X) (Interface.single X X))
    (message : M)
    (admissible : DDC.Raw.Admissible (cbc blockForm).toFun history)
    (latest : history.lastOuter = message) :
    response blockForm message (DDC.latestReplies history) ∈
      cbc blockForm history := by
  -- Reduce graph membership to admissibility and the displayed response.
  rw [mem_cbc_iff]
  refine ⟨admissible, ?_⟩
  rw [DDC.boundedInnerQueryResponse]
  unfold DDC.responseWithInnerQueryBound
  split_ifs with below
  -- Below the bound, the current-message response is used directly.
  · simp [latest]
  -- At the bound, successful replies already cover every encoded block.
  · simp only [latest]
    unfold response closeResponse
    cases valuesEqual : answerValues (DDC.latestReplies history) with
    | none => simp
    | some values =>
        -- Successful answer extraction preserves the reply count.
        have repliesEqual := answerValues_eq_some_iff.mp valuesEqual
        have valuesLength : values.length = (DDC.latestReplies history).length := by
          -- Successful values correspond one-for-one with the latest replies.
          rw [repliesEqual, List.length_map]
        have blockLength : (blockForm message).length ≤ values.length := by
          -- The uniform block bound is no larger than the reached inner depth.
          rw [valuesLength]
          exact (CBCCombinatorics.length_le_blockBound blockForm message).trans
            (Nat.le_of_not_gt below)
        simp [Nat.not_lt.mpr blockLength]

/-- The first CBC query is the first block, offset by the public zero chaining
value.  If the encoding is empty, CBC immediately returns `some 0`. -/
theorem initial_response_mem_cbc [Fintype M] [AddMonoid X]
    (blockForm : M → List X) (message : M) :
    (if blockForm message = [] then
        Sum.inr (some 0)
      else
        Sum.inl ((blockForm message).getD 0 0)) ∈
      cbc blockForm
        (DDC.History.singleton
          (B := Interface.single X X) message) := by
  -- Reduce the initial response to the bounded-inner-query graph.
  rw [mem_cbc_iff]
  constructor
  -- The initial outer query is admissible.
  · exact DDC.Raw.Admissible.start
      (raw := (cbc blockForm).toFun) message
  -- Evaluate the response before any inner answer exists.
  · rw [DDC.boundedInnerQueryResponse]
    simp only [DDC.latestReplies_singleton, DDC.History.lastOuter_singleton,
      DDC.responseWithInnerQueryBound]
    by_cases boundZero : CBCCombinatorics.blockBound blockForm = 0
    -- A zero uniform bound forces this particular encoding to be empty.
    · have empty : blockForm message = [] := by
        -- The message length is bounded above by zero.
        apply List.eq_nil_of_length_eq_zero
        have lengthBound := CBCCombinatorics.length_le_blockBound blockForm message
        omega
      simp [boundZero, empty, closeResponse]
    -- With positive bound, CBC either closes an empty encoding or emits its first block.
    · have below : 0 < CBCCombinatorics.blockBound blockForm :=
        Nat.pos_of_ne_zero boundZero
      simp [below, response]
      by_cases empty : blockForm message = []
      · simp [empty]
      · have positive := List.length_pos_of_ne_nil empty
        simp [empty, positive]

/-- A rejected round-function query closes the current CBC round with outer
rejection. -/
theorem rejection_response_mem_cbc [Fintype M] [AddMonoid X]
    (blockForm : M → List X)
    (history : DDC.History
      (Interface.single M X) (Interface.single X X))
    (admissible : DDC.Raw.Admissible (cbc blockForm).toFun history)
    (answers : List (Option X)) (replies : DDC.latestReplies history = answers)
    (containsRejection : none ∈ answers) :
    Sum.inr (none : Option X) ∈ cbc blockForm history := by
  -- Reduce graph membership to the bounded-inner-query response.
  rw [mem_cbc_iff]
  refine ⟨admissible, ?_⟩
  rw [DDC.boundedInnerQueryResponse]
  have noValues : answerValues answers = none :=
    answerValues_eq_none_of_mem_none containsRejection
  -- Both the below-bound and closing responses forward rejection.
  unfold DDC.responseWithInnerQueryBound
  split <;> simp [replies, response, closeResponse, noValues]

/-- CR18, Section 6.2.2 (printed p. 125), says that `θ_r` “keeps track of the
total number of such blocks resulting for all messages seen so far.”  This is
the complete-history function for that application-specific restriction. -/
def theta (blockForm : M → List X) (limit : Nat) :
    DDC (Interface.single M X) (Interface.single M X) :=
  DDC.filter
    (fun messages => CBCCombinatorics.totalBlocks blockForm messages ≤ limit)
    id (fun _ answer => answer)

/-- CR18, Example 5.2 (printed p. 122), states: “`[r]` is the special case of a
filter restricting access to `r` queries.”  This is that restriction on the
round-function interface. -/
def queryLimit (limit : Nat) :
    DDC (Interface.single X X) (Interface.single X X) :=
  DDC.filter (fun queries => queries.length ≤ limit) id
    (fun _ answer => answer)

/-- Exact complete-history equation for the block-count restriction. -/
theorem applySystem_theta
    (blockForm : M → List X) (limit : Nat)
    (system : DDS (Interface.single M X)) :
    applySystem (theta blockForm limit) system =
      fun history =>
        if CBCCombinatorics.totalBlocks blockForm history.queries ≤ limit then
          system history
        else
          none := by
  -- Prefix monotonicity discharges the generic filter hypothesis.
  rw [theta]
  have attachment := DDC.applySystem_filter_of_prefix_closed
    (fun messages : List M =>
      CBCCombinatorics.totalBlocks blockForm messages ≤ limit)
    (by
      intro priorPrefix wholeHistory isPrefix admitted
      exact (CBCCombinatorics.totalBlocks_mono blockForm isPrefix).trans
        admitted)
    id (fun (_ : M) (answer : Option X) => answer) system
  rw [attachment]
  funext history
  by_cases admitted :
      CBCCombinatorics.totalBlocks blockForm history.queries ≤ limit
  · rw [if_pos admitted, if_pos admitted, History.map_id]
  · rw [if_neg admitted, if_neg admitted]

/-- Exact complete-history equation for the inner-query restriction. -/
theorem applySystem_queryLimit (limit : Nat)
    (system : DDS (Interface.single X X)) :
    applySystem (queryLimit limit) system =
      fun history =>
        if history.queries.length ≤ limit then system history else none := by
  -- Prefix length discharges the generic filter hypothesis.
  rw [queryLimit]
  have attachment := DDC.applySystem_filter_of_prefix_closed
    (fun queries : List X => queries.length ≤ limit)
    (by
      intro priorPrefix wholeHistory isPrefix admitted
      exact isPrefix.length_le.trans admitted)
    id (fun (_ : X) (answer : Option X) => answer) system
  rw [attachment]
  funext history
  by_cases admitted : history.queries.length ≤ limit
  · rw [if_pos admitted, if_pos admitted, History.map_id]
  · rw [if_neg admitted, if_neg admitted]

/-- Maurer 2002, Definition 4 (printed p. 7), defines a URF as having “uniform
distribution over all functions from `X` to `Y`.”  Here both alphabets are
`X`. -/
def randomFunction [Fintype X] [DecidableEq X] [Nonempty X] :
    PDS (Interface.single X X) :=
  PDS.uniformFunction (Interface.single X X)

/-- Maurer 2002, Definition 4 (printed p. 7), defines a URF as having “uniform
distribution over all functions from `X` to `Y`.”  This finite message-space
URF represents the bounded ideal system. -/
def idealFunction [Fintype M] [DecidableEq M]
    [Fintype X] [DecidableEq X] [Nonempty X] :
    PDS (Interface.single M X) :=
  PDS.uniformFunction (Interface.single M X)

/-- Maurer 2002, Figure 6 (printed p. 17), defines `C(F)` by “applying the CBC
feedback construction with a random function” and “taking the last output”.
Here that random function is uniform, yielding the normalized finite-message
PDS corresponding to `C(R)` in the proof of Theorem 6. -/
def cbcPDS [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype M] [DecidableEq M] [AddMonoid X]
    (blockForm : M → List X) : PDS (Interface.single M X) :=
  ⟨Distribution.fTransform
      (fun function : X → X =>
        DDS.ofFunction (A := Interface.single M X) (fun message =>
          CBCCombinatorics.cbc function (blockForm message)))
      (Distribution.uniform (X → X)),
    Distribution.fTransform_isProbDist _
      Distribution.uniform_isProbDist⟩

/-- CR18, Example 5.2 (printed p. 122), states: “`[r]` is the special case of a
filter restricting access to `r` queries.”  This is `[r]R` for the finite
uniform round-function PDS. -/
def restrictedRandomFunction [Fintype X] [DecidableEq X] [Nonempty X]
    (limit : Nat) : PDS (Interface.single X X) :=
  PDS.apply (queryLimit limit) randomFunction

/-- CR18, Theorem 6.1 (printed p. 126), uses the real system `[r]R` with
`θ_r CBC` attached.  This is its normalized finite-message PDS
specialization. -/
def realPDS [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype M] [DecidableEq M] [AddMonoid X]
    (blockForm : M → List X) (limit : Nat) :
    PDS (Interface.single M X) :=
  PDS.apply (theta blockForm limit)
    (PDS.apply (cbc blockForm) (restrictedRandomFunction limit))

/-- CR18, Theorem 6.1 (printed p. 126), uses the ideal system `θ_r V`.  This is
its normalized finite-message PDS specialization. -/
def idealPDS [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype M] [DecidableEq M]
    (blockForm : M → List X) (limit : Nat) :
    PDS (Interface.single M X) :=
  PDS.apply (theta blockForm limit) idealFunction

end


end Applications.CBCMAC
