/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Applications.CBCMAC.Objects

set_option autoImplicit false

/-!
# CBC attachment equations

Maurer 2002, Figure 6 (printed p. 17), defines `C(F)` by applying the encoded
blocks through “the CBC feedback construction” and “taking the last output”.

The CBC converter is related to the ordinary CBC fold by an equality of
complete attempted-history functions. The generic bounded-inner-query theorem
in `RandomSystems.Converter.BoundedInnerQueries` supplies the unique compatible attachment;
the application proof below establishes the ordinary CBC recurrence.
-/

namespace Applications.CBCMAC

noncomputable section

open RandomSystems.Ambient
open Probability (Distribution)

universe u

variable {X M : Type u}

/-- Successful CBC values after the first `count` block positions. -/
private def successfulValues [AddMonoid X] (function : X → X)
    (blocks : List X) (count : Nat) : List X :=
  (List.range count).map fun position =>
    CBCCombinatorics.cbc function (blocks.take (position + 1))

/-- The corresponding complete list of successful inner replies. -/
private def successfulReplies [AddMonoid X] (function : X → X)
    (blocks : List X) (count : Nat) : List (Option X) :=
  (successfulValues function blocks count).map some

@[simp]
private theorem successfulReplies_zero [AddMonoid X]
    (function : X → X) (blocks : List X) :
    successfulReplies function blocks 0 = [] :=
  rfl

@[simp]
private theorem successfulReplies_length [AddMonoid X]
    (function : X → X) (blocks : List X) (count : Nat) :
    (successfulReplies function blocks count).length = count := by
  -- There is one successful reply for each enumerated block position.
  simp [successfulReplies, successfulValues]

@[simp]
private theorem successfulValues_length [AddMonoid X]
    (function : X → X) (blocks : List X) (count : Nat) :
    (successfulValues function blocks count).length = count := by
  -- The range enumerating positions has the requested length.
  simp [successfulValues]

private theorem successfulReplies_succ [AddMonoid X]
    (function : X → X) (blocks : List X) (count : Nat) :
    successfulReplies function blocks (count + 1) =
      successfulReplies function blocks count ++
        [some (CBCCombinatorics.cbc function
          (blocks.take (count + 1)))] := by
  -- Extending the position range appends the next CBC state.
  simp [successfulReplies, successfulValues, List.range_succ]

private theorem successfulValues_getLastD [AddMonoid X]
    (function : X → X) (blocks : List X) (count : Nat) :
    (successfulValues function blocks count).getLast?.getD 0 =
        CBCCombinatorics.cbc function (blocks.take count) := by
  -- Split the empty prefix from a positive prefix.
  cases count with
  | zero => simp [successfulValues, CBCCombinatorics.cbc]
  | succ count =>
      simp [successfulValues, List.range_succ]

private theorem cbc_take_succ [AddMonoid X]
    (function : X → X) (blocks : List X) {count : Nat}
    (below : count < blocks.length) :
    CBCCombinatorics.cbc function (blocks.take (count + 1)) =
      function (CBCCombinatorics.cbcInput function blocks count) := by
  -- Expose the next block at the end of the taken prefix.
  rw [List.take_add_one, List.getElem?_eq_getElem below]
  simp only [Option.toList_some]
  rw [CBCCombinatorics.cbc_append]
  -- The appended-block recurrence uses the same block selected at this position.
  congr 2
  rw [List.getD_eq_getElem _ _ below]

private theorem response_successfulReplies_of_lt [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (message : M)
    {count : Nat} (below : count < (blockForm message).length) :
    response blockForm message
        (successfulReplies function (blockForm message) count) =
      Sum.inl (CBCCombinatorics.cbcInput function
        (blockForm message) count) := by
  -- Successful prior replies expose precisely the next feedback input.
  simp [response, successfulReplies, answerValues_map_some,
    successfulValues_length, below, CBCCombinatorics.cbcInput,
    successfulValues_getLastD]

private theorem response_successfulReplies_length [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (message : M) :
    response blockForm message
        (successfulReplies function (blockForm message)
          (blockForm message).length) =
      Sum.inr (some (CBCCombinatorics.cbc function
        (blockForm message))) := by
  -- At the encoded length, the response closes with the final CBC state.
  simp [response, successfulReplies, answerValues_map_some,
    successfulValues_length, successfulValues_getLastD]

private theorem boundedInnerQueryResult_cbc [Fintype M] [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (message : M) :
    DDC.boundedInnerQueryResult (CBCCombinatorics.blockBound blockForm)
        (fun message answers _ => response blockForm message answers)
        closeResponse (fun input => some (function input)) message [] =
      some (CBCCombinatorics.cbc function (blockForm message)) := by
  let blocks := blockForm message
  -- Induct on the number of encoded blocks still to be processed.
  have digest : ∀ distance count : Nat,
      count + distance = blocks.length →
        DDC.boundedInnerQueryResult (CBCCombinatorics.blockBound blockForm)
            (fun message answers _ => response blockForm message answers)
            closeResponse (fun input => some (function input)) message
            (successfulReplies function blocks count) =
          some (CBCCombinatorics.cbc function blocks) := by
    -- Fix the number of blocks still to be processed.
    intro distance
    induction distance with
    | zero =>
        intro count countLength
        have countEqual : count = blocks.length := by omega
        subst count
        -- At the last block, either branch of the uniform inner-query bound closes.
        by_cases below : blocks.length <
            CBCCombinatorics.blockBound blockForm
        · rw [DDC.boundedInnerQueryResult, dif_pos (by
              simpa only [successfulReplies_length] using below)]
          rw [response_successfulReplies_length function blockForm message]
        · rw [DDC.boundedInnerQueryResult, dif_neg (by
              simpa only [successfulReplies_length] using below)]
          simp [closeResponse, successfulReplies, answerValues_map_some,
            successfulValues_getLastD, blocks]
    | succ distance inductionHypothesis =>
        intro count countLength
        have countBelow : count < blocks.length := by omega
        -- The message-specific remaining block also lies below the uniform bound.
        have belowBound : count < CBCCombinatorics.blockBound blockForm :=
          countBelow.trans_le
            (CBCCombinatorics.length_le_blockBound blockForm message)
        rw [DDC.boundedInnerQueryResult, dif_pos (by
          simpa only [successfulReplies_length] using belowBound)]
        rw [response_successfulReplies_of_lt function blockForm message
          (by simpa only [blocks] using countBelow)]
        -- The emitted query returns the next CBC state and extends the replies.
        simp only
        rw [← cbc_take_succ function blocks countBelow]
        rw [← successfulReplies_succ]
        exact inductionHypothesis (count + 1) (by omega)
  -- Start the recurrence with no processed blocks.
  simpa [blocks] using digest (blockForm message).length 0 (by simp [blocks])

private theorem innerQueriesWithinBound_cbc_length
    [Fintype M] [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (message : M) :
    (DDC.innerQueriesWithinBound
      (CBCCombinatorics.blockBound blockForm)
      (fun message answers _ => response blockForm message answers)
      (fun input => some (function input)) message []).length =
        (blockForm message).length := by
  let blocks := blockForm message
  -- Induct on the number of inner queries still to be emitted.
  have digest : ∀ distance count : Nat,
      count + distance = blocks.length →
        (DDC.innerQueriesWithinBound
          (CBCCombinatorics.blockBound blockForm)
          (fun message answers _ => response blockForm message answers)
          (fun input => some (function input)) message
          (successfulReplies function blocks count)).length = distance := by
    -- Fix the number of inner queries still to be emitted.
    intro distance
    induction distance with
    | zero =>
        intro count countLength
        have countEqual : count = blocks.length := by omega
        subst count
        -- Once all blocks are processed, either bound branch emits no further query.
        by_cases below : blocks.length <
            CBCCombinatorics.blockBound blockForm
        · rw [DDC.innerQueriesWithinBound, dif_pos (by
              simpa only [successfulReplies_length] using below)]
          rw [response_successfulReplies_length function blockForm message]
          rfl
        · rw [DDC.innerQueriesWithinBound, dif_neg (by
              simpa only [successfulReplies_length] using below)]
          rfl
    | succ distance inductionHypothesis =>
        intro count countLength
        have countBelow : count < blocks.length := by omega
        -- The next message block lies below the uniform inner-query bound.
        have belowBound : count < CBCCombinatorics.blockBound blockForm :=
          countBelow.trans_le
            (CBCCombinatorics.length_le_blockBound blockForm message)
        rw [DDC.innerQueriesWithinBound, dif_pos (by
          simpa only [successfulReplies_length] using belowBound)]
        rw [response_successfulReplies_of_lt function blockForm message
          (by simpa only [blocks] using countBelow)]
        rw [List.length_cons]
        rw [← cbc_take_succ function blocks countBelow]
        rw [← successfulReplies_succ]
        -- The tail emits exactly the remaining number of queries.
        have remaining := inductionHypothesis (count + 1) (by omega)
        omega
  simpa [blocks] using digest (blockForm message).length 0 (by simp [blocks])

private theorem innerQueriesWithinBoundContinuation_cbc_length
    [Fintype M] [AddMonoid X]
    (function : X → X) (blockForm : M → List X)
    (message : M) (remaining : List M) :
    (DDC.innerQueriesWithinBoundContinuation
      (CBCCombinatorics.blockBound blockForm)
      (fun message answers _ => response blockForm message answers)
      (fun input => some (function input)) message [] remaining).length =
        CBCCombinatorics.totalBlocks blockForm (message :: remaining) := by
  -- Concatenate the per-message query lists and add their lengths.
  induction remaining generalizing message with
  | nil =>
      rw [DDC.innerQueriesWithinBoundContinuation,
        innerQueriesWithinBound_cbc_length]
      rfl
  | cons next remaining inductionHypothesis =>
      rw [DDC.innerQueriesWithinBoundContinuation, List.length_append,
        innerQueriesWithinBound_cbc_length,
        inductionHypothesis next]
      rfl

/-- Maurer 2002, Figure 6 (printed p. 17), defines `C(F)` by “applying the CBC
feedback construction with a random function” and “taking the last output”.
Against a stateless round function, the complete-history attachment function
is exactly that CBC function on the final requested message. -/
theorem applySystem_cbc_ofFunction [Fintype M] [AddMonoid X]
    (function : X → X) (blockForm : M → List X) :
    applySystem (cbc blockForm) (DDS.ofFunction function) =
      DDS.ofFunction (fun message =>
        CBCCombinatorics.cbc function (blockForm message)) := by
  -- Expand CBC as a bounded-inner-query DDC against the stateless function.
  rw [cbc]
  calc
    applySystem
        (DDC.ofBoundedInnerQueries (CBCCombinatorics.blockBound blockForm)
          (fun message answers _ => response blockForm message answers)
          closeResponse)
        (DDS.ofFunction function) =
      fun outerHistory =>
        DDC.boundedInnerQueryResult
          (CBCCombinatorics.blockBound blockForm)
          (fun message answers _ => response blockForm message answers)
          closeResponse (fun input => some (function input))
          (History.last outerHistory) [] :=
      -- The generic attachment theorem reduces to the recursive bounded result.
      DDC.applySystem_ofBoundedInnerQueries_eq _ _ _ function
    _ = DDS.ofFunction (fun message =>
        CBCCombinatorics.cbc function (blockForm message)) := by
      -- Compare the resulting deterministic systems on each history.
      apply DDS.ext
      intro outerHistory
      -- The recurrence evaluates the bounded queries to the ordinary CBC fold.
      rw [boundedInnerQueryResult_cbc]
      rfl

/-- CR18, Equation (6.1) and the following sentence (printed p. 126), state
that “the filter `[r]` is irrelevant because the restriction implied by `θ_r`
guarantees that at most `r` queries are made”.  This is the corresponding
equality of complete-history functions. -/
theorem applySystem_theta_cbc_queryLimit_ofFunction
    [Fintype M] [AddMonoid X]
    (function : X → X) (blockForm : M → List X) (limit : Nat) :
    applySystem (theta blockForm limit)
        (applySystem (cbc blockForm)
          (applySystem (queryLimit limit) (DDS.ofFunction function))) =
      applySystem (theta blockForm limit)
        (applySystem (cbc blockForm) (DDS.ofFunction function)) := by
  -- Evaluate the outer restriction on both sides.
  rw [applySystem_theta, applySystem_theta]
  apply DDS.ext
  intro outerHistory
  by_cases admitted :
      CBCCombinatorics.totalBlocks blockForm outerHistory.queries ≤ limit
  -- For an admitted history, use its compatible unrestricted transcript.
  · simp only [admitted, if_pos]
    obtain ⟨transcript, compatible⟩ := Attachment.exists_compatible
      (cbc blockForm) (DDS.ofFunction function) outerHistory
    have queryCount : (Attachment.innerQueries transcript.responses).length =
        CBCCombinatorics.totalBlocks blockForm outerHistory.queries := by
      -- CBC issues one inner query per encoded block across the outer history.
      have queryList := DDC.innerQueries_ofBoundedInnerQueries_eq
        (CBCCombinatorics.blockBound blockForm)
        (fun message answers _ => response blockForm message answers)
        closeResponse function outerHistory transcript
        (by simpa only [cbc] using compatible)
      rw [queryList,
        innerQueriesWithinBoundContinuation_cbc_length]
      exact congrArg (CBCCombinatorics.totalBlocks blockForm)
        (List.cons_head_tail outerHistory.nonempty)
    -- The admitted total block count places every inner query within the limit.
    have within : ([] : List X).length +
        (Attachment.innerQueries transcript.responses).length ≤ limit := by
      -- Substitute the transcript query count into the admitted block bound.
      simpa only [List.length_nil, zero_add, queryCount] using admitted
    have compatibleRestricted : Attachment.Compatible (cbc blockForm)
        (applySystem (queryLimit limit) (DDS.ofFunction function))
        outerHistory transcript :=
      -- Reuse the transcript because the query-limit DDS agrees along its query list.
      Attachment.CompatibleFrom.congr_dds_of_length_le _ _ _ compatible limit
        (fun history historyWithin => by
          rw [applySystem_queryLimit]
          simp [historyWithin]) within
    have restrictedValue : applySystem (cbc blockForm)
          (applySystem (queryLimit limit) (DDS.ofFunction function))
          outerHistory = transcript.final.2 :=
      -- Compatibility identifies the restricted attachment result.
      (applySystem_eq_iff _ _ _ _).mpr
        ⟨transcript, compatibleRestricted, HEq.rfl⟩
    have unrestrictedValue : applySystem (cbc blockForm)
          (DDS.ofFunction function) outerHistory = transcript.final.2 :=
      -- The same transcript identifies the unrestricted attachment result.
      (applySystem_eq_iff _ _ _ _).mpr
        ⟨transcript, compatible, HEq.rfl⟩
    exact restrictedValue.trans unrestrictedValue.symm
  -- Outside the `θ_r` block bound, both sides reject.
  · simp [admitted]

/-- Applying the CBC converter to the uniform round-function PDS is exactly
the directly induced CBC PDS. -/
theorem apply_cbc_randomFunction [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype M] [DecidableEq M] [AddMonoid X]
    (blockForm : M → List X) :
    PDS.apply (cbc blockForm) randomFunction = cbcPDS blockForm := by
  -- Compare the normalized distributions carried by the two PDS values.
  apply Subtype.ext
  change Distribution.fTransform (applySystem (cbc blockForm))
      (Distribution.fTransform DDS.ofFunction
        (Distribution.uniform (X → X))) =
    Distribution.fTransform
      (fun function : X → X =>
        DDS.ofFunction (fun message =>
          CBCCombinatorics.cbc function (blockForm message)))
      (Distribution.uniform (X → X))
  rw [Distribution.fTransform_fTransform]
  -- The pointwise bounded-query equation identifies the pushforward maps.
  congr 1
  funext function
  exact applySystem_cbc_ofFunction function blockForm

/-- The `[r]R` system with `θ_r CBC` attached is exactly the direct CBC law
restricted by `θ_r`.  This is the normalized finite-message form of CR18,
Equation (6.1) (printed p. 126). -/
theorem realPDS_eq [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype M] [DecidableEq M] [AddMonoid X]
    (blockForm : M → List X) (limit : Nat) :
    realPDS blockForm limit =
      PDS.apply (theta blockForm limit) (cbcPDS blockForm) := by
  -- Compare the normalized distributions after expanding the PDS definitions.
  apply Subtype.ext
  change Distribution.fTransform (applySystem (theta blockForm limit))
      (Distribution.fTransform (applySystem (cbc blockForm))
        (Distribution.fTransform (applySystem (queryLimit limit))
          (Distribution.fTransform DDS.ofFunction
            (Distribution.uniform (X → X))))) =
    Distribution.fTransform (applySystem (theta blockForm limit))
      (Distribution.fTransform
        (fun function : X → X =>
          DDS.ofFunction (fun message =>
            CBCCombinatorics.cbc function (blockForm message)))
        (Distribution.uniform (X → X)))
  rw [Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  -- The restricted and unrestricted CBC attachments agree on every admitted history.
  apply Distribution.fTransform_congr
  intro function _
  simpa only [Function.comp_apply, applySystem_cbc_ofFunction] using
    applySystem_theta_cbc_queryLimit_ofFunction function blockForm limit

end

end Applications.CBCMAC
