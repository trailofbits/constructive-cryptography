module

public import RandomSystems.Typed.RecordingGuard
public import Commons.Definitions.AEAD

/-!
# Recorded-ciphertext rejection

`wrapper • inside` records encryption replies and rejects their subsequent decryption.
The inside counter stays at one after that rejection; decrypting a different ciphertext
advances it to two. `wrapped_eq` identifies this transition test with attachment.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Tests.RecordingGuard
open SystemAlgebra SystemAlgebra.TypedConverter Probability.Distribution
open scoped List

/-- Three encryption/decryption queries with Boolean messages and ciphertexts. -/
abbrev A := Commons.AE Bool Bool 3

/-- Record the ciphertext from `enc(m) ⇒ c`; decryption records nothing. -/
def recordCiphertext : ∀ i : A.I, A.X i → A.Y i → Option Bool
  | .enc, _, c => some c
  | .dec, _, _ => none

/-- Reply `none` to `dec(c)` when `c` was recorded; forward every other query.
[1, Attack Game 9.2, p. 362] permits a ciphertext “not among the responses to the previous
encryption queries”; `none` extends the rule to the recorded ciphertexts. -/
def rejectRecorded (keys : List Bool) : ∀ i : A.I, A.X i → Option (A.Y i)
  | .enc, _ => none
  | .dec, c => if c ∈ keys then some none else none

/-- Removing inputs preserves the three-query limit. -/
lemma admitted_sublist {xs ys : List (Σ i, A.X i)}
    (hs : xs <+ ys) (hx : xs ≠ []) (hy : A.domain ys) : A.domain xs :=
  ⟨hx, hs.length_le.trans hy.2⟩

/-- The recording guard on the same encryption/decryption interface `A`. -/
noncomputable def wrapper : TypedConverter A A :=
  recordingGuard recordCiphertext rejectRecorded admitted_sublist

/-- `enc(m) ⇒ !m`, `dec(c) ⇒ some (!c)`; each inside call increments counter `n`. -/
def oracleTransition (n : ℕ) : ∀ i : A.I, A.X i → ℕ × A.Y i
  | .enc, m => (n + 1, !m)
  | .dec, c => (n + 1, some (!c))

/-- The counter starts at zero; later replies follow `oracleTransition`. -/
noncomputable def inside : TypedSystem A :=
  TypedSystem.ofAutomaton A oracleTransition (ProbDist.single 0)

/-- Attach the recorded-ciphertext guard to the counting oracle. -/
noncomputable def wrapped : TypedSystem A := wrapper • inside

/-- The attached transition retains both the ciphertext list and the inside counter. -/
noncomputable def combined :
    List Bool × ℕ → (i : A.I) → A.X i → (List Bool × ℕ) × A.Y i :=
  (recordingGuardProgram recordCiphertext rejectRecorded).combine oracleTransition
    (recordingGuardProgram_bounded recordCiphertext rejectRecorded)

/-- Encryption records its reply and uses one inside call. -/
example : combined ([], 0) .enc true = (([false], 1), false) := by
  rw [combined, recordingGuardProgram_combine]
  simp only [rejectRecorded, oracleTransition, recordCiphertext, Option.elim_some,
    List.insert_nil, Bool.not_true]

/-- Decrypting that ciphertext rejects and leaves the inside counter unchanged. -/
example : combined ([false], 1) .dec false = (([false], 1), none) := by
  rw [combined, recordingGuardProgram_combine]
  simp only [rejectRecorded, List.mem_singleton, ↓reduceIte]

/-- A different ciphertext is forwarded; its reply is returned and the counter advances. -/
example : combined ([false], 1) .dec true = (([false], 2), some false) := by
  rw [combined, recordingGuardProgram_combine]
  simp only [rejectRecorded, List.mem_singleton, Bool.true_eq_false, ↓reduceIte,
    oracleTransition, recordCiphertext, Option.elim_none, Bool.not_true]

/-- Recording a repeated reply preserves the set; a fresh reply inserts its own value. -/
example : combined ([false], 1) .enc true = (([false], 2), false) ∧
    combined ([false], 1) .enc false = (([true, false], 2), true) := by
  constructor
  · rw [combined, recordingGuardProgram_combine]
    simp only [rejectRecorded, oracleTransition, recordCiphertext, Option.elim_some,
      Bool.not_true, List.insert_of_mem (List.mem_singleton_self _)]
  · rw [combined, recordingGuardProgram_combine]
    simp only [rejectRecorded, oracleTransition, recordCiphertext, Option.elim_some, Bool.not_false]
    rw [List.insert_of_not_mem (by simp only [List.mem_singleton, Bool.true_eq_false,
      not_false_eq_true])]

/-- Rejecting a recorded ciphertext costs zero calls; forwarding a fresh one costs one. -/
example :
    Program.CallCost 0
      (recordingGuardProgram recordCiphertext rejectRecorded [false] .dec false) ∧
    Program.CallCost 1
      (recordingGuardProgram recordCiphertext rejectRecorded [false] .dec true) := by
  constructor
  · simpa only [rejectRecorded, List.mem_singleton, ↓reduceIte, Option.elim_some] using
      recordingGuardProgram_cost recordCiphertext rejectRecorded [false] .dec false
  · simpa only [rejectRecorded, List.mem_singleton, Bool.true_eq_false,
      ↓reduceIte, Option.elim_none] using
      recordingGuardProgram_cost recordCiphertext rejectRecorded [false] .dec true

/-- The tested transition is the actual attached system, initialized with an empty record. -/
lemma wrapped_eq : wrapped = TypedSystem.ofAutomaton A combined (ProbDist.single ([], 0)) := by
  rw [wrapped, wrapper, inside, recordingGuard_smul_ofAutomaton]
  congr 1
  apply Subtype.ext
  exact Probability.Distribution.fTransform_single _ _ _

#print axioms DDC.insideQueries_sublist_outsideInputs
#print axioms recordingGuardProgram_combine
#print axioms recordingGuard_smul_ofAutomaton
#print axioms wrapped_eq

end Tests.RecordingGuard
