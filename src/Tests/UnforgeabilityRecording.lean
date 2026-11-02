module

public import Commons.Definitions.MAC
public import Commons.Definitions.Signature

/-!
# Recording in unforgeability restrictions

The arbitrary-state body equations check that EUF records the requested message and SUF records
the returned pair. Both return the inner verification result conjoined with the membership test.
The other checks cover insertion membership, pending-call forwarding, freshness and repeated
requests. They distinguish a new valid output for an old message from an issued pair and verify
that signing's public-key port preserves the records.
-/

@[expose] public section

namespace UnforgeabilityRecordingTests

open Commons SystemAlgebra.DSL

-- `M` carries messages, `T` tags or signatures, and `PK` public keys.
variable {M T PK : Type} [Fintype M] [Fintype T] [Fintype PK]
  [DecidableEq M]

/-- Insertion has the same members as chronological append. -/
example (records : List M) (message query : M) :
    query ∈ records.insert message ↔ query ∈ records ++ [message] := by
  simp only [List.mem_insert_iff, List.mem_append, List.mem_singleton, or_comm]

/-- Pending MAC calls forward the requested message or verification pair. -/
example [DecidableEq T] (messages : Option (List M)) (pairs : Option (List (M × T)))
    (message : M) (output : T) :
    MAC.EUF.body M T messages .tag message [] = .inr ⟨.tag, message⟩ ∧
    MAC.SUF.body M T pairs .tag message [] = .inr ⟨.tag, message⟩ ∧
    MAC.EUF.body M T messages .verify (message, output) [] = .inr ⟨.verify, (message, output)⟩ ∧
    MAC.SUF.body M T pairs .verify (message, output) [] = .inr ⟨.verify, (message, output)⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases messages <;> rfl
  · cases pairs <;> rfl
  · cases messages <;> rfl
  · cases pairs <;> rfl

/-- EUF records the message and returns the supplied tag, including at initialization. -/
lemma mac_euf_record (records : Option (List M)) (message : M) (tag : T) :
    MAC.EUF.body M T records .tag message [(⟨.tag, message⟩, ⟨.tag, tag⟩)] =
      .inl (some ((records.getD []).insert message), tag) := by
  cases records <;> simp only [MAC.EUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- SUF records the returned tag together with its message. -/
lemma mac_suf_record [DecidableEq T] (records : Option (List (M × T))) (message : M) (tag : T) :
    MAC.SUF.body M T records .tag message [(⟨.tag, message⟩, ⟨.tag, tag⟩)] =
      .inl (some ((records.getD []).insert (message, tag)), tag) := by
  cases records <;> simp only [MAC.SUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- Pending signature calls forward the requested message or verification pair. -/
example [DecidableEq T] (messages : Option (List M)) (pairs : Option (List (M × T)))
    (message : M) (output : T) :
    SignatureScheme.EUF.body PK M T messages .sign message [] = .inr ⟨.sign, message⟩ ∧
    SignatureScheme.SUF.body PK M T pairs .sign message [] = .inr ⟨.sign, message⟩ ∧
    SignatureScheme.EUF.body PK M T messages .verify (message, output) [] =
      .inr ⟨.verify, (message, output)⟩ ∧
    SignatureScheme.SUF.body PK M T pairs .verify (message, output) [] =
      .inr ⟨.verify, (message, output)⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases messages <;> rfl
  · cases pairs <;> rfl
  · cases messages <;> rfl
  · cases pairs <;> rfl

/-- Signature EUF records the requested message and returns its signature. -/
lemma signature_euf_record (records : Option (List M)) (message : M) (signature : T) :
    SignatureScheme.EUF.body PK M T records .sign message
      [(⟨.sign, message⟩, ⟨.sign, signature⟩)] =
      .inl (some ((records.getD []).insert message), signature) := by
  cases records <;>
    simp only [SignatureScheme.EUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- Signature SUF records the returned signature together with its message. -/
lemma signature_suf_record [DecidableEq T] (records : Option (List (M × T)))
    (message : M) (signature : T) :
    SignatureScheme.SUF.body PK M T records .sign message
      [(⟨.sign, message⟩, ⟨.sign, signature⟩)] =
      .inl (some ((records.getD []).insert (message, signature)), signature) := by
  cases records <;>
    simp only [SignatureScheme.SUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- MAC verification returns the inner validity bit conjoined with message membership. -/
lemma mac_euf_verify (records : Option (List M)) (message : M) (tag : T) (valid : Bool) :
    MAC.EUF.body M T records .verify (message, tag)
      [(⟨.verify, (message, tag)⟩, ⟨.verify, valid⟩)] =
      .inl (some (records.getD []), valid && (records.getD []).contains message) := by
  cases records <;> simp only [MAC.EUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- Strong MAC verification instead tests membership of the entire pair. -/
lemma mac_suf_verify [DecidableEq T] (records : Option (List (M × T))) (message : M) (tag : T)
    (valid : Bool) :
    MAC.SUF.body M T records .verify (message, tag)
      [(⟨.verify, (message, tag)⟩, ⟨.verify, valid⟩)] =
      .inl (some (records.getD []), valid && (records.getD []).contains (message, tag)) := by
  cases records <;> simp only [MAC.SUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- Signature verification returns the inner validity bit conjoined with message membership. -/
lemma signature_euf_verify (records : Option (List M)) (message : M) (signature : T)
    (valid : Bool) :
    SignatureScheme.EUF.body PK M T records .verify (message, signature)
      [(⟨.verify, (message, signature)⟩, ⟨.verify, valid⟩)] =
      .inl (some (records.getD []), valid && (records.getD []).contains message) := by
  cases records <;>
    simp only [SignatureScheme.EUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- Strong signature verification instead tests membership of the entire pair. -/
lemma signature_suf_verify [DecidableEq T] (records : Option (List (M × T)))
    (message : M) (signature : T)
    (valid : Bool) :
    SignatureScheme.SUF.body PK M T records .verify (message, signature)
      [(⟨.verify, (message, signature)⟩, ⟨.verify, valid⟩)] =
      .inl (some (records.getD []), valid && (records.getD []).contains (message, signature)) := by
  cases records <;>
    simp only [SignatureScheme.SUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- EUF rejects a valid tag on a message that has not been requested. -/
example (records : List M) (message : M) (tag : T) (fresh : message ∉ records) :
    MAC.EUF.body M T (some records) .verify (message, tag)
      [(⟨.verify, (message, tag)⟩, ⟨.verify, true⟩)] = .inl (some records, false) := by
  rw [mac_euf_verify]
  simp only [Option.getD_some, List.contains_eq_mem, fresh, decide_false, Bool.and_false]

/-- Signature EUF has the same new-message rejection rule. -/
example (records : List M) (message : M) (signature : T) (fresh : message ∉ records) :
    SignatureScheme.EUF.body PK M T (some records) .verify (message, signature)
      [(⟨.verify, (message, signature)⟩, ⟨.verify, true⟩)] = .inl (some records, false) := by
  rw [signature_euf_verify]
  simp only [Option.getD_some, List.contains_eq_mem, fresh, decide_false, Bool.and_false]

/-- A repeated message leaves the EUF records fixed even when the next tag differs. -/
example (records : List M) (message : M) (tag : T) :
    MAC.EUF.body M T (some (records.insert message)) .tag message
      [(⟨.tag, message⟩, ⟨.tag, tag⟩)] = .inl (some (records.insert message), tag) := by
  rw [mac_euf_record, Option.getD_some, List.insert_of_mem List.mem_insert_self]

/-- Repeated signing likewise leaves the EUF message records fixed. -/
example (records : List M) (message : M) (signature : T) :
    SignatureScheme.EUF.body PK M T (some (records.insert message)) .sign message
      [(⟨.sign, message⟩, ⟨.sign, signature⟩)] =
      .inl (some (records.insert message), signature) := by
  rw [signature_euf_record, Option.getD_some, List.insert_of_mem List.mem_insert_self]

/-- A fresh valid tag on an old message passes EUF and fails SUF. -/
lemma mac_fresh_tag [DecidableEq T]
    -- `records` contains earlier returned pairs; `message` has just received output `first`.
    (records : List (M × T)) (message : M) (first second : T)
    -- `different` and `fresh` make `second` a new output for that message.
    (different : second ≠ first) (fresh : (message, second) ∉ records) :
    MAC.EUF.body M T (some ((records.map Prod.fst).insert message)) .verify (message, second)
      [(⟨.verify, (message, second)⟩, ⟨.verify, true⟩)] =
      .inl (some ((records.map Prod.fst).insert message), true) ∧
    MAC.SUF.body M T (some (records.insert (message, first))) .verify (message, second)
      [(⟨.verify, (message, second)⟩, ⟨.verify, true⟩)] =
      .inl (some (records.insert (message, first)), false) := by
  -- The message was requested, but neither the first reply nor an earlier pair equals this pair.
  constructor
  · rw [mac_euf_verify]
    simp only [Option.getD_some, List.contains_insert, beq_self_eq_true, Bool.true_or,
      Bool.true_and]
  · rw [mac_suf_verify]
    simp only [Option.getD_some, Bool.true_and, List.contains_eq_mem, List.mem_insert_iff,
      Prod.mk.injEq, true_and, different, fresh, or_self, eq_self, decide_false]

/-- A fresh valid signature on an old message passes EUF and fails SUF. -/
lemma signature_fresh_signature [DecidableEq T]
    -- `records` contains earlier returned pairs; `message` has just received output `first`.
    (records : List (M × T)) (message : M) (first second : T)
    -- `different` and `fresh` make `second` a new output for that message.
    (different : second ≠ first) (fresh : (message, second) ∉ records) :
    SignatureScheme.EUF.body PK M T (some ((records.map Prod.fst).insert message))
      .verify (message, second) [(⟨.verify, (message, second)⟩, ⟨.verify, true⟩)] =
      .inl (some ((records.map Prod.fst).insert message), true) ∧
    SignatureScheme.SUF.body PK M T (some (records.insert (message, first)))
      .verify (message, second) [(⟨.verify, (message, second)⟩, ⟨.verify, true⟩)] =
      .inl (some (records.insert (message, first)), false) := by
  constructor
  · rw [signature_euf_verify]
    simp only [Option.getD_some, List.contains_insert, beq_self_eq_true, Bool.true_or,
      Bool.true_and]
  · rw [signature_suf_verify]
    simp only [Option.getD_some, Bool.true_and, List.contains_eq_mem, List.mem_insert_iff,
      Prod.mk.injEq, true_and, different, fresh, or_self, eq_self, decide_false]

/-- Once a tag is returned, SUF accepts its pair exactly when the inner verifier accepts. -/
example [DecidableEq T] (records : List (M × T)) (message : M) (tag : T) (valid : Bool) :
    MAC.SUF.body M T (some (records.insert (message, tag))) .verify (message, tag)
      [(⟨.verify, (message, tag)⟩, ⟨.verify, valid⟩)] =
      .inl (some (records.insert (message, tag)), valid) := by
  rw [mac_suf_verify]
  simp only [Option.getD_some, List.contains_insert, beq_self_eq_true, Bool.true_or,
    Bool.and_true]

/-- A returned signature has the same acceptance rule, including rejection of invalid pairs. -/
example [DecidableEq T] (records : List (M × T)) (message : M) (signature : T) (valid : Bool) :
    SignatureScheme.SUF.body PK M T (some (records.insert (message, signature)))
      .verify (message, signature) [(⟨.verify, (message, signature)⟩, ⟨.verify, valid⟩)] =
      .inl (some (records.insert (message, signature)), valid) := by
  rw [signature_suf_verify]
  simp only [Option.getD_some, List.contains_insert, beq_self_eq_true, Bool.true_or,
    Bool.and_true]

/-- Public-key queries return the supplied key and preserve the EUF message records. -/
example (records : Option (List M)) (key : PK) :
    SignatureScheme.EUF.body PK M T records .publicKey ()
      [(⟨.publicKey, ()⟩, ⟨.publicKey, key⟩)] =
      .inl (some (records.getD []), key) := by
  cases records <;>
    simp only [SignatureScheme.EUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- Public-key queries also preserve the SUF pair records. -/
example [DecidableEq T] (records : Option (List (M × T))) (key : PK) :
    SignatureScheme.SUF.body PK M T records .publicKey ()
      [(⟨.publicKey, ()⟩, ⟨.publicKey, key⟩)] =
      .inl (some (records.getD []), key) := by
  cases records <;>
    simp only [SignatureScheme.SUF.body, callProg, returnProg, ↓reduceDIte, Option.getD]

#print axioms mac_fresh_tag
#print axioms signature_fresh_signature

end UnforgeabilityRecordingTests
