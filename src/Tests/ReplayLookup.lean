module

public import Commons.Definitions.AEAD
public import Commons.Definitions.PublicKeyEncryption

/-!
# Replay lookup regression checks

Both tuple orientations keep the first message when ciphertexts repeat. The duplicate checks
use distinct message and ciphertext types and conflicting messages at one ciphertext. The
encryption checks verify chronological insertion for every stored table, including initialization.
A miss calls the inner decryption port and returns its reply in both CCA converters, and returns
rejection in the ideal AE and ciphertext-integrity converters.
-/

@[expose] public section

open Commons SystemAlgebra.DSL

namespace ReplayLookupTests

-- `K` carries lookup keys and `V` recorded values, with equality required only for keys.
variable {K V : Type*} [DecidableEq K]

/-- A later duplicate key preserves the original lookup, for arbitrary accumulated records. -/
lemma lookup_append_duplicate
    -- `h` says `table` already returns `first` at `key`; `later` is the appended value.
    (table : List (K × V)) (key : K) (first later : V)
    (h : table.lookup key = some first) :
    (table ++ [(key, later)]).lookup key = some first := by
  rw [List.lookup_append, h, Option.some_or]

/-- A fresh key becomes available at its first insertion. -/
lemma lookup_append_fresh
    -- `h` says `key` is absent from `table`; insertion records `value` there.
    (table : List (K × V)) (key : K) (value : V) (h : table.lookup key = none) :
    (table ++ [(key, value)]).lookup key = some value := by
  rw [List.lookup_append, h, Option.none_or, List.lookup_cons_self]

/-- AE's value/key orientation has the same insertion rule as the key/value orientation. -/
lemma replay_append
    -- `M` carries messages and `C` ciphertexts; lookup compares ciphertexts.
    {M C : Type} [DecidableEq C]
    -- Append `(message, ciphertext)` and look up `query`, preserving any earlier answer.
    (table : List (M × C)) (query ciphertext : C) (message : M) :
    AE.replay (table ++ [(message, ciphertext)]) query =
      (AE.replay table query).or (if query == ciphertext then some message else none) := by
  simp only [AE.replay, List.map_append, List.map_cons, List.map_nil, Prod.swap_prod_mk]
  rw [List.lookup_append, List.lookup_cons, List.lookup_nil]
  cases query == ciphertext <;> rfl

/-- AE CCA appends the requested message and returned ciphertext, including duplicate keys. -/
example (table : Option (List (Bool × Bool))) (message replacement reply : Bool) :
    AE.CCA.body Bool Bool table .enc message
      [(⟨.inr (), ()⟩, ⟨.inr (), replacement⟩),
        (⟨.inl .enc, replacement⟩, ⟨.inl .enc, reply⟩)] =
      .inl (some (table.getD [] ++ [(message, reply)]), reply) := by
  cases table <;> simp only [AE.CCA.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- PKE CCA appends the same record with ciphertext first, including duplicate keys. -/
example (table : Option (List (Bool × Bool))) (message replacement reply : Bool) :
    PKE.CCA.body Unit Bool Bool table .enc message
      [(⟨.inr (), ()⟩, ⟨.inr (), replacement⟩),
        (⟨.inl .enc, replacement⟩, ⟨.inl .enc, reply⟩)] =
      .inl (some (table.getD [] ++ [(reply, message)]), reply) := by
  cases table <;> simp only [PKE.CCA.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- Ideal AE appends the requested message paired with the replacement's ciphertext. -/
example (table : Option (List (Bool × Bool))) (message replacement reply : Bool) :
    AE.Ideal.body Bool Bool table .enc message
      [(⟨.inr (), ()⟩, ⟨.inr (), replacement⟩),
        (⟨.inl .enc, replacement⟩, ⟨.inl .enc, reply⟩)] =
      .inl (some (table.getD [] ++ [(message, reply)]), reply) := by
  cases table <;> simp only [AE.Ideal.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- The ciphertext-integrity converter appends each encryption's message/ciphertext pair. -/
example (table : Option (List (Bool × Bool))) (message reply : Bool) :
    AE.CTXT.body Bool Bool table .enc message
      [(⟨.enc, message⟩, ⟨.enc, reply⟩)] =
      .inl (some (table.getD [] ++ [(message, reply)]), reply) := by
  cases table <;> simp only [AE.CTXT.body, callProg, returnProg, ↓reduceDIte, Option.getD]

/-- AE CCA returns the first Boolean message for a repeated unit ciphertext without a call. -/
example : AE.CCA.body Bool Unit (some [(false, ()), (true, ())]) .dec () [] =
    .inl (some [(false, ()), (true, ())], some false) := rfl

/-- PKE CCA returns the same first message with the opposite tuple orientation. -/
example : PKE.CCA.body Unit Bool Unit (some [((), false), ((), true)]) .dec () [] =
    .inl (some [((), false), ((), true)], some false) := rfl

/-- Ideal AE returns the first message at a repeated ciphertext. -/
example : AE.Ideal.body Bool Unit (some [(false, ()), (true, ())]) .dec () [] =
    .inl (some [(false, ()), (true, ())], some false) := rfl

/-- The ciphertext-integrity converter returns the same first message. -/
example : AE.CTXT.body Bool Unit (some [(false, ()), (true, ())]) .dec () [] =
    .inl (some [(false, ()), (true, ())], some false) := rfl

/-- An unseen ciphertext is forwarded to the AE decryption port. -/
example : AE.CCA.body Bool Bool (some [(false, false)]) .dec true [] =
    .inr ⟨.inl .dec, true⟩ := rfl

/-- An unseen ciphertext is forwarded to the PKE decryption port. -/
example : PKE.CCA.body Unit Bool Bool (some [(false, false)]) .dec true [] =
    .inr ⟨.inl .dec, true⟩ := rfl

/-- AE CCA returns the inner reply unchanged, including rejection. -/
example (result : Option Bool) :
    AE.CCA.body Bool Bool (some [(false, false)]) .dec true
      [(⟨.inl .dec, true⟩, ⟨.inl .dec, result⟩)] =
      .inl (some [(false, false)], result) := by
  have h : AE.replay [(false, false)] true = none := rfl
  simp only [AE.CCA.body, h, callProg, returnProg, ↓reduceDIte]

/-- PKE CCA returns the inner reply unchanged, including rejection. -/
example (result : Option Bool) :
    PKE.CCA.body Unit Bool Bool (some [(false, false)]) .dec true
      [(⟨.inl .dec, true⟩, ⟨.inl .dec, result⟩)] =
      .inl (some [(false, false)], result) := by
  have h : ([(false, false)] : List (Bool × Bool)).lookup true = none := rfl
  simp only [PKE.CCA.body, h, callProg, returnProg, ↓reduceDIte]

/-- Ideal AE rejects an unseen ciphertext without a call. -/
example : AE.Ideal.body Bool Bool (some [(false, false)]) .dec true [] =
    .inl (some [(false, false)], none) := rfl

/-- The ciphertext-integrity converter also rejects an unseen ciphertext. -/
example : AE.CTXT.body Bool Bool (some [(false, false)]) .dec true [] =
    .inl (some [(false, false)], none) := rfl

/-- Before any encryption, AE CCA forwards every ciphertext. -/
example : AE.CCA.body Bool Unit none .dec () [] = .inr ⟨.inl .dec, ()⟩ := rfl

/-- Before any encryption, PKE CCA forwards every ciphertext. -/
example : PKE.CCA.body Unit Bool Unit none .dec () [] = .inr ⟨.inl .dec, ()⟩ := rfl

/-- Before any encryption, ideal AE initializes an empty table and rejects. -/
example : AE.Ideal.body Bool Unit none .dec () [] = .inl (some [], none) := rfl

/-- Before any encryption, ciphertext integrity initializes an empty table and rejects. -/
example : AE.CTXT.body Bool Unit none .dec () [] = .inl (some [], none) := rfl

#print axioms Commons.AE.replay_eq_find?
#print axioms lookup_append_duplicate
#print axioms lookup_append_fresh
#print axioms replay_append

end ReplayLookupTests
