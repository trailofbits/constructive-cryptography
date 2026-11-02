module

public import Commons.Definitions.Nonce
public import Examples.DSL.AEAD

/-!
# Nonce admission and rejection replies

The AEAD encryption port consumes a nonce; decryption may reuse it. The checks distinguish
nonce uniqueness from the original query allowance. Filtering preserves the cumulative
probability of an admitted transcript containing a rejection reply.
-/

@[expose] public section

namespace Tests.NonceDomain

open Commons SystemAlgebra DSLExamples.Authenticated

/-- Encryption with input `(n, ad, m)` selects `some n`; decryption selects `none`. -/
def encryptionNonce
    -- `q` bounds the total number of queries to the two AEAD ports.
    {q : ℕ} : (Σ i, (AEAD q).X i) → Option Nonce
  | ⟨.encrypt, (n, _, _)⟩ => some n
  | ⟨.decrypt, _⟩ => none

-- `n` is the nonce, `ad` associated data, `m` plaintext, `c` ciphertext and `tag` its tag.
variable (n : Nonce) (ad m c : Message) (tag : Commons.AES.Block)

/-- One encryption followed by two decryptions with its nonce fits the allowance of three. -/
example :
    (nonceRestricted (AEAD 3) encryptionNonce).domain
      [⟨.encrypt, (n, ad, m)⟩, ⟨.decrypt, (n, ad, c, tag)⟩,
        ⟨.decrypt, (n, ad, c, tag)⟩] := by
  constructor
  · -- The input history is nonempty and has length three.
    constructor
    · intro h; cases h
    · norm_num
  · -- Neither decryption adds to the list containing the encryption nonce.
    change nonceUnique (encryptionNonce (q := 3))
      ([⟨.encrypt, (n, ad, m)⟩, ⟨.decrypt, (n, ad, c, tag)⟩] ++
        [⟨.decrypt, (n, ad, c, tag)⟩])
    rw [nonceUnique_snoc_none encryptionNonce _ _ rfl]
    change nonceUnique encryptionNonce
      ([⟨.encrypt, (n, ad, m)⟩] ++ [⟨.decrypt, (n, ad, c, tag)⟩])
    rw [nonceUnique_snoc_none encryptionNonce _ _ rfl]
    exact List.nodup_singleton n

/-- Two decryptions consume no fresh nonce but exceed the allowance of one query. -/
example : ¬(nonceRestricted (AEAD 1) encryptionNonce).domain
    [⟨.decrypt, (n, ad, c, tag)⟩, ⟨.decrypt, (n, ad, c, tag)⟩] := by
  intro h
  have bound := h.1.2
  norm_num at bound

/-- Two encryptions fit the original allowance, but their nonces must differ even if their
associated data and plaintexts differ. -/
example
    -- `ad'`, `m'` may change while the encryption nonce `n` stays fixed.
    (ad' m' : Message) :
    (AEAD 2).domain [⟨.encrypt, (n, ad, m)⟩, ⟨.encrypt, (n, ad', m')⟩] ∧
    ¬(nonceRestricted (AEAD 2) encryptionNonce).domain
      [⟨.encrypt, (n, ad, m)⟩, ⟨.encrypt, (n, ad', m')⟩] := by
  constructor
  · constructor
    · intro h; cases h
    · norm_num
  · -- The second query selects `n` again, independently of its data and message.
    intro h
    have unique := h.2
    change nonceUnique encryptionNonce
      ([⟨.encrypt, (n, ad, m)⟩] ++ [⟨.encrypt, (n, ad', m')⟩]) at unique
    rw [nonceUnique_snoc_some encryptionNonce _ _ n rfl] at unique
    exact unique.2 (by simp only [List.filterMap_cons, encryptionNonce,
      List.filterMap_nil, List.mem_cons, true_or])

/-- Two distinct encryption nonces satisfy both the nonce condition and the allowance. -/
example
    -- `fresh` separates the second nonce `n'` from the first nonce `n`.
    (n' : Nonce) (fresh : n' ≠ n) :
    (nonceRestricted (AEAD 2) encryptionNonce).domain
      [⟨.encrypt, (n, ad, m)⟩, ⟨.encrypt, (n', ad, m)⟩] := by
  constructor
  · constructor
    · intro h; cases h
    · norm_num
  · change nonceUnique encryptionNonce
      ([⟨.encrypt, (n, ad, m)⟩] ++ [⟨.encrypt, (n', ad, m)⟩])
    rw [nonceUnique_snoc_some encryptionNonce _ _ n' rfl]
    simp only [nonceUnique, List.filterMap_cons, encryptionNonce, List.filterMap_nil,
      List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      List.mem_cons, or_false, fresh, and_self]

/-- Decryption may reuse the encryption nonce and return `none`; filtering keeps that mass. -/
example
    -- `R` is any system on the AEAD interface with two allowed queries.
    (R : TypedSystem (AEAD 2))
    -- `c'`, `tag'` describe the decryption candidate; encryption returned `(c, tag)`.
    (c' : Message) (tag' : AES.Block) :
    (TypedConverter.filter (AEAD 2) (nonceUnique encryptionNonce)
      (nonceUnique_prefix encryptionNonce) • R).1
      [(⟨.encrypt, (n, ad, m)⟩, ⟨.encrypt, (c, tag)⟩),
        (⟨.decrypt, (n, ad, c', tag')⟩, ⟨.decrypt, none⟩)] =
    R.1 [(⟨.encrypt, (n, ad, m)⟩, ⟨.encrypt, (c, tag)⟩),
      (⟨.decrypt, (n, ad, c', tag')⟩, ⟨.decrypt, none⟩)] := by
  -- The filter changes admission, while keeping each admitted transcript probability.
  apply TypedConverter.filter_mass_of_admitted
  apply Or.inr
  constructor
  · constructor
    · intro h; cases h
    · norm_num
  · change nonceUnique encryptionNonce
      ([⟨.encrypt, (n, ad, m)⟩] ++ [⟨.decrypt, (n, ad, c', tag')⟩])
    rw [nonceUnique_snoc_none encryptionNonce _ _ rfl]
    exact List.nodup_singleton n

/-- A second encryption under the same nonce has zero probability after filtering. -/
example (R : TypedSystem (AEAD 2)) :
    (TypedConverter.filter (AEAD 2) (nonceUnique encryptionNonce)
      (nonceUnique_prefix encryptionNonce) • R).1
      [(⟨.encrypt, (n, ad, m)⟩, ⟨.encrypt, (c, tag)⟩),
        (⟨.encrypt, (n, ad, m)⟩, ⟨.encrypt, (c, tag)⟩)] = 0 := by
  classical
  rw [TypedConverter.filter_smul]
  -- Restriction assigns zero to a transcript outside the selected input domain.
  change (if Admitted (nonceRestricted (AEAD 2) encryptionNonce).inputDomain _ then _ else 0) = 0
  apply ite_eq_right
  rw [admitted_ofInputs_iff (nonceRestricted (AEAD 2) encryptionNonce).nonempty_prefix]
  rintro (h | h)
  · cases h
  · have unique := h.2
    simp only [List.map_cons, List.map_nil, nonceUnique, List.filterMap_cons,
      encryptionNonce, List.filterMap_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, or_false,
      not_true_eq_false, false_and] at unique

end Tests.NonceDomain
