module

public import Commons.Definitions.StreamCipher
public import Commons.Definitions.NonceAEAD
public import Commons.Definitions.MAC
public import RandomSystems.Typed.Memoryless

/-!
# Nonce and associated-data encrypt-then-MAC

`nonceEncryptThenMAC` attaches to `StreamCipher N M` and `Tagging (N × AD × M) T`.
It authenticates the tuple `(nonce, associated data, ciphertext)` and verifies before decrypting:

```text
  encrypt(n, ad, m) ──► cipher.crypt(n, m) ──c──► auth.tag(n, ad, c) ──t──► (c, t)
  decrypt(n, ad, c, t) ──► auth.verify((n, ad, c), t)
                           ├─true──► cipher.crypt(n, c) ──m──► some m
                           └─false───────────────────────────► none
```

This applies the encrypt-then-MAC rule “Output (c, t)” [1, §9.4.1, p. 367] to the nonce/AD
syntax of [1, §9.5, p. 378]. Here the authentication input is the tuple `(n, ad, c)`; a concrete
byte encoding belongs to the authentication component. Each outside call uses at most two inside
calls, at most one per component. For outside budget `q`, the generated domain guarantee grants each
component `2 * q` queries. Components own their retained keys and randomness.

`nonceEncryptThenMAC.smul_ofFunction` identifies the assembly with `nonceEncryptThenMAC.reply`
for fixed component functions. `nonceEncryptThenMAC.encrypt_decrypt_eq_of_correct` derives
probability-one roundtrips from cipher involution and acceptance of generated tags, using
this equality of typed systems. For a fresh-nonce domain, compose `TypedConverter.filter` for
`nonceUnique AEAD.encryptionNonce` before this converter; the filter supplies the restriction
to `nonceRestricted (AEAD N AD M T q) AEAD.encryptionNonce`.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution
open scoped SystemAlgebra SystemAlgebra.DSL

noncomputable section

-- `N`, `AD`, `M`, `T` carry nonces, associated data, plaintext/ciphertext bodies and tags.
-- Encrypt then tag `(n, ad, c)`; verify that tuple before decrypting with the same `n`.
converter nonceEncryptThenMAC(N AD M T : Type)
    [Fintype N] [Fintype AD] [Fintype M] [Fintype T] : AEAD N AD M T
  inside cipher : StreamCipher N M
  inside auth : Tagging (N × AD × M) T
  on encrypt(nonce : N, associatedData : AD, message : M) → M × T
    ciphertext ← cipher.crypt(nonce, message)
    tag ← auth.tag(nonce, associatedData, ciphertext)
    return (ciphertext, tag)
  on decrypt(nonce : N, associatedData : AD, ciphertext : M, tag : T) → Option M
    valid ← auth.verify((nonce, associatedData, ciphertext), tag)
    if valid
      message ← cipher.crypt(nonce, ciphertext)
      return some message
    else
      return none

-- `N`, `AD`, `M`, `T` are the four finite interface alphabets. Budget `0` below names only
-- their port alphabets, which are the same at every query budget.
variable {N AD M T : Type} [Fintype N] [Fintype AD] [Fintype M] [Fintype T]

/-- Encryption first asks the cipher for `crypt(n, m)`. -/
lemma nonceEncryptThenMAC.encrypt_query_eq
    -- `s` is the converter state; `n`, `ad`, `m` are the caller's encryption input.
    (s : Option Unit) (n : N) (ad : AD) (m : M) :
    nonceEncryptThenMAC.body N AD M T s .encrypt (n, ad, m) [] =
      .inr ⟨.inl .crypt, (n, m)⟩ := by
  cases s <;> rfl

/-- Encryption authenticates the nonce, associated data and returned ciphertext together. -/
lemma nonceEncryptThenMAC.encrypt_tag_query_eq
    -- `s` is the converter state; `c` is the reply to encryption of `(n, m)`.
    (s : Option Unit) (n : N) (ad : AD) (m c : M) :
    nonceEncryptThenMAC.body N AD M T s .encrypt (n, ad, m)
      [(⟨.inl .crypt, (n, m)⟩, ⟨.inl .crypt, c⟩)] =
        .inr ⟨.inr .tag, (n, ad, c)⟩ := by
  cases s <;> simp only [nonceEncryptThenMAC.body, callProg, ↓reduceDIte]

/-- Decryption first verifies the complete authentication tuple and supplied tag. -/
lemma nonceEncryptThenMAC.decrypt_query_eq
    -- `s` is the converter state; `n`, `ad`, `c`, `t` are the caller's decryption input.
    (s : Option Unit) (n : N) (ad : AD) (c : M) (t : T) :
    nonceEncryptThenMAC.body N AD M T s .decrypt (n, ad, c, t) [] =
      .inr ⟨.inr .verify, ((n, ad, c), t)⟩ := by
  cases s <;> rfl

/-- Accepted verification permits decryption with the submitted nonce and ciphertext. -/
lemma nonceEncryptThenMAC.decrypt_cipher_query_eq
    -- `s` is the converter state; the tuple `(n, ad, c)` and tag `t` have been accepted.
    (s : Option Unit) (n : N) (ad : AD) (c : M) (t : T) :
    nonceEncryptThenMAC.body N AD M T s .decrypt (n, ad, c, t)
      [(⟨.inr .verify, ((n, ad, c), t)⟩, ⟨.inr .verify, true⟩)] =
        .inr ⟨.inl .crypt, (n, c)⟩ := by
  cases s <;> simp only [nonceEncryptThenMAC.body, callProg, ↓reduceDIte, ↓reduceIte]

/-- Rejected verification returns `none` after its sole inside call. -/
lemma nonceEncryptThenMAC.decrypt_eq_false
    -- `s` is the converter state; verification rejected `(n, ad, c)` with tag `t`.
    (s : Option Unit) (n : N) (ad : AD) (c : M) (t : T) :
    nonceEncryptThenMAC.body N AD M T s .decrypt (n, ad, c, t)
      [(⟨.inr .verify, ((n, ad, c), t)⟩, ⟨.inr .verify, false⟩)] =
        .inl (some (), none) := by
  cases s <;> simp only [nonceEncryptThenMAC.body, callProg, returnProg, ↓reduceDIte,
    Bool.false_eq_true, ↓reduceIte]

/-- Encryption returns the ciphertext and tag after the two prescribed queries. -/
lemma nonceEncryptThenMAC.encrypt_eq
    -- `s` is the converter state; `c`, `t` are replies to encrypting `(n, ad, m)`.
    (s : Option Unit) (n : N) (ad : AD) (m c : M) (t : T) :
    nonceEncryptThenMAC.body N AD M T s .encrypt (n, ad, m)
      [(⟨.inl .crypt, (n, m)⟩, ⟨.inl .crypt, c⟩),
       (⟨.inr .tag, (n, ad, c)⟩, ⟨.inr .tag, t⟩)] = .inl (some (), (c, t)) := by
  cases s <;> simp only [nonceEncryptThenMAC.body, callProg, returnProg, ↓reduceDIte]

/-- Accepted decryption returns the cipher's reply as `some m`. -/
lemma nonceEncryptThenMAC.decrypt_eq_true
    -- `s` is the converter state; the accepted `(n, ad, c, t)` decrypts to reply `m`.
    (s : Option Unit) (n : N) (ad : AD) (c : M) (t : T) (m : M) :
    nonceEncryptThenMAC.body N AD M T s .decrypt (n, ad, c, t)
      [(⟨.inr .verify, ((n, ad, c), t)⟩, ⟨.inr .verify, true⟩),
       (⟨.inl .crypt, (n, c)⟩, ⟨.inl .crypt, m⟩)] = .inl (some (), some m) := by
  cases s <;> simp only [nonceEncryptThenMAC.body, callProg, returnProg, ↓reduceDIte, ↓reduceIte]

/-- Encryption returns `(crypt(n, m), tag(n, ad, crypt(n, m)))`; accepted decryption
returns `some (crypt(n, c))`, and rejected verification returns `none`. -/
def nonceEncryptThenMAC.reply
    -- `crypt` encrypts and decrypts at a fixed nonce; `auth` tags and verifies complete tuples.
    (crypt : N × M → M)
    (auth : ∀ i, (Tagging (N × AD × M) T 0).X i → (Tagging (N × AD × M) T 0).Y i) :
    ∀ i, (AEAD N AD M T 0).X i → (AEAD N AD M T 0).Y i
  | .encrypt, (n, ad, m) => let c := crypt (n, m); (c, auth .tag (n, ad, c))
  | .decrypt, (n, ad, c, t) =>
      if auth .verify ((n, ad, c), t) then some (crypt (n, c)) else none

/-- Attaching fixed cipher and authentication functions gives exactly `reply` on every history. -/
lemma nonceEncryptThenMAC.smul_ofFunction
    -- `crypt` and `auth` give the component replies, including arbitrary verification answers.
    (crypt : N × M → M)
    (auth : ∀ i, (Tagging (N × AD × M) T 0).X i → (Tagging (N × AD × M) T 0).Y i)
    -- `q` bounds outside queries; each component receives the generated allowance `2 * q`.
    (q : ℕ) :
    nonceEncryptThenMAC N AD M T •
        (TypedSystem.ofFunction (A := StreamCipher N M (2 * q)) (fun _ x => crypt x) ∥
          TypedSystem.ofFunction (A := Tagging (N × AD × M) T (2 * q)) auth) =
      TypedSystem.ofFunction (A := AEAD N AD M T q) (nonceEncryptThenMAC.reply crypt auth) := by
  -- Point laws identify the supplied functions with the program attachment law.
  change nonceEncryptThenMAC N AD M T •
      (TypedSystem.ofMemoryless (StreamCipher N M (2 * q))
        (fun _ x => ProbDist.single (crypt x)) ∥
       TypedSystem.ofMemoryless (Tagging (N × AD × M) T (2 * q))
        (fun j x => ProbDist.single (auth j x))) =
    TypedSystem.ofMemoryless (AEAD N AD M T q)
      (fun i x => ProbDist.single (nonceEncryptThenMAC.reply crypt auth i x))
  rw [Interface.cc_parallel_eq, TypedSystem.parallel_ofMemoryless,
    nonceEncryptThenMAC, nonceEncryptThenMAC.program]
  apply TypedConverter.ofProgram_smul_ofMemoryless _ _ _ _ rfl
  intro s i x
  cases i with
  | encrypt =>
    -- Encryption queries the cipher, then authenticates the complete tuple with its reply.
    simp only [Program.memorylessReplyLaw,
      (nonceEncryptThenMAC.encrypt_query_eq (T := T)),
      (nonceEncryptThenMAC.encrypt_tag_query_eq (T := T)),
      (nonceEncryptThenMAC.encrypt_eq (N := N) (AD := AD) (M := M) (T := T)),
      RandomSystem.parallelLaw, ProbDist.single, bindK_single, one_smul,
      List.nil_append, List.cons_append, nonceEncryptThenMAC.reply]
  | decrypt =>
    rcases x with ⟨n, ad, c, t⟩
    -- The fixed verification answer selects either one cipher call or immediate rejection.
    cases hv : auth .verify ((n, ad, c), t) <;>
      simp only [Program.memorylessReplyLaw,
        (nonceEncryptThenMAC.decrypt_query_eq (N := N) (AD := AD) (M := M) (T := T)),
        (nonceEncryptThenMAC.decrypt_cipher_query_eq (N := N) (AD := AD) (M := M) (T := T)),
        (nonceEncryptThenMAC.decrypt_eq_false (N := N) (AD := AD) (M := M) (T := T)),
        (nonceEncryptThenMAC.decrypt_eq_true (N := N) (AD := AD) (M := M) (T := T)),
        RandomSystem.parallelLaw, ProbDist.single, bindK_single, one_smul,
        List.nil_append, List.cons_append, nonceEncryptThenMAC.reply,
        hv, Bool.false_eq_true, ↓reduceIte]

/-- With the same nonce and associated data, decryption recovers the encrypted message.
This is the equation “D(k, E(k, m, d, N), d, N) = m” of [1, §9.5, p. 378]. -/
lemma nonceEncryptThenMAC.reply_decrypt_encrypt_eq
    -- `crypt` is involutive at each nonce, as stated by `hcrypt`.
    (crypt : N × M → M) (hcrypt : ∀ n m, crypt (n, crypt (n, m)) = m)
    -- `auth` accepts every tag it generates, as stated by `hauth`.
    (auth : ∀ i, (Tagging (N × AD × M) T 0).X i → (Tagging (N × AD × M) T 0).Y i)
    (hauth : ∀ x, auth .verify (x, auth .tag x) = true)
    -- `n`, `ad`, `m` are the encryption input, reused unchanged for decryption.
    (n : N) (ad : AD) (m : M) :
    let ct := nonceEncryptThenMAC.reply crypt auth .encrypt (n, ad, m)
    nonceEncryptThenMAC.reply crypt auth .decrypt (n, ad, ct.1, ct.2) = some m := by
  simp only [nonceEncryptThenMAC.reply, hauth, ↓reduceIte, hcrypt]

/-- At fixed component functions, the assembly gives probability one to encrypting and then
recovering the message with the same nonce and associated data, from the supplied contracts. -/
theorem nonceEncryptThenMAC.encrypt_decrypt_eq_of_correct
    -- `crypt` encrypts/decrypts; `hcrypt` gives involution at each caller-supplied nonce.
    (crypt : N × M → M) (hcrypt : ∀ n m, crypt (n, crypt (n, m)) = m)
    -- `auth` supplies tagging/verification; `hauth` accepts its generated tags.
    (auth : ∀ i, (Tagging (N × AD × M) T 0).X i → (Tagging (N × AD × M) T 0).Y i)
    (hauth : ∀ x, auth .verify (x, auth .tag x) = true)
    -- `q` admits the two outside queries; `n`, `ad`, `m` are their common input data.
    {q : ℕ} (hq : 2 ≤ q) (n : N) (ad : AD) (m : M) :
    let ct := nonceEncryptThenMAC.reply crypt auth .encrypt (n, ad, m)
    (nonceEncryptThenMAC N AD M T (budget := q) •
        (TypedSystem.ofFunction (A := StreamCipher N M (2 * q)) (fun _ x => crypt x) ∥
          TypedSystem.ofFunction (A := Tagging (N × AD × M) T (2 * q)) auth) :
          TypedSystem (AEAD N AD M T q)).1
      [(⟨.encrypt, (n, ad, m)⟩, ⟨.encrypt, ct⟩),
       (⟨.decrypt, (n, ad, ct.1, ct.2)⟩, ⟨.decrypt, some m⟩)] = 1 := by
  -- The attachment equality transfers the functional roundtrip to the named converter assembly.
  dsimp only
  rw [nonceEncryptThenMAC.smul_ofFunction]
  apply TypedSystem.ofFunction_mass_eq_one
  · -- The two-query history is nonempty and has length at most `q` by `hq`.
    refine Or.inr ⟨?_, hq⟩
    intro h
    cases h
  · -- Encryption defines `ct`; the functional correctness equation supplies decryption.
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · rfl
    · exact congrArg (fun y => (⟨AEAD.Port.decrypt, y⟩ : Σ i, (AEAD N AD M T q).Y i))
        (nonceEncryptThenMAC.reply_decrypt_encrypt_eq crypt hcrypt auth hauth n ad m).symm

end

end Commons
