module

public import Commons.Definitions.AEAD
public import Commons.Definitions.MAC

/-!
# Encrypt-then-MAC

`encryptThenMAC` exposes `AE M (C × T)` from `AE M C` and `Tagging C T`:
encryption returns `(c, t)` after encrypting the message and tagging `c`; decryption verifies
`(c, t)` before requesting decryption of `c`. The `enc_query_eq` and `enc_tag_query_eq` laws
fix encryption then tagging; `dec_query_eq` and `dec_cipher_query_eq` fix verification then
decryption. Its reply laws `encryptThenMAC.enc_eq`,
`encryptThenMAC.dec_eq_true` and `encryptThenMAC.dec_eq_false` specify both branches.
Each invocation uses at most two inside calls, at most one to each component. The generated
uniform allowance gives each component budget `2 * q` for outside budget `q`; the converter
carries the corresponding domain guarantee.

`encryptThenMAC.system` is the assembly
`encryptThenMAC M C T • (AE.system scheme ∥ MAC.system mac)`. The two components retain
independent keys from `scheme.gen` and `mac.gen`; each encryption and tagging call draws fresh
randomness within its component: [1, §9.4.1.1, p. 369], “the two keys ke and km are chosen
independently”; [2, p. 49], “the product distribution of GenΠ and GenΣ”.

```text
  cipher = AE.system scheme  [retains ke ∼ scheme.gen]
  auth   = MAC.system mac    [retains km ∼ mac.gen]

  enc(m) ──► cipher.enc(m) ──c──► auth.tag(c) ──t──► (c, t)
  dec(c,t) ──► auth.verify(c,t) ──true──► cipher.dec(c) ──► m or none
                              └─false──────────────────► none
```

The input/output rule is [1, §9.4.1, p. 367]: “Output (c, t)” and
“if V(km, c, t) = reject then output reject otherwise, output D(ke, c)”.
The source’s `reject` is `none : Option M`.
The Boolean verification interface returns only acceptance; the converter retains `c` for
subsequent decryption, representing the ciphertext-returning verification of [2, p. 49]
through the existing `Tagging` interface.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
2. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

noncomputable section

-- On `enc(m)`, return `(c, t)` from `cipher.enc(m)` then `auth.tag(c)`; on `dec(c, t)`,
-- verify first, then return `cipher.dec(c)` if accepted and `none` otherwise.
-- `M` carries messages, `C` encryption ciphertexts, and `T` tags.
converter encryptThenMAC(M C T : Type) [Fintype M] [Fintype C] [Fintype T] : AE M (C × T)
  inside cipher : AE M C
  inside auth : Tagging C T
  on enc(message : M) → C × T
    ciphertext ← cipher.enc(message)
    tag ← auth.tag(ciphertext)
    return (ciphertext, tag)
  on dec(ciphertext : C, tag : T) → Option M
    valid ← auth.verify(ciphertext, tag)
    if valid
      message ← cipher.dec(ciphertext)
      return message
    else
      return none

-- `M`, `C`, `T` give the three finite alphabets of the existing interfaces.
variable {M C T : Type} [Fintype M] [Fintype C] [Fintype T]

/-- The first encryption query requests the ciphertext of `m`. -/
lemma encryptThenMAC.enc_query_eq
    -- `s` is the converter state; `m` is the message to encrypt.
    (s : Option Unit) (m : M) :
    encryptThenMAC.body M C T s .enc m [] = .inr ⟨.inl .enc, m⟩ := by
  cases s <;> rfl

/-- The second encryption query authenticates the ciphertext just returned. -/
lemma encryptThenMAC.enc_tag_query_eq
    -- `s` is the converter state; `c` is the reply to encryption of `m`.
    (s : Option Unit) (m : M) (c : C) :
    encryptThenMAC.body M C T s .enc m [(⟨.inl .enc, m⟩, ⟨.inl .enc, c⟩)] =
      .inr ⟨.inr .tag, c⟩ := by
  cases s <;> simp only [encryptThenMAC.body, callProg, ↓reduceDIte]

/-- The first decryption query verifies the supplied ciphertext and tag. -/
lemma encryptThenMAC.dec_query_eq
    -- `s` is the converter state; `c`, `t` are the submitted ciphertext and tag.
    (s : Option Unit) (c : C) (t : T) :
    encryptThenMAC.body M C T s .dec (c, t) [] = .inr ⟨.inr .verify, (c, t)⟩ := by
  cases s <;> rfl

/-- Accepted verification requests decryption of the same ciphertext. -/
lemma encryptThenMAC.dec_cipher_query_eq
    -- `s` is the converter state; `c`, `t` are the accepted ciphertext and tag.
    (s : Option Unit) (c : C) (t : T) :
    encryptThenMAC.body M C T s .dec (c, t)
      [(⟨.inr .verify, (c, t)⟩, ⟨.inr .verify, true⟩)] = .inr ⟨.inl .dec, c⟩ := by
  cases s <;> simp only [encryptThenMAC.body, callProg, ↓reduceDIte, ↓reduceIte]

/-- Encryption returns `(c, t)` after `cipher.enc(m) = c` and `auth.tag(c) = t`. -/
lemma encryptThenMAC.enc_eq
    -- `s` is the converter's optional unit state; `m`, `c`, `t` are the request and replies.
    (s : Option Unit) (m : M) (c : C) (t : T) :
    encryptThenMAC.body M C T s .enc m
      [(⟨.inl .enc, m⟩, ⟨.inl .enc, c⟩),
       (⟨.inr .tag, c⟩, ⟨.inr .tag, t⟩)] = .inl (some (), (c, t)) := by
  cases s <;> simp only [encryptThenMAC.body, callProg, returnProg, ↓reduceDIte]

/-- Acceptance forwards `c` to decryption and returns its reply, including `none`. -/
lemma encryptThenMAC.dec_eq_true
    -- `s` is the converter state; `c`, `t` are the ciphertext and tag, and `m` the cipher's reply.
    (s : Option Unit) (c : C) (t : T) (m : Option M) :
    encryptThenMAC.body M C T s .dec (c, t)
      [(⟨.inr .verify, (c, t)⟩, ⟨.inr .verify, true⟩),
       (⟨.inl .dec, c⟩, ⟨.inl .dec, m⟩)] = .inl (some (), m) := by
  cases s <;>
    simp only [encryptThenMAC.body, callProg, returnProg, ↓reduceDIte, ↓reduceIte]

/-- Rejection returns `none` after the verification call, with no decryption call. -/
lemma encryptThenMAC.dec_eq_false
    -- `s` is the converter state; `c`, `t` are the rejected ciphertext and tag.
    (s : Option Unit) (c : C) (t : T) :
    encryptThenMAC.body M C T s .dec (c, t)
      [(⟨.inr .verify, (c, t)⟩, ⟨.inr .verify, false⟩)] = .inl (some (), none) := by
  cases s <;> simp only [encryptThenMAC.body, callProg, returnProg, ↓reduceDIte,
    Bool.false_eq_true, ↓reduceIte]

-- `K` and `L` carry the independently retained encryption and authentication keys.
variable {K L : Type} [Fintype K] [Fintype L]
  [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq C]

/-- On `AE M (C × T) q`, independently retain `ke ∼ scheme.gen` and `km ∼ mac.gen`.
`enc(m)` replies `(c, t)`, with fresh `c ∼ scheme.enc ke m` and `t ∼ mac.tag km c`.
`dec(c, t)` replies `scheme.dec ke c` if `mac.verify km c t = true`, otherwise `none`. -/
def encryptThenMAC.system
    -- `scheme` supplies encryption/decryption; `mac` authenticates complete ciphertexts in `C`.
    (scheme : SymmetricEncryption K M C) (mac : MAC L C T)
    -- `q` is the total outside query budget; each component receives budget `2 * q`.
    (q : ℕ) : TypedSystem (AE M (C × T) q) :=
  encryptThenMAC M C T • (AE.system scheme ∥ MAC.system mac)

/-- Expose the declared converter attachment to the two independent retained-key components.
`cc_normalize` unfolds this one name and keeps the component systems and converter as atoms.
Apply equations about the whole named system before exposing its assembly. -/
@[cc_normalization]
lemma encryptThenMAC.system_eq
    -- `scheme`, `mac` are the components; `q` bounds the outside queries.
    (scheme : SymmetricEncryption K M C) (mac : MAC L C T) (q : ℕ) :
    encryptThenMAC.system scheme mac q =
      encryptThenMAC M C T • (AE.system scheme ∥ MAC.system mac) := rfl

end

end Commons
