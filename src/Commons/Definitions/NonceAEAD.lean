module

public import ConstructiveCryptography.DSL
public import Commons.Definitions.Nonce

/-!
# Nonce and associated-data encryption interface

`AEAD N AD M T` exposes encryption of `(n, ad, m)` to `(c, t)` and decryption of
`(n, ad, c, t)` to a message or `none`. Plaintexts and ciphertext bodies share the carrier `M`;
the complete ciphertext is `(c, t) : M × T`. The interface carries a total query budget.

The nonce-based AD syntax of [1, §9.5, p. 378] requires correct decryption when both operations
receive “the same nonce and associated data”. `AEAD.encryptionNonce` selects only encryption
nonces, so `nonceRestricted (AEAD N AD M T q) AEAD.encryptionNonce` admits repeated decryption
nonces and requires fresh encryption nonces while retaining budget `q`.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL

noncomputable section

-- `N`, `AD`, `M`, `T` carry nonces, associated data, message/ciphertext bodies and tags.
-- Encryption returns `(c, t)`; decryption returns the message or rejection `none`.
interface AEAD(N AD M T : Type) [Fintype N] [Fintype AD] [Fintype M] [Fintype T]
  encrypt(nonce : N, associatedData : AD, message : M) → M × T
  decrypt(nonce : N, associatedData : AD, ciphertext : M, tag : T) → Option M

/-- `encryptionNonce ⟨encrypt, (n, ad, m)⟩ = some n`;
`encryptionNonce ⟨decrypt, x⟩ = none`. -/
def AEAD.encryptionNonce
    -- `N`, `AD`, `M`, `T` are the interface alphabets; `q` is its total query allowance.
    {N AD M T : Type} [Fintype N] [Fintype AD] [Fintype M] [Fintype T] {q : ℕ} :
    (Σ i, (AEAD N AD M T q).X i) → Option N
  | ⟨.encrypt, (n, _, _)⟩ => some n
  | ⟨.decrypt, _⟩ => none

end

end Commons
