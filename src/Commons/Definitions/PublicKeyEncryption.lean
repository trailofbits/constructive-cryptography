module

public import ConstructiveCryptography.DSL
public import ConstructiveCryptography.Notation

/-!
# Public-key encryption

`PublicKeyEncryption` supplies key generation, probabilistic encryption, and deterministic
decryption with rejection [2, Definition 11.1, p. 436]. `PKE.system` retains one key pair,
publishes its public key, and offers encryption and decryption at that pair.
`PublicKeyEncryption.encryptions` draws independent ciphertexts for all public-key/message
pairs on each encryption call; selecting the current entry gives `scheme.enc pk m`.

`PKE.INDCCA.systems` is `(X, PKE.CCA.perPort PK M C • X)` for `X = PKE.system.perPort scheme`,
using the random-message substitution of [1, Definition 2.3.5, p. 20] with public-key publication.
`PKE.CCA` encrypts a uniform message in the fixed-length type `M`
and records the requested message; on a recorded ciphertext it returns that message.
This is the library's substitution presentation of chosen-ciphertext security; the
left-or-right attack game is stated in [2, Attack Game 12.1, pp. 467–468]. `PKE.INDCPA.systems`
sets the decryption budget to zero [2, Attack Game 11.2, p. 439].

The security predicates bound the advantage of each typed distinguisher selected by
`AdmissibleDistinguishers` by the supplied `error d`, using the system-pair convention of
[1, §2.3.1, p. 14]. No closure of the selected tests is assumed.

## Main definitions

* `PublicKeyEncryption PK SK M C`: the syntax
* `PKE PK M C`: the interface of the public key, encryption and decryption
* `PKE.system scheme`: the public key, `E_pk` and `D_sk` for `(pk, sk) ← G`
* `PKE.CCA`: the random-message transformation
* `PKE.INDCCA.systems scheme q`: the systems of IND-CCA
* `PKE.INDCCA scheme error`: IND-CCA for the admitted distinguishers, within `error`
* `PKE.INDCPA.systems scheme q`, `PKE.INDCPA scheme error`: IND-CPA

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A public-key encryption scheme** `(G, E, D)` [2, Definition 11.1, p. 436] with public keys
`PK`, secret keys `SK`, messages `M` and ciphertexts `C`. -/
structure PublicKeyEncryption
    -- `PK`, `SK` carry public and secret keys; `M`, `C` carry messages and ciphertexts.
    (PK SK M C : Type) where
  /-- The “key generation algorithm” of [2, Definition 11.1, p. 436], as a pair law. -/
  gen : Distribution.ProbDist (PK × SK)
  /-- Encryption `E`. -/
  enc : PK → M → Distribution.ProbDist C
  /-- Decryption `D`; `none` is rejection. -/
  dec : SK → C → Option M

interface PKE(PK M C : Type) [Fintype PK] [Fintype M] [Fintype C]
  publicKey() → PK
  enc(message : M) → C
  dec(ciphertext : C) → Option M

noncomputable section

-- `PK`, `SK` carry public and secret keys; `M`, `C` carry messages and ciphertexts.
variable {PK SK M C : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype C]

/-- The table law `encryptions scheme f = ∏ pm, scheme.enc pm.1 pm.2 (f pm)`: independent
ciphertexts for every public-key/message pair. -/
def PublicKeyEncryption.encryptions [DecidableEq PK] [DecidableEq M]
    (scheme : PublicKeyEncryption PK SK M C) : Distribution.ProbDist (PK × M → C) :=
  Distribution.ProbDist.pi fun pm => scheme.enc pm.1 pm.2

-- Retain `(pk, sk) ← scheme.gen` and publish `pk` [2, Definition 11.1, p. 436].
-- Each `enc(m)` draws a fresh `scheme.enc pk m`; `dec(c)` returns `scheme.dec sk c`.
-- The interface admits the selected total or per-port query budget.
system PKE.system
    -- `scheme` supplies the key-pair law and encryption and decryption operations.
    (scheme : PublicKeyEncryption PK SK M C)
    [DecidableEq PK] [DecidableEq M] : PKE PK M C
  initialize
    keys ←$ scheme.gen
  on publicKey() → PK
    return keys.1
  on enc(message : M) → C
    encryptions ←$ scheme.encryptions
    return encryptions (keys.1, message)
  on dec(ciphertext : C) → Option M
    return scheme.dec keys.2 ciphertext

-- Encrypt a random message `m̃` instead of `m` and record `(c, m)`; on `c`, output its first
-- recorded message, otherwise forward `c`.
converter PKE.CCA(PK M C : Type)
    [Fintype PK] [Fintype M] [Fintype C] [DecidableEq C] [Nonempty M] : PKE PK M C
  inside pke : PKE PK M C
  initialize
    table ← ([] : List (C × M))
  on publicKey() → PK
    pk ← pke.publicKey()
    return pk
  on enc(message : M) → C
    replacement ←$ 𝒰[M]
    ciphertext ← pke.enc(replacement)
    table ← table ++ [(ciphertext, message)]
    return ciphertext
  on dec(ciphertext : C) → Option M
    match table.lookup ciphertext
    | some message →
      return some message
    | none →
      result ← pke.dec(ciphertext)
      return result

/-- **The systems of IND-CCA**: the real system and its random-message transformation, for
`(pk, sk) ← G`, at the budget `q` per port. -/
def PKE.INDCCA.systems [DecidableEq PK] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : PublicKeyEncryption PK SK M C) (q : PKE.Port → ℕ) :
    TypedSystem (PKE.perPort PK M C q) × TypedSystem (PKE.perPort PK M C q) :=
  (PKE.system.perPort scheme, PKE.CCA.perPort PK M C • PKE.system.perPort scheme)

/-- **IND-CCA** within `error`: against the admitted distinguishers, the real system substitutes
for its random-message transformation. -/
def PKE.INDCCA [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq PK] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : PublicKeyEncryption PK SK M C) {q : PKE.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (PKE.perPort PK M C q)) → ENNReal) : Prop :=
  (PKE.INDCCA.systems scheme q).1 ≃[error] (PKE.INDCCA.systems scheme q).2

/-- **The systems of IND-CPA** [2, Attack Game 11.2, p. 439], in real-or-random form:
those of IND-CCA without decryption queries, at budget `q` per port with none at `dec`. -/
def PKE.INDCPA.systems [DecidableEq PK] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : PublicKeyEncryption PK SK M C) (q : PKE.Port → ℕ) :
    TypedSystem (PKE.perPort PK M C (Function.update q .dec 0)) ×
      TypedSystem (PKE.perPort PK M C (Function.update q .dec 0)) :=
  PKE.INDCCA.systems scheme (Function.update q .dec 0)

/-- **IND-CPA** within `error`: against the admitted distinguishers, the real system without
decryption queries substitutes for its random-message transformation. -/
def PKE.INDCPA [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq PK] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : PublicKeyEncryption PK SK M C) {q : PKE.Port → ℕ}
    -- `q` is the query budget per port, with no decryption queries; `error d` bounds the
    -- advantage of each admitted `d`.
    (error : (TypedDistinguisher (PKE.perPort PK M C (Function.update q .dec 0))) →
      ENNReal) :
    Prop :=
  (PKE.INDCPA.systems scheme q).1 ≃[error] (PKE.INDCPA.systems scheme q).2

end

end Commons
