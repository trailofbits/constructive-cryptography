import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation

/-!
# Public-key encryption

A public-key encryption scheme `(G, E, D)`: key generation, probabilistic encryption under the
public key, and decryption with the secret key, which may reject (Boneh–Shoup, Definition 11.1).

Security against chosen-ciphertext attacks (Boneh–Shoup, Definition 12.1) in the real-or-random
form of Banfi's ind-cca (Definition 2.3.5, printed p. 20), with the public key published: the
system of the public key, `E_pk` and `D_sk` substitutes for its transformation that encrypts a
random message in place of each input and records it, and decrypts a recorded ciphertext to its
original message. The message space `M` has one length, so a random message is a uniform element
of `M`. Encryption samples, from the closed law `PublicKeyEncryption.encryptions`, a ciphertext
for every public key and message, and returns the one of the current key and message.

IND-CPA is IND-CCA without decryption queries: its systems are those of IND-CCA at a budget with
no queries at `dec`.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

## Main definitions

* `PublicKeyEncryption PK SK M C`: the syntax
* `PKE PK M C`: the interface of the public key, encryption and decryption
* `PKE.Real scheme`: the public key, `E_pk` and `D_sk` for `(pk, sk) ← G`
* `PKE.CCA`: the random-message transformation
* `PKE.INDCCA.systems scheme q`: the systems of IND-CCA
* `PKE.INDCCA scheme error`: IND-CCA for the admitted distinguishers, within `error`
* `PKE.INDCPA.systems scheme q`, `PKE.INDCPA scheme error`: IND-CPA
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A public-key encryption scheme** `(G, E, D)` (Boneh–Shoup, Definition 11.1) with public keys
`PK`, secret keys `SK`, messages `M` and ciphertexts `C`. -/
structure PublicKeyEncryption (PK SK M C : Type) where
  /-- Key generation `G`. -/
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

variable {PK SK M C : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype C]

/-- Independent encryptions of every message under every public key. -/
def PublicKeyEncryption.encryptions [DecidableEq PK] [DecidableEq M]
    (scheme : PublicKeyEncryption PK SK M C) : Distribution.ProbDist (PK × M → C) :=
  ⟨Distribution.pi fun pm => (scheme.enc pm.1 pm.2).1,
    Distribution.pi_isProbDist fun pm => (scheme.enc pm.1 pm.2).2⟩

-- The public key, `E_pk` and `D_sk` for `(pk, sk) ← G`: on `m`, output `c ← E(pk, m)`; on `c`,
-- output `D(sk, c)`.
system PKE.Real(scheme : PublicKeyEncryption PK SK M C) [DecidableEq PK] [DecidableEq M] : PKE PK M C
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
converter PKE.CCA(PK M C : Type) [Fintype PK] [Fintype M] [Fintype C] [DecidableEq C] [Nonempty M] : PKE PK M C
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
    Interface.Resource (PKE.perPort PK M C q) × Interface.Resource (PKE.perPort PK M C q) :=
  (PKE.Real.perPort scheme, PKE.CCA.perPort PK M C • PKE.Real.perPort scheme)

/-- **IND-CCA** within `error`: against the admitted distinguishers, the real system substitutes
for its random-message transformation. -/
def PKE.INDCCA [Interface.AdmissibleDistinguishers]
    [DecidableEq PK] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : PublicKeyEncryption PK SK M C) {q : PKE.Port → ℕ}
    (error : (PKE.perPort PK M C q).inputDomain.Distinguisher → ENNReal) : Prop :=
  (PKE.INDCCA.systems scheme q).1 ≃[error] (PKE.INDCCA.systems scheme q).2

/-- **The systems of IND-CPA** (Boneh–Shoup, Attack Game 11.2, in real-or-random form): those of
IND-CCA without decryption queries, at the budget `q` per port with none at `dec`. -/
def PKE.INDCPA.systems [DecidableEq PK] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : PublicKeyEncryption PK SK M C) (q : PKE.Port → ℕ) :
    Interface.Resource (PKE.perPort PK M C (Function.update q .dec 0)) ×
      Interface.Resource (PKE.perPort PK M C (Function.update q .dec 0)) :=
  PKE.INDCCA.systems scheme (Function.update q .dec 0)

/-- **IND-CPA** within `error`: against the admitted distinguishers, the real system without
decryption queries substitutes for its random-message transformation. -/
def PKE.INDCPA [Interface.AdmissibleDistinguishers]
    [DecidableEq PK] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : PublicKeyEncryption PK SK M C) {q : PKE.Port → ℕ}
    (error : (PKE.perPort PK M C (Function.update q .dec 0)).inputDomain.Distinguisher → ENNReal) :
    Prop :=
  (PKE.INDCPA.systems scheme q).1 ≃[error] (PKE.INDCPA.systems scheme q).2

end

end Commons
