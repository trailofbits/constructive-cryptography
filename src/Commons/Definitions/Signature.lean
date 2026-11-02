module

public import ConstructiveCryptography.DSL
public import ConstructiveCryptography.Notation

/-!
# Digital signature schemes

`SignatureScheme` supplies key generation, probabilistic signing, and deterministic
verification [2, Definition 13.1, pp. 528–529]. `SignatureScheme.Correct` states that supported
signatures verify. `SignatureScheme.system` retains one key pair, publishes its public key,
and offers signing and verification. Each signing call draws a fresh table from
`SignatureScheme.signatures` and selects the current secret-key/message entry.

`SignatureScheme.EUF` accepts only valid signatures on previously signed messages;
`SignatureScheme.SUF` accepts only valid previously issued pairs. Both use `List.insert` and
`List.contains`; `List.mem_insert_iff` gives the membership update, and `List.insert_of_mem`
makes repeated recording inert.
`SignatureScheme.EUFCMA.systems` and `SignatureScheme.SUFCMA.systems` compare the scheme oracle
with these restrictions, adapting the integrity
substitutions of [1, Definitions 2.3.6–2.3.7, p. 21]. They adapt the new-message and new-pair
conditions of [2, Attack Games 13.1–13.2, pp. 529–530], testing freshness at each verification
query against the earlier signing queries.

The security predicates bound each typed distinguisher's advantage by `error d`, following
[1, §2.3.1, p. 14]. `AdmissibleDistinguishers` selects the tests, with no closure assumed.

## Main definitions

* `SignatureScheme PK SK M Sig`: the syntax
* `SignatureScheme.Correct`: correctness
* `Signing PK M Sig`: the interface of the public key, signing and verification
* `SignatureScheme.system scheme`: the public key, `S_sk` and `V_pk` for `(pk, sk) ← G`
* `SignatureScheme.EUF`, `SignatureScheme.SUF`: verification restricted to the signed messages,
  and to the signed pairs
* `SignatureScheme.EUFCMA.systems`, `SignatureScheme.SUFCMA.systems`: the systems of EUF-CMA and
  SUF-CMA
* `SignatureScheme.EUFCMA`, `SignatureScheme.SUFCMA`: these notions for the distinguisher
  advantage, within an error

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A signature scheme** with public keys `PK`, secret keys `SK`, messages `M` and signatures
`Sig`. -/
structure SignatureScheme
    -- `PK`, `SK` carry verification and signing keys; `M` messages; `Sig` signatures.
    (PK SK M Sig : Type) where
  /-- Key generation `G`. -/
  gen : Distribution.ProbDist (PK × SK)
  /-- The “signing algorithm” of [2, Definition 13.1, p. 528], as a law on signatures. -/
  sign : SK → M → Distribution.ProbDist Sig
  /-- Verification `V`. -/
  verify : PK → M → Sig → Bool

/-- **Correctness**: for every generated key pair, every signature of a message verifies. -/
def SignatureScheme.Correct {PK SK M Sig : Type} (scheme : SignatureScheme PK SK M Sig) : Prop :=
  ∀ pk sk, (pk, sk) ∈ scheme.gen.1.support → ∀ m σ, σ ∈ (scheme.sign sk m).1.support →
    scheme.verify pk m σ = true

interface Signing(PK M Sig : Type) [Fintype PK] [Fintype M] [Fintype Sig]
  publicKey() → PK
  sign(message : M) → Sig
  verify(message : M, signature : Sig) → Bool

noncomputable section

-- `PK`, `SK` carry verification and signing keys; `M` messages; `Sig` signatures.
variable {PK SK M Sig : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype Sig]

/-- The table law `signatures scheme f = ∏ km, scheme.sign km.1 km.2 (f km)`: independent
signatures for every secret-key/message pair. -/
def SignatureScheme.signatures [DecidableEq SK] [DecidableEq M]
    (scheme : SignatureScheme PK SK M Sig) : Distribution.ProbDist (SK × M → Sig) :=
  Distribution.ProbDist.pi fun km => scheme.sign km.1 km.2

-- Retain `(pk, sk) ← scheme.gen` and publish `pk` [2, Definition 13.1, pp. 528–529].
-- Each `sign(m)` draws a fresh `scheme.sign sk m`; `verify(m, σ)` returns `scheme.verify pk m σ`.
-- The interface admits the selected total or per-port query budget.
system SignatureScheme.system
    -- `scheme` supplies the key-pair law and signing and verification operations.
    (scheme : SignatureScheme PK SK M Sig)
    [DecidableEq SK] [DecidableEq M] : Signing PK M Sig
  initialize
    keys ←$ scheme.gen
  on publicKey() → PK
    return keys.1
  on sign(message : M) → Sig
    signatures ←$ scheme.signatures
    return signatures (keys.2, message)
  on verify(message : M, signature : Sig) → Bool
    return scheme.verify keys.1 message signature

-- Retain requested messages in `signed`; verification returns `valid && signed.contains message`.
-- Insert the message before requesting its signature. The condition "m is new" in
-- [2, Attack Game 13.1, p. 530] is tested against the messages requested so far.
converter SignatureScheme.EUF(PK M Sig : Type)
    [Fintype PK] [Fintype M] [Fintype Sig] [DecidableEq M] : Signing PK M Sig
  inside signing : Signing PK M Sig
  initialize
    signed ← ([] : List M)
  on publicKey() → PK
    pk ← signing.publicKey()
    return pk
  on sign(message : M) → Sig
    signed ← signed.insert message
    signature ← signing.sign(message)
    return signature
  on verify(message : M, signature : Sig) → Bool
    valid ← signing.verify(message, signature)
    return valid && signed.contains message

-- Retain returned pairs in `signed`; verification returns
-- `valid && signed.contains (message, signature)`.
-- Insert the pair after receiving the signature. The condition "(m, σ) is new" in
-- [2, Attack Game 13.2, p. 530] is tested against the pairs returned so far.
converter SignatureScheme.SUF(PK M Sig : Type)
    [Fintype PK] [Fintype M] [Fintype Sig] [DecidableEq M] [DecidableEq Sig] : Signing PK M Sig
  inside signing : Signing PK M Sig
  initialize
    signed ← ([] : List (M × Sig))
  on publicKey() → PK
    pk ← signing.publicKey()
    return pk
  on sign(message : M) → Sig
    signature ← signing.sign(message)
    signed ← signed.insert (message, signature)
    return signature
  on verify(message : M, signature : Sig) → Bool
    valid ← signing.verify(message, signature)
    return valid && signed.contains (message, signature)

/-- **The systems of EUF-CMA**: the real system and the one whose verification accepts only
signatures on signed messages, for `(pk, sk) ← G`, at the budget `q` per port. -/
def SignatureScheme.EUFCMA.systems [DecidableEq SK] [DecidableEq M]
    (scheme : SignatureScheme PK SK M Sig) (q : Signing.Port → ℕ) :
    TypedSystem (Signing.perPort PK M Sig q) ×
      TypedSystem (Signing.perPort PK M Sig q) :=
  (SignatureScheme.system.perPort scheme,
    SignatureScheme.EUF.perPort PK M Sig • SignatureScheme.system.perPort scheme)

/-- **The systems of SUF-CMA**: the real system and the one whose verification accepts only signed
pairs, for `(pk, sk) ← G`, at the budget `q` per port. -/
def SignatureScheme.SUFCMA.systems [DecidableEq SK] [DecidableEq M] [DecidableEq Sig]
    (scheme : SignatureScheme PK SK M Sig) (q : Signing.Port → ℕ) :
    TypedSystem (Signing.perPort PK M Sig q) ×
      TypedSystem (Signing.perPort PK M Sig q) :=
  (SignatureScheme.system.perPort scheme,
    SignatureScheme.SUF.perPort PK M Sig • SignatureScheme.system.perPort scheme)

/-- **EUF-CMA** within `error`: against the admitted distinguishers, the real system substitutes
for the one that accepts only signatures on signed messages. -/
def SignatureScheme.EUFCMA
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq SK] [DecidableEq M] (scheme : SignatureScheme PK SK M Sig)
    {q : Signing.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (Signing.perPort PK M Sig q)) → ENNReal) : Prop :=
  (SignatureScheme.EUFCMA.systems scheme q).1 ≃[error] (SignatureScheme.EUFCMA.systems scheme q).2

/-- **SUF-CMA** within `error`: against the admitted distinguishers, the real system substitutes
for the one that accepts only signed pairs. -/
def SignatureScheme.SUFCMA
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq SK] [DecidableEq M] [DecidableEq Sig] (scheme : SignatureScheme PK SK M Sig)
    {q : Signing.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (Signing.perPort PK M Sig q)) → ENNReal) : Prop :=
  (SignatureScheme.SUFCMA.systems scheme q).1 ≃[error] (SignatureScheme.SUFCMA.systems scheme q).2

end

end Commons
