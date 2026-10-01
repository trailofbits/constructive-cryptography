import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation

/-!
# Digital signature schemes

A signature scheme `(G, S, V)`: key generation, signing of a message with the secret key, and
verification of a signature with the public key (Boneh–Shoup, Definition 13.1). It is correct
when every signature verifies.

Unforgeability under chosen-message attacks, as pairs of systems in the form of Banfi's
int-ptxt and int-ctxt (Definitions 2.3.6–2.3.7, printed p. 21): the system of the public key, the
signing oracle and the verification oracle, against the one whose verification accepts only what
verifies and was issued. Existential unforgeability (Boneh–Shoup, Attack Game 13.1) accepts a
signature on a signed message; strong unforgeability (Attack Game 13.2) accepts only a signed
pair. A distinguisher tells the two systems apart exactly when it submits a forgery. Signing
samples, from the closed law `SignatureScheme.signatures`, a signature under every secret key on
every message, and returns the one of the current key and message.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

## Main definitions

* `SignatureScheme PK SK M Sig`: the syntax
* `SignatureScheme.Correct`: correctness
* `Signing PK M Sig`: the interface of the public key, signing and verification
* `SignatureScheme.Real scheme`: the public key, `S_sk` and `V_pk` for `(pk, sk) ← G`
* `SignatureScheme.EUF`, `SignatureScheme.SUF`: verification restricted to the signed messages,
  and to the signed pairs
* `SignatureScheme.EUFCMA.systems`, `SignatureScheme.SUFCMA.systems`: the systems of EUF-CMA and
  SUF-CMA
* `SignatureScheme.EUFCMA`, `SignatureScheme.SUFCMA`: these notions for the distinguisher
  advantage, within an error
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A signature scheme** with public keys `PK`, secret keys `SK`, messages `M` and signatures
`Sig`. -/
structure SignatureScheme (PK SK M Sig : Type) where
  /-- Key generation `G`. -/
  gen : Distribution.ProbDist (PK × SK)
  /-- Signing `S`. -/
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

variable {PK SK M Sig : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype Sig]

/-- Independent signatures under every secret key on every message. -/
def SignatureScheme.signatures [DecidableEq SK] [DecidableEq M]
    (scheme : SignatureScheme PK SK M Sig) : Distribution.ProbDist (SK × M → Sig) :=
  ⟨Distribution.pi fun km => (scheme.sign km.1 km.2).1,
    Distribution.pi_isProbDist fun km => (scheme.sign km.1 km.2).2⟩

-- The public key, `S_sk` and `V_pk` for `(pk, sk) ← G`: on `m`, output `σ ← S(sk, m)`; on
-- `(m, σ)`, output `V(pk, m, σ)`.
system SignatureScheme.Real(scheme : SignatureScheme PK SK M Sig) [DecidableEq SK] [DecidableEq M] : Signing PK M Sig
  initialize
    keys ←$ scheme.gen
  on publicKey() → PK
    return keys.1
  on sign(message : M) → Sig
    signatures ←$ scheme.signatures
    return signatures (keys.2, message)
  on verify(message : M, signature : Sig) → Bool
    return scheme.verify keys.1 message signature

-- Record each signed message; accept a signature only if it verifies and its message was signed.
converter SignatureScheme.EUF(PK M Sig : Type) [Fintype PK] [Fintype M] [Fintype Sig] [DecidableEq M] : Signing PK M Sig
  inside signing : Signing PK M Sig
  initialize
    signed ← ([] : List M)
  on publicKey() → PK
    pk ← signing.publicKey()
    return pk
  on sign(message : M) → Sig
    signed ← signed ++ [message]
    signature ← signing.sign(message)
    return signature
  on verify(message : M, signature : Sig) → Bool
    valid ← signing.verify(message, signature)
    return valid && decide (message ∈ signed)

-- Record each signed pair; accept a signature only if it verifies and the pair was signed.
converter SignatureScheme.SUF(PK M Sig : Type) [Fintype PK] [Fintype M] [Fintype Sig] [DecidableEq M] [DecidableEq Sig] : Signing PK M Sig
  inside signing : Signing PK M Sig
  initialize
    signed ← ([] : List (M × Sig))
  on publicKey() → PK
    pk ← signing.publicKey()
    return pk
  on sign(message : M) → Sig
    signature ← signing.sign(message)
    signed ← signed ++ [(message, signature)]
    return signature
  on verify(message : M, signature : Sig) → Bool
    valid ← signing.verify(message, signature)
    return valid && decide ((message, signature) ∈ signed)

/-- **The systems of EUF-CMA**: the real system and the one whose verification accepts only
signatures on signed messages, for `(pk, sk) ← G`, at the budget `q` per port. -/
def SignatureScheme.EUFCMA.systems [DecidableEq SK] [DecidableEq M]
    (scheme : SignatureScheme PK SK M Sig) (q : Signing.Port → ℕ) :
    Interface.Resource (Signing.perPort PK M Sig q) ×
      Interface.Resource (Signing.perPort PK M Sig q) :=
  (SignatureScheme.Real.perPort scheme,
    SignatureScheme.EUF.perPort PK M Sig • SignatureScheme.Real.perPort scheme)

/-- **The systems of SUF-CMA**: the real system and the one whose verification accepts only signed
pairs, for `(pk, sk) ← G`, at the budget `q` per port. -/
def SignatureScheme.SUFCMA.systems [DecidableEq SK] [DecidableEq M] [DecidableEq Sig]
    (scheme : SignatureScheme PK SK M Sig) (q : Signing.Port → ℕ) :
    Interface.Resource (Signing.perPort PK M Sig q) ×
      Interface.Resource (Signing.perPort PK M Sig q) :=
  (SignatureScheme.Real.perPort scheme,
    SignatureScheme.SUF.perPort PK M Sig • SignatureScheme.Real.perPort scheme)

/-- **EUF-CMA** within `error`: against the admitted distinguishers, the real system substitutes
for the one that accepts only signatures on signed messages. -/
def SignatureScheme.EUFCMA [Interface.AdmissibleDistinguishers]
    [DecidableEq SK] [DecidableEq M] (scheme : SignatureScheme PK SK M Sig)
    {q : Signing.Port → ℕ}
    (error : (Signing.perPort PK M Sig q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (SignatureScheme.EUFCMA.systems scheme q).1 ≃[error] (SignatureScheme.EUFCMA.systems scheme q).2

/-- **SUF-CMA** within `error`: against the admitted distinguishers, the real system substitutes
for the one that accepts only signed pairs. -/
def SignatureScheme.SUFCMA [Interface.AdmissibleDistinguishers]
    [DecidableEq SK] [DecidableEq M] [DecidableEq Sig] (scheme : SignatureScheme PK SK M Sig)
    {q : Signing.Port → ℕ}
    (error : (Signing.perPort PK M Sig q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (SignatureScheme.SUFCMA.systems scheme q).1 ≃[error] (SignatureScheme.SUFCMA.systems scheme q).2

end

end Commons
