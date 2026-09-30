import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation

/-!
# Symmetric encryption

Banfi, §2.3.4 (printed pp. 18–20). A symmetric-key encryption scheme `Π = (Gen, Enc, Dec)`
(Definition 2.3.3), its encryption oracle `E_k` for `k ← Gen`, and security against
chosen-plaintext attacks in the real-or-random form: `E_k` substitutes for `ρ^cpa(E_k)`, which
encrypts a random message in place of each input (Definition 2.3.4). The message space `M` has
one length, so a random message of the length of `m` is a uniform element of `M`.

Encryption is a probabilistic function: each encryption samples, from the closed law
`SymmetricEncryption.encryptions`, a ciphertext for every key and message, and returns the one
of the current key and message.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

The left-or-right form (Boneh–Shoup, Attack Game 5.2) takes a pair `(m_L, m_R)` per query and
encrypts `m_L` in one system and `m_R` in the other, both transformations of `E_k`.

## Main definitions

* `SymmetricEncryption K M C`: a symmetric-key encryption scheme `Π = (Gen, Enc, Dec)`
* `Encryption M C`: the encryption interface
* `Encryption.Real scheme`: `E_k` for `k ← Gen`
* `Encryption.CPA`: the transformation `ρ^cpa`
* `Encryption.INDCPA.systems scheme q`: the systems `(E_k, ρ^cpa(E_k))` of ind-cpa
* `Encryption.INDCPA scheme error`: ind-cpa for the admitted distinguishers,
  within `error`
* `LeftRight M C`, `Encryption.Left`, `Encryption.Right`: the interface of message pairs, and
  the encryption of the left and of the right message
* `Encryption.LORCPA.systems scheme q`, `Encryption.LORCPA scheme error`:
  left-or-right CPA
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A symmetric-key encryption scheme** `Π = (Gen, Enc, Dec)` (Banfi, Definition 2.3.3): a
distribution over keys, a probabilistic encryption function and a deterministic decryption
function (`none` is `⊥`). -/
structure SymmetricEncryption (K M C : Type) where
  /-- Key generation `Gen`. -/
  gen : Distribution.ProbDist K
  /-- Encryption `Enc`. -/
  enc : K → M → Distribution.ProbDist C
  /-- Decryption `Dec`. -/
  dec : K → C → Option M

interface Encryption(M C : Type) [Fintype M] [Fintype C]
  enc(message : M) → C

interface LeftRight(M C : Type) [Fintype M] [Fintype C]
  enc(left : M, right : M) → C

noncomputable section

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]

/-- Independent encryptions of every message under every key. -/
def SymmetricEncryption.encryptions [DecidableEq K] [DecidableEq M]
    (scheme : SymmetricEncryption K M C) : Distribution.ProbDist (K × M → C) :=
  ⟨Distribution.pi fun km => (scheme.enc km.1 km.2).1,
    Distribution.pi_isProbDist fun km => (scheme.enc km.1 km.2).2⟩

-- `E_k` for `k ← Gen`: on `m`, output `c ← Enc_k(m)`.
system Encryption.Real(scheme : SymmetricEncryption K M C) [DecidableEq K] [DecidableEq M] : Encryption M C
  initialize
    key ←$ scheme.gen
  on enc(message : M) → C
    encryptions ←$ scheme.encryptions
    return encryptions (key, message)

-- `ρ^cpa`: encrypt a random message `m̃` instead of `m`.
converter Encryption.CPA(M C : Type) [Fintype M] [Fintype C] [Nonempty M] : Encryption M C
  inside encryption : Encryption M C
  on enc(_message : M) → C
    replacement ←$ 𝒰[M]
    ciphertext ← encryption.enc(replacement)
    return ciphertext

/-- **The systems of ind-cpa** (Banfi, Definition 2.3.4): `E_k` and `ρ^cpa(E_k)`, for `k ← Gen`,
at the budget `q` per port. -/
def Encryption.INDCPA.systems [DecidableEq K] [DecidableEq M] [Nonempty M]
    (scheme : SymmetricEncryption K M C) (q : Encryption.Port → ℕ) :
    Interface.Resource (Encryption.perPort M C q) × Interface.Resource (Encryption.perPort M C q) :=
  (Encryption.Real.perPort scheme, Encryption.CPA.perPort M C • Encryption.Real.perPort scheme)

/-- **ind-cpa** within `error`: against the admitted distinguishers, `E_k` substitutes for
`ρ^cpa(E_k)`. -/
def Encryption.INDCPA [Interface.AdmissibleDistinguishers]
    [DecidableEq K] [DecidableEq M] [Nonempty M] (scheme : SymmetricEncryption K M C)
    {q : Encryption.Port → ℕ} (error : (Encryption.perPort M C q).inputDomain.Distinguisher → ENNReal) :
    Prop :=
  (Encryption.INDCPA.systems scheme q).1 ≃[error] (Encryption.INDCPA.systems scheme q).2

-- On `(m_L, m_R)`, encrypt `m_L`.
converter Encryption.Left(M C : Type) [Fintype M] [Fintype C] : LeftRight M C
  inside encryption : Encryption M C
  on enc(left : M, _right : M) → C
    ciphertext ← encryption.enc(left)
    return ciphertext

-- On `(m_L, m_R)`, encrypt `m_R`.
converter Encryption.Right(M C : Type) [Fintype M] [Fintype C] : LeftRight M C
  inside encryption : Encryption M C
  on enc(_left : M, right : M) → C
    ciphertext ← encryption.enc(right)
    return ciphertext

/-- **The systems of left-or-right CPA** (Boneh–Shoup, Attack Game 5.2): `E_k` on the left
message of each pair, and on the right one, for `k ← Gen`, at the budget `q`. -/
def Encryption.LORCPA.systems [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C)
    (q : ℕ) : Interface.Resource (LeftRight M C q) × Interface.Resource (LeftRight M C q) :=
  (Encryption.Left M C • Encryption.Real scheme, Encryption.Right M C • Encryption.Real scheme)

/-- **Left-or-right CPA** within `error`: against the admitted distinguishers, encrypting the left
messages substitutes for encrypting the right ones. -/
def Encryption.LORCPA [Interface.AdmissibleDistinguishers]
    [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C) {q : ℕ}
    (error : (LeftRight M C q).inputDomain.Distinguisher → ENNReal) : Prop :=
  (Encryption.LORCPA.systems scheme q).1 ≃[error] (Encryption.LORCPA.systems scheme q).2

end

end Commons
