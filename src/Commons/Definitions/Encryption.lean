module

public import ConstructiveCryptography.DSL
public import ConstructiveCryptography.Notation

/-!
# Symmetric encryption

A symmetric-key encryption scheme `Π = (Gen, Enc, Dec)` [1, Definition 2.3.3, p. 18]
supplies a key law, probabilistic encryption, and deterministic decryption. The message type
`M` represents one length. `Encryption.system` retains one `k ← scheme.gen` and answers each
message with a fresh ciphertext. `SymmetricEncryption.encryptions` supplies an independent
table draw per encryption; the selected key/message entry has law `scheme.enc k m`.

`Encryption.INDCPA.systems` is `(X, ρ^cpa • X)` for `X = Encryption.system.perPort scheme`.
The converter `ρ^cpa` encrypts a uniform message in `M` in place of the requested message
[1, Definition 2.3.4, p. 20].
`Encryption.LORCPA.systems` instead encrypts the left or right member of each queried pair
[2, Attack Game 5.2, pp. 181–182]. Both use the same scheme oracle as their component.

The system pairs implement the substitution convention of [1, §2.3.1, p. 14]. Their security
predicates bound the advantage of each typed distinguisher selected by the
`AdmissibleDistinguishers` instance in scope, with the supplied `error d` and no closure assumed.

## Main definitions

* `SymmetricEncryption K M C`: a symmetric-key encryption scheme `Π = (Gen, Enc, Dec)`
* `Encryption M C`: the encryption interface
* `Encryption.system scheme`: `E_k` for `k ← Gen`
* `Encryption.CPA`: the transformation `ρ^cpa`, written so with `open Commons`
* `Encryption.INDCPA.systems scheme q`: the systems `(E_k, ρ^cpa(E_k))` of ind-cpa
* `Encryption.INDCPA scheme error`: ind-cpa for the admitted distinguishers,
  within `error`
* `LeftRight M C`, `Encryption.Left`, `Encryption.Right`: the interface of message pairs, and
  the encryption of the left and of the right message
* `Encryption.LORCPA.systems scheme q`, `Encryption.LORCPA scheme error`:
  left-or-right CPA

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A symmetric-key encryption scheme** `Π = (Gen, Enc, Dec)` [1, Definition 2.3.3, p. 18]: a
distribution over keys, a probabilistic encryption function and a deterministic decryption
function (`none` is `⊥`). -/
structure SymmetricEncryption
    -- `K` carries keys, `M` fixed-length messages, and `C` ciphertexts.
    (K M C : Type) where
  /-- Key generation `Gen`, the “distribution over K” of [1, Definition 2.3.3, p. 18]. -/
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

-- `K`, `M`, `C` carry keys, fixed-length messages and ciphertexts.
variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]

/-- The table law `encryptions scheme f = ∏ km, scheme.enc km.1 km.2 (f km)`: independent
ciphertexts for every key/message pair. -/
def SymmetricEncryption.encryptions [DecidableEq K] [DecidableEq M]
    (scheme : SymmetricEncryption K M C) : Distribution.ProbDist (K × M → C) :=
  Distribution.ProbDist.pi fun km => scheme.enc km.1 km.2

-- Retain `k ← scheme.gen`; each `enc(m)` returns a fresh `c ← scheme.enc k m`
-- [1, §2.3.4, p. 18]. The interface admits the selected total or per-port query budget.
system Encryption.system
    -- `scheme.gen` supplies the retained key; `scheme.enc` supplies each fresh ciphertext.
    (scheme : SymmetricEncryption K M C)
    [DecidableEq K] [DecidableEq M] : Encryption M C
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

/-- The random-message transformation `ρ^cpa` of [1, §2.3.4, p. 18]. -/
scoped notation "ρ^cpa" => Encryption.CPA.perPort _ _

/-- **The systems of ind-cpa** [1, Definition 2.3.4, p. 20]: `E_k` and `ρ^cpa(E_k)`, for `k ← Gen`,
at the budget `q` per port. -/
def Encryption.INDCPA.systems [DecidableEq K] [DecidableEq M] [Nonempty M]
    (scheme : SymmetricEncryption K M C) (q : Encryption.Port → ℕ) :
    TypedSystem (Encryption.perPort M C q) × TypedSystem (Encryption.perPort M C q) :=
  (Encryption.system.perPort scheme, Encryption.CPA.perPort M C • Encryption.system.perPort scheme)

/-- **ind-cpa** within `error`: against the admitted distinguishers, `E_k` substitutes for
`ρ^cpa(E_k)`. -/
def Encryption.INDCPA
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq K] [DecidableEq M] [Nonempty M] (scheme : SymmetricEncryption K M C)
    {q : Encryption.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (Encryption.perPort M C q)) → ENNReal) :
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

/-- **The systems of left-or-right CPA** [2, Attack Game 5.2, pp. 181–182]: `E_k` on the left
message of each pair, and on the right one, for `k ← Gen`, at the budget `q`. -/
def Encryption.LORCPA.systems [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C)
    (q : ℕ) : TypedSystem (LeftRight M C q) × TypedSystem (LeftRight M C q) :=
  (Encryption.Left M C • Encryption.system scheme, Encryption.Right M C • Encryption.system scheme)

/-- **Left-or-right CPA** within `error`: against the admitted distinguishers, encrypting the left
messages substitutes for encrypting the right ones. -/
def Encryption.LORCPA
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C) {q : ℕ}
    -- `q` is the query budget; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (LeftRight M C q)) → ENNReal) : Prop :=
  (Encryption.LORCPA.systems scheme q).1 ≃[error] (Encryption.LORCPA.systems scheme q).2

end

end Commons
