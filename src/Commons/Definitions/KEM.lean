module

public import ConstructiveCryptography.DSL
public import ConstructiveCryptography.Notation

/-!
# Key encapsulation mechanisms

`KEM` supplies key generation, encapsulation, and deterministic decapsulation with rejection
[2, Exercise 11.9, p. 460]. `KEM.Correct` states that supported encapsulations decapsulate to their
keys. `KEM.system` retains a key pair, publishes its public key, and answers encapsulation
with a fresh `(ciphertext, key)` pair. `KEM.encapsulations` samples independent outcomes for
all public keys on each call, and the system selects the current public key's entry.

`KEM.INDCCA.systems` is `(X, KEM.CCA.perPort PK C K • X)` for `X = KEM.system.perPort kem`.
The converter replaces each encapsulated key by an independent uniform key and replays it on
recorded ciphertexts. This adapts the
substitution convention of [1, Definition 2.3.5, p. 20] to the KEM syntax of [2, Exercise 11.9].
`KEM.INDCPA.systems` sets the decapsulation budget to zero.

The security predicates bound each typed distinguisher's advantage by `error d`, following
[1, §2.3.1, p. 14]. `AdmissibleDistinguishers` selects the tests, with no closure assumed.

## Main definitions

* `KEM PK SK C K`: the syntax
* `KEM.Correct`: correctness
* `Encapsulation PK C K`: the interface of the public key, encapsulation and decapsulation
* `KEM.system kem`: the public key, `E_pk` and `D_sk` for `(pk, sk) ← G`
* `KEM.CCA`: the substitution of uniform keys for the encapsulated keys
* `KEM.INDCCA.systems kem q`: the systems of IND-CCA
* `KEM.INDCCA kem error`: IND-CCA for the admitted distinguishers, within `error`
* `KEM.INDCPA.systems kem q`, `KEM.INDCPA kem error`: IND-CPA

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A key encapsulation mechanism** with public keys `PK`, secret keys `SK`, ciphertexts `C` and
keys `K`. -/
structure KEM
    -- `PK`, `SK` carry asymmetric keys; `C` carries ciphertexts; `K` carries encapsulated keys.
    (PK SK C K : Type) where
  /-- The generated public/secret key pair of [2, Exercise 11.9, p. 460]. -/
  gen : Distribution.ProbDist (PK × SK)
  /-- Encapsulation returns the ciphertext and key; [2, Exercise 11.9, p. 460]
  orders this pair as “(k, ckem)”. -/
  encaps : PK → Distribution.ProbDist (C × K)
  /-- Decapsulation `D`; `none` is rejection. -/
  decaps : SK → C → Option K

/-- **Correctness**: for every generated key pair, decapsulation recovers every encapsulated key. -/
def KEM.Correct {PK SK C K : Type} (kem : KEM PK SK C K) : Prop :=
  ∀ pk sk, (pk, sk) ∈ kem.gen.1.support → ∀ c k, (c, k) ∈ (kem.encaps pk).1.support →
    kem.decaps sk c = some k

interface Encapsulation(PK C K : Type) [Fintype PK] [Fintype C] [Fintype K]
  publicKey() → PK
  encaps() → C × K
  decaps(ciphertext : C) → Option K

noncomputable section

-- `PK`, `SK` carry asymmetric keys; `C` carries ciphertexts; `K` carries encapsulated keys.
variable {PK SK C K : Type} [Fintype PK] [Fintype SK] [Fintype C] [Fintype K]

/-- The table law `encapsulations kem f = ∏ pk, kem.encaps pk (f pk)`: one independent
encapsulation outcome per public key. -/
def KEM.encapsulations [DecidableEq PK] (kem : KEM PK SK C K) :
    Distribution.ProbDist (PK → C × K) :=
  Distribution.ProbDist.pi kem.encaps

-- Retain `(pk, sk) ← kem.gen` and publish `pk` [2, Exercise 11.9, p. 460].
-- Each `encaps()` draws a fresh `(c, k) ← kem.encaps pk`; `decaps(c)` returns `kem.decaps sk c`.
-- The interface admits the selected total or per-port query budget.
system KEM.system
    -- `kem` supplies the key-pair law and encapsulation and decapsulation operations.
    (kem : KEM PK SK C K) [DecidableEq PK] : Encapsulation PK C K
  initialize
    keys ←$ kem.gen
  on publicKey() → PK
    return keys.1
  on encaps() → C × K
    encapsulations ←$ kem.encapsulations
    return encapsulations keys.1
  on decaps(ciphertext : C) → Option K
    return kem.decaps keys.2 ciphertext

-- Replace each encapsulated key by a uniform key `k̃` and record `(c, k̃)`; on `c`, output its
-- first recorded key, otherwise forward `c`.
converter KEM.CCA(PK C K : Type)
    [Fintype PK] [Fintype C] [Fintype K] [DecidableEq C] [Nonempty K] : Encapsulation PK C K
  inside kem : Encapsulation PK C K
  initialize
    table ← ([] : List (C × K))
  on publicKey() → PK
    pk ← kem.publicKey()
    return pk
  on encaps() → C × K
    encapsulation ← kem.encaps()
    key ←$ 𝒰[K]
    table ← table ++ [(encapsulation.1, key)]
    return (encapsulation.1, key)
  on decaps(ciphertext : C) → Option K
    match table.lookup ciphertext
    | some key →
      return some key
    | none →
      result ← kem.decaps(ciphertext)
      return result

/-- **The systems of IND-CCA**: the real system and the one with uniform keys, for
`(pk, sk) ← G`, at the budget `q` per port. -/
def KEM.INDCCA.systems [DecidableEq PK] [DecidableEq C] [Nonempty K] (kem : KEM PK SK C K)
    (q : Encapsulation.Port → ℕ) :
    TypedSystem (Encapsulation.perPort PK C K q) ×
      TypedSystem (Encapsulation.perPort PK C K q) :=
  (KEM.system.perPort kem, KEM.CCA.perPort PK C K • KEM.system.perPort kem)

/-- **IND-CCA** within `error`: against the admitted distinguishers, the real system substitutes
for the one with uniform keys. -/
def KEM.INDCCA [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq PK] [DecidableEq C] [Nonempty K] (kem : KEM PK SK C K)
    {q : Encapsulation.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (Encapsulation.perPort PK C K q)) → ENNReal) : Prop :=
  (KEM.INDCCA.systems kem q).1 ≃[error] (KEM.INDCCA.systems kem q).2

/-- **The systems of IND-CPA**: those of IND-CCA without decapsulation queries, at the budget `q`
per port with none at `decaps`. -/
def KEM.INDCPA.systems [DecidableEq PK] [DecidableEq C] [Nonempty K] (kem : KEM PK SK C K)
    (q : Encapsulation.Port → ℕ) :
    TypedSystem (Encapsulation.perPort PK C K (Function.update q .decaps 0)) ×
      TypedSystem (Encapsulation.perPort PK C K (Function.update q .decaps 0)) :=
  KEM.INDCCA.systems kem (Function.update q .decaps 0)

/-- **IND-CPA** within `error`: against the admitted distinguishers, the real system without
decapsulation queries substitutes for the one with uniform keys. -/
def KEM.INDCPA [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq PK] [DecidableEq C] [Nonempty K] (kem : KEM PK SK C K)
    {q : Encapsulation.Port → ℕ}
    -- `q` is the query budget per port, with no decapsulation queries; `error d` bounds the
    -- advantage of each admitted `d`.
    (error :
      (TypedDistinguisher (Encapsulation.perPort PK C K (Function.update q .decaps 0))) →
        ENNReal) : Prop :=
  (KEM.INDCPA.systems kem q).1 ≃[error] (KEM.INDCPA.systems kem q).2

end

end Commons
