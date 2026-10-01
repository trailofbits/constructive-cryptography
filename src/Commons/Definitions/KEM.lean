import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation

/-!
# Key encapsulation mechanisms

A key encapsulation mechanism `(G, E, D)`: key generation, encapsulation of a fresh key under a
public key, and decapsulation of a ciphertext with the secret key, which may reject (Boneh–Shoup,
Chapters 11–12). It is correct when decapsulation recovers every encapsulated key.

Security against chosen-ciphertext attacks in the real-or-random form of Banfi's ind-cca
(Definition 2.3.5, printed p. 20): the system of the public key, the encapsulation oracle and the
decapsulation oracle substitutes for the one in which each encapsulated key is replaced by a
uniform key, and decapsulating a ciphertext it output returns that key. Encapsulation samples,
from the closed law `KEM.encapsulations`, an encapsulation under every public key, and returns
the one under the current key.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

IND-CPA is IND-CCA without decapsulation queries: its systems are those of IND-CCA at a budget
with no queries at `decaps`.

## Main definitions

* `KEM PK SK C K`: the syntax
* `KEM.Correct`: correctness
* `Encapsulation PK C K`: the interface of the public key, encapsulation and decapsulation
* `KEM.Real kem`: the public key, `E_pk` and `D_sk` for `(pk, sk) ← G`
* `KEM.CCA`: the substitution of uniform keys for the encapsulated keys
* `KEM.INDCCA.systems kem q`: the systems of IND-CCA
* `KEM.INDCCA kem error`: IND-CCA for the admitted distinguishers, within `error`
* `KEM.INDCPA.systems kem q`, `KEM.INDCPA kem error`: IND-CPA
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A key encapsulation mechanism** with public keys `PK`, secret keys `SK`, ciphertexts `C` and
keys `K`. -/
structure KEM (PK SK C K : Type) where
  /-- Key generation `G`. -/
  gen : Distribution.ProbDist (PK × SK)
  /-- Encapsulation `E`: a ciphertext and the key it encapsulates. -/
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

variable {PK SK C K : Type} [Fintype PK] [Fintype SK] [Fintype C] [Fintype K]

/-- Independent encapsulations under every public key. -/
def KEM.encapsulations [DecidableEq PK] (kem : KEM PK SK C K) :
    Distribution.ProbDist (PK → C × K) :=
  ⟨Distribution.pi fun pk => (kem.encaps pk).1, Distribution.pi_isProbDist fun pk => (kem.encaps pk).2⟩

-- The public key, `E_pk` and `D_sk` for `(pk, sk) ← G`: on `encaps`, output `(c, k) ← E(pk)`;
-- on `c`, output `D(sk, c)`.
system KEM.Real(kem : KEM PK SK C K) [DecidableEq PK] : Encapsulation PK C K
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
converter KEM.CCA(PK C K : Type) [Fintype PK] [Fintype C] [Fintype K] [DecidableEq C] [Nonempty K] : Encapsulation PK C K
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
    Interface.Resource (Encapsulation.perPort PK C K q) ×
      Interface.Resource (Encapsulation.perPort PK C K q) :=
  (KEM.Real.perPort kem, KEM.CCA.perPort PK C K • KEM.Real.perPort kem)

/-- **IND-CCA** within `error`: against the admitted distinguishers, the real system substitutes
for the one with uniform keys. -/
def KEM.INDCCA [Interface.AdmissibleDistinguishers]
    [DecidableEq PK] [DecidableEq C] [Nonempty K] (kem : KEM PK SK C K)
    {q : Encapsulation.Port → ℕ}
    (error : (Encapsulation.perPort PK C K q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (KEM.INDCCA.systems kem q).1 ≃[error] (KEM.INDCCA.systems kem q).2

/-- **The systems of IND-CPA**: those of IND-CCA without decapsulation queries, at the budget `q`
per port with none at `decaps`. -/
def KEM.INDCPA.systems [DecidableEq PK] [DecidableEq C] [Nonempty K] (kem : KEM PK SK C K)
    (q : Encapsulation.Port → ℕ) :
    Interface.Resource (Encapsulation.perPort PK C K (Function.update q .decaps 0)) ×
      Interface.Resource (Encapsulation.perPort PK C K (Function.update q .decaps 0)) :=
  KEM.INDCCA.systems kem (Function.update q .decaps 0)

/-- **IND-CPA** within `error`: against the admitted distinguishers, the real system without
decapsulation queries substitutes for the one with uniform keys. -/
def KEM.INDCPA [Interface.AdmissibleDistinguishers]
    [DecidableEq PK] [DecidableEq C] [Nonempty K] (kem : KEM PK SK C K)
    {q : Encapsulation.Port → ℕ}
    (error :
      (Encapsulation.perPort PK C K (Function.update q .decaps 0)).inputDomain.DistinguisherBehavior →
        ENNReal) : Prop :=
  (KEM.INDCPA.systems kem q).1 ≃[error] (KEM.INDCPA.systems kem q).2

end

end Commons
