import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation

/-!
# Message authentication codes

A MAC `(G, S, V)`: key generation, tagging of a message, and verification of a tag, both with the
secret key (Boneh–Shoup, Definition 6.1). It is correct when every tag verifies.

Unforgeability under chosen-message attacks, as pairs of systems in the form of Banfi's
int-ptxt and int-ctxt (Definitions 2.3.6–2.3.7, printed p. 21): the system of the tagging and the
verification oracle, against the one whose verification accepts only what verifies and was
issued. Existential unforgeability accepts a tag on a tagged message; strong unforgeability
accepts only a tagged pair, which is the security of Boneh–Shoup (Attack Game 6.2 and
Definition 6.2, with verification queries). A distinguisher tells the two systems apart exactly
when it submits a forgery. Tagging samples, from the closed law `MAC.tags`, a tag under every key
on every message, and returns the one of the current key and message.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

## Main definitions

* `MAC K M T`: the syntax
* `MAC.Correct`: correctness
* `Tagging M T`: the interface of tagging and verification
* `MAC.Real mac`: `S_k` and `V_k` for `k ← G`
* `MAC.EUF`, `MAC.SUF`: verification restricted to the tagged messages, and to the tagged pairs
* `MAC.EUFCMA.systems`, `MAC.SUFCMA.systems`: the systems of EUF-CMA and SUF-CMA
* `MAC.EUFCMA`, `MAC.SUFCMA`: these notions for the admitted distinguishers, within an error
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A MAC** with keys `K`, messages `M` and tags `T` (Boneh–Shoup, Definition 6.1, with a key
distribution). -/
structure MAC (K M T : Type) where
  /-- Key generation `G`. -/
  gen : Distribution.ProbDist K
  /-- Tagging `S`. -/
  tag : K → M → Distribution.ProbDist T
  /-- Verification `V`. -/
  verify : K → M → T → Bool

/-- **Correctness**: for every generated key, every tag of a message verifies. -/
def MAC.Correct {K M T : Type} (mac : MAC K M T) : Prop :=
  ∀ k, k ∈ mac.gen.1.support → ∀ m t, t ∈ (mac.tag k m).1.support → mac.verify k m t = true

interface Tagging(M T : Type) [Fintype M] [Fintype T]
  tag(message : M) → T
  verify(message : M, tag : T) → Bool

noncomputable section

variable {K M T : Type} [Fintype K] [Fintype M] [Fintype T]

/-- Independent tags under every key on every message. -/
def MAC.tags [DecidableEq K] [DecidableEq M] (mac : MAC K M T) :
    Distribution.ProbDist (K × M → T) :=
  ⟨Distribution.pi fun km => (mac.tag km.1 km.2).1,
    Distribution.pi_isProbDist fun km => (mac.tag km.1 km.2).2⟩

-- `S_k` and `V_k` for `k ← G`: on `m`, output `t ← S(k, m)`; on `(m, t)`, output `V(k, m, t)`.
system MAC.Real(mac : MAC K M T) [DecidableEq K] [DecidableEq M] : Tagging M T
  initialize
    key ←$ mac.gen
  on tag(message : M) → T
    tags ←$ mac.tags
    return tags (key, message)
  on verify(message : M, tag : T) → Bool
    return mac.verify key message tag

-- Record each tagged message; accept a tag only if it verifies and its message was tagged.
converter MAC.EUF(M T : Type) [Fintype M] [Fintype T] [DecidableEq M] : Tagging M T
  inside tagging : Tagging M T
  initialize
    tagged ← ([] : List M)
  on tag(message : M) → T
    tagged ← tagged ++ [message]
    t ← tagging.tag(message)
    return t
  on verify(message : M, tag : T) → Bool
    valid ← tagging.verify(message, tag)
    return valid && decide (message ∈ tagged)

-- Record each tagged pair; accept a tag only if it verifies and the pair was tagged.
converter MAC.SUF(M T : Type) [Fintype M] [Fintype T] [DecidableEq M] [DecidableEq T] : Tagging M T
  inside tagging : Tagging M T
  initialize
    tagged ← ([] : List (M × T))
  on tag(message : M) → T
    t ← tagging.tag(message)
    tagged ← tagged ++ [(message, t)]
    return t
  on verify(message : M, tag : T) → Bool
    valid ← tagging.verify(message, tag)
    return valid && decide ((message, tag) ∈ tagged)

/-- **The systems of EUF-CMA**: the real system and the one whose verification accepts only tags
on tagged messages, for `k ← G`, at the budget `q` per port. -/
def MAC.EUFCMA.systems [DecidableEq K] [DecidableEq M] (mac : MAC K M T) (q : Tagging.Port → ℕ) :
    Interface.Resource (Tagging.perPort M T q) × Interface.Resource (Tagging.perPort M T q) :=
  (MAC.Real.perPort mac, MAC.EUF.perPort M T • MAC.Real.perPort mac)

/-- **The systems of SUF-CMA**: the real system and the one whose verification accepts only tagged
pairs, for `k ← G`, at the budget `q` per port. -/
def MAC.SUFCMA.systems [DecidableEq K] [DecidableEq M] [DecidableEq T] (mac : MAC K M T)
    (q : Tagging.Port → ℕ) :
    Interface.Resource (Tagging.perPort M T q) × Interface.Resource (Tagging.perPort M T q) :=
  (MAC.Real.perPort mac, MAC.SUF.perPort M T • MAC.Real.perPort mac)

/-- **EUF-CMA** within `error`: against the admitted distinguishers, the real system substitutes
for the one that accepts only tags on tagged messages. -/
def MAC.EUFCMA [Interface.AdmissibleDistinguishers]
    [DecidableEq K] [DecidableEq M] (mac : MAC K M T) {q : Tagging.Port → ℕ}
    (error : (Tagging.perPort M T q).inputDomain.Distinguisher → ENNReal) : Prop :=
  (MAC.EUFCMA.systems mac q).1 ≃[error] (MAC.EUFCMA.systems mac q).2

/-- **SUF-CMA** within `error`: against the admitted distinguishers, the real system substitutes
for the one that accepts only tagged pairs. -/
def MAC.SUFCMA [Interface.AdmissibleDistinguishers]
    [DecidableEq K] [DecidableEq M] [DecidableEq T] (mac : MAC K M T) {q : Tagging.Port → ℕ}
    (error : (Tagging.perPort M T q).inputDomain.Distinguisher → ENNReal) : Prop :=
  (MAC.SUFCMA.systems mac q).1 ≃[error] (MAC.SUFCMA.systems mac q).2

end

end Commons
