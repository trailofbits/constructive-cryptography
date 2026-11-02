module

public import ConstructiveCryptography.DSL
public import ConstructiveCryptography.Notation

/-!
# Message authentication codes

`MAC` supplies a key law, probabilistic tagging, and deterministic verification
[2, Definition 6.1, p. 217]; `MAC.Correct` states that supported tags verify.
`MAC.system` retains one key shared by the tagging and verification ports. Each tagging call
draws a fresh independent table from `MAC.tags` and selects the current key/message entry.

`MAC.EUF` accepts only valid tags on previously tagged messages; `MAC.SUF` accepts only valid
previously issued pairs. The pairs `MAC.EUFCMA.systems` and `MAC.SUFCMA.systems` compare the
scheme oracle with these restrictions. This uses the substitution presentation of integrity
from [1, Definitions 2.3.6–2.3.7, p. 21]. The strong form's fresh-pair condition corresponds
to [2, Attack Game 6.2, p. 221].

The security predicates bound each typed distinguisher's advantage by `error d`, following
[1, §2.3.1, p. 14]. `AdmissibleDistinguishers` selects the tests, with no closure assumed.

## Main definitions

* `MAC K M T`: the syntax
* `MAC.Correct`: correctness
* `Tagging M T`: the interface of tagging and verification
* `MAC.system mac`: `S_k` and `V_k` for `k ← G`
* `MAC.EUF`, `MAC.SUF`: verification restricted to the tagged messages, and to the tagged pairs
* `MAC.EUFCMA.systems`, `MAC.SUFCMA.systems`: the systems of EUF-CMA and SUF-CMA
* `MAC.EUFCMA`, `MAC.SUFCMA`: these notions for the admitted distinguishers, within an error

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

/-- **A MAC** with keys `K`, messages `M` and tags `T` [2, Definition 6.1, p. 217],
with an explicit key law. -/
structure MAC
    -- `K` carries shared keys, `M` messages, and `T` authentication tags.
    (K M T : Type) where
  /-- Key generation `G`. -/
  gen : Distribution.ProbDist K
  /-- The “signing algorithm” of [2, Definition 6.1, p. 217], as the tag law at `k, m`. -/
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

-- `K` carries shared keys, `M` messages, and `T` authentication tags.
variable {K M T : Type} [Fintype K] [Fintype M] [Fintype T]

/-- The table law `tags mac f = ∏ km, mac.tag km.1 km.2 (f km)`: independent tags for
every key/message pair. -/
def MAC.tags [DecidableEq K] [DecidableEq M] (mac : MAC K M T) :
    Distribution.ProbDist (K × M → T) :=
  Distribution.ProbDist.pi fun km => mac.tag km.1 km.2

-- Retain one `k ← mac.gen` shared by tagging and verification [2, Definition 6.1, p. 217].
-- Each `tag(m)` draws a fresh `mac.tag k m`; `verify(m, t)` returns `mac.verify k m t`.
-- The interface admits the selected total or per-port query budget.
system MAC.system
    -- `mac` supplies the shared-key law and tagging and verification operations.
    (mac : MAC K M T) [DecidableEq K] [DecidableEq M] : Tagging M T
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
    TypedSystem (Tagging.perPort M T q) × TypedSystem (Tagging.perPort M T q) :=
  (MAC.system.perPort mac, MAC.EUF.perPort M T • MAC.system.perPort mac)

/-- **The systems of SUF-CMA**: the real system and the one whose verification accepts only tagged
pairs, for `k ← G`, at the budget `q` per port. -/
def MAC.SUFCMA.systems [DecidableEq K] [DecidableEq M] [DecidableEq T] (mac : MAC K M T)
    (q : Tagging.Port → ℕ) :
    TypedSystem (Tagging.perPort M T q) × TypedSystem (Tagging.perPort M T q) :=
  (MAC.system.perPort mac, MAC.SUF.perPort M T • MAC.system.perPort mac)

/-- **EUF-CMA** within `error`: against the admitted distinguishers, the real system substitutes
for the one that accepts only tags on tagged messages. -/
def MAC.EUFCMA [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq K] [DecidableEq M] (mac : MAC K M T) {q : Tagging.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (Tagging.perPort M T q)) → ENNReal) : Prop :=
  (MAC.EUFCMA.systems mac q).1 ≃[error] (MAC.EUFCMA.systems mac q).2

/-- **SUF-CMA** within `error`: against the admitted distinguishers, the real system substitutes
for the one that accepts only tagged pairs. -/
def MAC.SUFCMA [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq K] [DecidableEq M] [DecidableEq T] (mac : MAC K M T) {q : Tagging.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (Tagging.perPort M T q)) → ENNReal) : Prop :=
  (MAC.SUFCMA.systems mac q).1 ≃[error] (MAC.SUFCMA.systems mac q).2

end

end Commons
