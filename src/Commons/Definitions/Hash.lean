import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation

/-!
# Hash functions

Collision resistance of a hash function `H : K → M → T` parameterized by a public uniform key, the
system parameter of Boneh–Shoup (Attack Game 8.1, Definition 8.1, with §8.1.1): as a pair of
systems that publish the key and answer each candidate `(m₀, m₁)`, the real system with whether
`H(k, m₀) = H(k, m₁)` and the ideal one with whether `m₀ = m₁`. The game admits only distinct
messages; here the two systems answer candidates of equal messages alike, so they differ exactly
on a collision.
The random oracle on `M` is the uniform random function `URF (Evaluation M T q)` of
`Commons.Definitions.Ideal`.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

## Main definitions

* `KeyedCollision K M`: the interface of the key and the candidate collisions
* `Hash.CR.systems H q`, `Hash.CR H error`: collision resistance
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

interface KeyedCollision(K M : Type) [Fintype K] [Fintype M]
  key() → K
  collide(first : M, second : M) → Bool

noncomputable section

variable {K M T : Type} [Fintype K] [Nonempty K] [Fintype M]

-- For `k ← K`: publish `k`; on `(m₀, m₁)`, whether `H(k, m₀) = H(k, m₁)`.
system Hash.Real(H : K → M → T) [DecidableEq T] : KeyedCollision K M
  initialize
    k ←$ 𝒰[K]
  on key() → K
    return k
  on collide(first : M, second : M) → Bool
    return decide (H k first = H k second)

-- For `k ← K`: publish `k`; on `(m₀, m₁)`, whether `m₀ = m₁`.
system Hash.Ideal(K M : Type) [Fintype K] [Nonempty K] [Fintype M] [DecidableEq M] : KeyedCollision K M
  initialize
    k ←$ 𝒰[K]
  on key() → K
    return k
  on collide(first : M, second : M) → Bool
    return decide (first = second)

/-- **The systems of collision resistance**: the collisions of `H(k, ·)` for a published `k ← K`,
and the equalities of messages, at the budget `q`. -/
def Hash.CR.systems [DecidableEq M] [DecidableEq T] (H : K → M → T) (q : ℕ) :
    Interface.Resource (KeyedCollision K M q) × Interface.Resource (KeyedCollision K M q) :=
  (Hash.Real H, Hash.Ideal K M)

/-- **Collision resistance** within `error`: against the admitted distinguishers, the collisions
of `H(k, ·)` for a published key substitute for the equalities of messages. -/
def Hash.CR [Interface.AdmissibleDistinguishers] [DecidableEq M]
    [DecidableEq T] (H : K → M → T) {q : ℕ}
    (error : (KeyedCollision K M q).inputDomain.Distinguisher → ENNReal) : Prop :=
  (Hash.CR.systems H q).1 ≃[error] (Hash.CR.systems H q).2

end

end Commons
