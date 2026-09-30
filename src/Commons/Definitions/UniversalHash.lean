import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation

/-!
# Universal hash functions

A keyed hash function `H : K → M → T` (Boneh–Shoup, Definition 7.1) with a uniform secret key.
It is a UHF when two distinct messages rarely collide (Attack Game 7.1, Definition 7.2), and a DUF
when no difference of the digests of two distinct messages is predictable (Attack Game 7.3,
Definition 7.5, on an additive group of digests; on bit strings with `⊕` this is the XOR
variant). As pairs of systems: the real system answers each candidate with whether
`H(k, m₀) = H(k, m₁)`, or `H(k, m₁) - H(k, m₀) = δ`, and the ideal one, the collision oracle of an
injective hash, with whether `m₀ = m₁`, or `m₀ = m₁ ∧ δ = 0`. The games admit only distinct
messages; here the two systems answer candidates of equal messages alike, so they differ exactly
on a winning candidate, as in Banfi's ind-cca, which answers the queries its source excludes
(Definition 2.3.5). With every distinguisher admitted, one query and the constant error `ε`, the
predicates are the `ε`-UHF and `ε`-DUF properties.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

## Main definitions

* `Collision M`, `Difference M T`: the interfaces of the candidate collisions and differences
* `UniversalHash.UHF.systems H q`, `UniversalHash.UHF H error`: UHF
* `UniversalHash.DUF.systems H q`, `UniversalHash.DUF H error`: DUF
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

interface Collision(M : Type) [Fintype M]
  collide(first : M, second : M) → Bool

interface Difference(M T : Type) [Fintype M] [Fintype T]
  differ(first : M, second : M, difference : T) → Bool

noncomputable section

variable {K M T : Type} [Fintype K] [Nonempty K] [Fintype M]

-- For `k ← K`: on `(m₀, m₁)`, whether `H(k, m₀) = H(k, m₁)`.
system UniversalHash.Real(H : K → M → T) [DecidableEq T] : Collision M
  initialize
    key ←$ 𝒰[K]
  on collide(first : M, second : M) → Bool
    return decide (H key first = H key second)

-- On `(m₀, m₁)`, whether `m₀ = m₁`.
system UniversalHash.Ideal(M : Type) [Fintype M] [DecidableEq M] : Collision M
  on collide(first : M, second : M) → Bool
    return decide (first = second)

-- For `k ← K`: on `(m₀, m₁, δ)`, whether `H(k, m₁) - H(k, m₀) = δ`.
system UniversalHash.DifferenceReal(H : K → M → T) [Fintype T] [DecidableEq T] [AddCommGroup T] : Difference M T
  initialize
    key ←$ 𝒰[K]
  on differ(first : M, second : M, difference : T) → Bool
    return decide (H key second - H key first = difference)

-- On `(m₀, m₁, δ)`, whether `m₀ = m₁` and `δ = 0`.
system UniversalHash.DifferenceIdeal(M T : Type) [Fintype M] [DecidableEq M] [Fintype T] [DecidableEq T] [AddCommGroup T] : Difference M T
  on differ(first : M, second : M, difference : T) → Bool
    return decide (first = second ∧ difference = 0)

/-- **The systems of a UHF**: the collisions of `H(k, ·)` for `k ← K`, and the equalities of
messages, at the budget `q`. -/
def UniversalHash.UHF.systems [DecidableEq M] [DecidableEq T] (H : K → M → T) (q : ℕ) :
    Interface.Resource (Collision M q) × Interface.Resource (Collision M q) :=
  (UniversalHash.Real H, UniversalHash.Ideal M)

/-- **UHF** within `error`: against the admitted distinguishers, the collisions of `H(k, ·)`
substitute for the equalities of messages. -/
def UniversalHash.UHF [Interface.AdmissibleDistinguishers]
    [DecidableEq M] [DecidableEq T] (H : K → M → T) {q : ℕ}
    (error : (Collision M q).inputDomain.Distinguisher → ENNReal) : Prop :=
  (UniversalHash.UHF.systems H q).1 ≃[error] (UniversalHash.UHF.systems H q).2

/-- **The systems of a DUF**: the digest differences of `H(k, ·)` for `k ← K`, and the trivial
differences, at the budget `q`. -/
def UniversalHash.DUF.systems [DecidableEq M] [Fintype T] [DecidableEq T] [AddCommGroup T]
    (H : K → M → T) (q : ℕ) :
    Interface.Resource (Difference M T q) × Interface.Resource (Difference M T q) :=
  (UniversalHash.DifferenceReal H, UniversalHash.DifferenceIdeal M T)

/-- **DUF** within `error`: against the admitted distinguishers, the digest differences of
`H(k, ·)` substitute for the trivial differences. -/
def UniversalHash.DUF [Interface.AdmissibleDistinguishers]
    [DecidableEq M] [Fintype T] [DecidableEq T] [AddCommGroup T] (H : K → M → T) {q : ℕ}
    (error : (Difference M T q).inputDomain.Distinguisher → ENNReal) : Prop :=
  (UniversalHash.DUF.systems H q).1 ≃[error] (UniversalHash.DUF.systems H q).2

end

end Commons
