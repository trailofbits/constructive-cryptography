import Commons.Definitions.Ideal
import ConstructiveCryptography.Notation

/-!
# Pseudorandom generators

A PRG `G : S → R` (Boneh–Shoup, Section 3.1) is secure when its value on a uniform seed
substitutes for a uniform element of `R` (Attack Game 3.1, Definition 3.1). As systems on
`Evaluation Unit R`, the real system samples a seed once and answers with `G s`, and the ideal one
is the uniform random function on the one-point domain.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

## Main definitions

* `PRG.Secure.systems G q`: `G s` for a uniform seed `s`, and a uniform element of `R`
* `PRG.Secure G error`: the security of `G` for the admitted distinguishers,
  within `error`
-/

namespace Commons

open SystemAlgebra Probability
open scoped SystemAlgebra

noncomputable section

open Classical

variable {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]

/-- **The systems of PRG security**: `G s` for a uniform seed `s`, and a uniform element of `R`,
at the budget `q`. -/
def PRG.Secure.systems (G : S → R) (q : ℕ) :
    Interface.Resource (Evaluation Unit R q) × Interface.Resource (Evaluation Unit R q) :=
  (Interface.Resource.sample (Distribution.uniform S)
      fun s => Interface.Resource.ofFunction fun _ _ => G s,
    URF (Evaluation Unit R q))

/-- **PRG security** within `error`: against the admitted distinguishers, `G` on a uniform seed
substitutes for a uniform element of `R`. -/
def PRG.Secure [Interface.AdmissibleDistinguishers] (G : S → R)
    {q : ℕ} (error : (Evaluation Unit R q).inputDomain.Distinguisher → ENNReal) : Prop :=
  (PRG.Secure.systems G q).1 ≃[error] (PRG.Secure.systems G q).2

end

end Commons
