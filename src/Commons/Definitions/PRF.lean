module

public import Commons.Definitions.Ideal
public import ConstructiveCryptography.Notation

/-!
# Pseudorandom functions

A keyed function `F : K → X → Y` [1, §4.4, p. 131] is a pseudorandom function (PRF) within
`error` when its retained-key system `KeyedPRF.real F q` substitutes for the uniform random
function `URF (Evaluation X Y q)` against the admitted distinguishers.

`KeyedPRF.systems` names the real and ideal pair. `KeyedPRF.specification` collects retained-key
systems satisfying the chosen advantage bound. `KeyedPRF.of_converter` transfers security when
a converter realizes the target family and preserves the ideal random function.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
2. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis, ETH Zurich, 2020.
-/

@[expose] public section

set_option autoImplicit false

namespace Commons

open CategoryTheory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open SystemAlgebra Probability
open scoped SystemAlgebra SystemAlgebra.DSL

noncomputable section

variable {K X Y : Type} [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y]

/-- Retained-key system: sample `k ←$ 𝒰[K]` once and answer `eval(x)` with `F k x`
[1, §4.4, p. 131]. -/
def KeyedPRF.real (F : K → X → Y) (q : ℕ) : TypedSystem (Evaluation X Y q) :=
  sample k ←$ 𝒰[K]; system [Evaluation X Y q] _ x => F k x

/-- Pair of PRF systems `(KeyedPRF.real F q, URF (Evaluation X Y q))`. -/
def KeyedPRF.systems (F : K → X → Y) (q : ℕ) :
    TypedSystem (Evaluation X Y q) × TypedSystem (Evaluation X Y q) :=
  (KeyedPRF.real F q, URF (Evaluation X Y q))

/-- PRF security within `error`: `KeyedPRF.real F q` substitutes for `URF (Evaluation X Y q)`
against admitted distinguishers. -/
def KeyedPRF [AdmissibleDistinguishers Interface TypedDistinguisher] (F : K → X → Y) {q : ℕ}
    (error : TypedDistinguisher (Evaluation X Y q) → ENNReal) : Prop :=
  (KeyedPRF.systems F q).1 ≃[error] (KeyedPRF.systems F q).2

/-- Specification of all keyed families `F : K → X → Y` satisfying `KeyedPRF F error`. -/
def KeyedPRF.specification [AdmissibleDistinguishers Interface TypedDistinguisher]
    (K X Y : Type) [Fintype K] [Nonempty K] [Fintype X] [Fintype Y] [Nonempty Y] {q : ℕ}
    (error : TypedDistinguisher (Evaluation X Y q) → ENNReal) :
    ConstructiveCryptography.Specification (TypedSystem (Evaluation X Y q)) :=
  {R | ∃ F : K → X → Y, R = KeyedPRF.real F q ∧ KeyedPRF F error}

variable [AdmissibleDistinguishers Interface TypedDistinguisher]

/-- A PRF's keyed system belongs to `KeyedPRF.specification`. -/
lemma KeyedPRF.real_mem_specification {q : ℕ} {F : K → X → Y}
    {error : TypedDistinguisher (Evaluation X Y q) → ENNReal} (h : KeyedPRF F error) :
    KeyedPRF.real F q ∈ KeyedPRF.specification K X Y error :=
  ⟨F, rfl, h⟩

/-- `KeyedPRF.specification` lies in the reduction relaxation of `{URF (Evaluation X Y q)}`
[2, Definition 2.2.9, p. 22]. -/
lemma KeyedPRF.specification_subset_reductionRelaxation {q : ℕ}
    (error : TypedDistinguisher (Evaluation X Y q) → ENNReal) :
    KeyedPRF.specification K X Y error ⊆
      reductionRelaxation (Distinguishers.distinguisherAdvantage (Phi := TypedSystem)
        AdmissibleDistinguishers.admissible) error {URF (Evaluation X Y q)} := by
  rintro R ⟨F, rfl, hF⟩
  rw [mem_reductionRelaxation_iff]
  exact ⟨_, rfl, DistinguisherAdvantage.SubstitutesWithin.symm _ hF⟩

/-- Converter transport for PRF security: if `α` maps `KeyedPRF.real F q` to `KeyedPRF.real G q'`
and preserves `URF`, then `KeyedPRF F error` lifts to `KeyedPRF G (fun d => error (dα))`. -/
theorem KeyedPRF.of_converter
    -- `K'` carries the target family's keys, independently of the source key type `K`.
    {K' X' Y' : Type} [Fintype K'] [Nonempty K']
    [Fintype X'] [Fintype Y'] [Nonempty Y'] {q q' : ℕ}
    (α : Evaluation X' Y' q' ⟶ Evaluation X Y q) (F : K → X → Y) (G : K' → X' → Y')
    (closed : AdmissibleDistinguishers.ClosedUnder (Phi := TypedSystem)
      (D := TypedDistinguisher) α)
    (hreal : α • KeyedPRF.real F q = KeyedPRF.real G q')
    (hideal : α • URF (Evaluation X Y q) = URF (Evaluation X' Y' q'))
    {error : TypedDistinguisher (Evaluation X Y q) → ENNReal} (h : KeyedPRF F error) :
    KeyedPRF G (fun d => error (TypedDistinguisher.absorb d α)) :=
  AdmissibleDistinguishers.substitutesWithin_context α closed h hreal hideal

end

end Commons
