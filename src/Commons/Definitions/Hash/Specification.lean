module

public import Commons.Definitions.Hash
public import ConstructiveCryptography.Instances.Substitution

/-!
# The collision-resistance specification

Fix the public-key collision interface and its ideal equality test. Each hash proves
membership in `Hash.CR.specification` using its own collision-resistance bound. An application
of the collision interface uses `Hash.CR.constructs_attach` once for every member.
-/

@[expose] public section

namespace Commons.Hash.CR

open ConstructiveCryptography SystemAlgebra
open scoped SystemAlgebra

noncomputable section

variable [AdmissibleDistinguishers Interface TypedDistinguisher]

/-- Resources on the collision interface within the per-observer bound `ε` of `Hash.Ideal`. -/
def specification
    -- The ideal publishes a uniform key in `K` and compares messages in `M` for equality.
    (K M : Type) [Fintype K] [Nonempty K] [Fintype M] [DecidableEq M] {q : ℕ}
    -- An admitted observer `d` at budget `q` may distinguish with advantage at most `ε d`.
    (ε : TypedDistinguisher (KeyedCollision K M q) → ENNReal) :
    Specification (TypedSystem (KeyedCollision K M q)) :=
  CryptographicAlgebra.Specification.reductionRelaxation
    (Distinguishers.distinguisherAdvantage AdmissibleDistinguishers.admissible) ε
    {Hash.Ideal K M}

variable {K M : Type} [Fintype K] [Nonempty K] [Fintype M] [DecidableEq M] {q : ℕ}

/-- Membership compares the supplied collision resource with the ideal equality test. -/
lemma mem_specification_iff
    {ε : TypedDistinguisher (KeyedCollision K M q) → ENNReal}
    {R : TypedSystem (KeyedCollision K M q)} :
    R ∈ specification K M ε ↔ R ≃[ε] Hash.Ideal K M := by
  rw [specification, Relaxation.apply_singleton]
  -- The relaxation compares the ideal with R. Symmetry gives the real-first bound.
  exact ⟨CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.symm _,
    CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.symm _⟩

/-- A keyed hash satisfies `Hash.CR` exactly when its real experiment meets the specification. -/
lemma iff_mem_specification {T : Type} [DecidableEq T] (H : K → M → T)
    {ε : TypedDistinguisher (KeyedCollision K M q) → ENNReal} :
    Hash.CR H ε ↔ Hash.Real H ∈ specification K M ε :=
  mem_specification_iff.symm

/-- Attaching the same application to every admitted collision resource carries its guarantee
to the outside interface. The error at observer `d` is the inside error at `d.absorb α`. -/
theorem constructs_attach
    -- `α` uses the inside collision interface and exposes the outside interface `A`.
    {A : Interface} (α : TypedConverter A (KeyedCollision K M q))
    -- Absorbing the application maps every admitted outside observer to an admitted inside one.
    (closed : AdmissibleDistinguishers.ClosedUnder (Phi := TypedSystem) α)
    (ε : TypedDistinguisher (KeyedCollision K M q) → ENNReal) :
    specification K M ε —[α]→ {R | R ≃[fun d => ε (d.absorb α)] α • Hash.Ideal K M} := by
  intro R admitted
  exact α.substitutesWithin_attach closed (mem_specification_iff.mp admitted)

end

end Commons.Hash.CR
