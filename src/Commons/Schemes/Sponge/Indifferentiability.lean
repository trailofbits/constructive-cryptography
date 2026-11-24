module

public import Commons.Definitions.Indifferentiability
public import Commons.Schemes.Sponge.Indifferentiability.GameEquiv
public import Commons.Schemes.Sponge.Indifferentiability.HCoefficient
public import Commons.Schemes.Sponge.Simulator

/-!
# Generic indifferentiability of the byte-oriented sponge construction

Constructs a shared ideal random oracle `sharedIdealRO` from `StrongURP (ByteState p.stateBytes)`
via the single-squeeze sponge converter `spongePublic` and lazy simulator `spongeSimulator`
[1, §§3–4], [2, §4], [3, §§3.4, 4.2].

Two independent proof engines establish the same unified distinguishing bound
`indifferentiabilityBound p (w + q_pub) = Q^2 / |C| + C(Q, 2) / |S|`:

* **Path A (`Commons.Schemes.Sponge.Indifferentiability.GameEquiv`)**: switches `StrongURP` to
  `LazyBidirectionalRF` (`C(Q, 2) / |S|`) and couples `realSpongeGame ≡g idealSpongeGame`
  (`Q^2 / |C|`).
* **Path B (`Commons.Schemes.Sponge.Indifferentiability.HCoefficient`)**: bounds the real/ideal
  distance directly in one hop via `RatioCost` (also yielding the tight bound `Q^2 / |C|`).

Both work-budgeted (`HonestWorkSpec`) and fixed-budget (`Evaluation M (ByteState p.outputBytes) q`)
interfaces are packaged into `Commons.Indifferentiability.specification`.

## References

1. G. Bertoni, J. Daemen, M. Peeters, and G. Van Assche. *On the Indifferentiability of the Sponge
   Construction*. In *Advances in Cryptology — EUROCRYPT 2008*, LNCS 4965, pp. 181–197, 2008.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
3. U. Maurer and R. Renner. *From Indifferentiability to Constructive Cryptography (and Back)*.
   In *Theory of Cryptography (TCC 2016-B)*, LNCS 9985, Springer, 2016.
   Cryptology ePrint Archive, Paper 2016/903.
-/

@[expose] public section

namespace Commons.Sponge

open CategoryTheory ConstructiveCryptography SystemAlgebra
open Commons.BidirectionalSwitching
open scoped BigOperators NNReal SystemAlgebra ConstructiveCryptography MonoidalCategory

section PublicAPI

variable (p : Parameters) (M : Type) [Fintype M] [DecidableEq M]

/-- Unified sponge indifferentiability error `Q^2 / |C| + C(Q, 2) / |S|` shared by both proof
engines [1, Theorem 1]. -/
noncomputable def indifferentiabilityBound (Q : ℕ) : ENNReal :=
  ENNReal.ofReal
    ((Q : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ) +
      ((Q.choose 2 : ℕ) : ℝ) / (Fintype.card (ByteState p.stateBytes) : ℝ))

/-- Tight 1-hop sponge indifferentiability error `Q^2 / |C|` [1, Theorem 1]. -/
noncomputable def indifferentiabilityBoundTight (Q : ℕ) : ENNReal :=
  ENNReal.ofReal ((Q : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ))

/-! ### Work-budgeted indifferentiability (both proof engines) -/

open Classical in
/-- Distance bound via **Path A** (2-hop `≡g` game equivalence + `BidirectionalSwitching`). -/
theorem indifferentiability_distance_of_gameEquivalent (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      indifferentiabilityBound p (w + q_pub) :=
  sponge_indifferentiability_of_gameEquivalent p M hp henc spec q_pub

/-- Distance bound via **Path B** (direct 1-hop H-coefficient via `RatioCost`). -/
theorem indifferentiability_distance_of_hCoefficient (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      indifferentiabilityBound p (w + q_pub) :=
  sponge_indifferentiability_of_hCoefficient p M hp henc spec q_pub

/-- Tight `Q^2 / |C|` distance bound via **Path B** (direct 1-hop H-coefficient). -/
theorem indifferentiability_distance_tight (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      indifferentiabilityBoundTight p (w + q_pub) :=
  sponge_indifferentiability_hCoefficient_tight p M hp henc spec q_pub

open Classical in
/-- Indifferentiability construction into `Commons.Indifferentiability.specification` via
**Path A** (2-hop `≡g` game equivalence + `BidirectionalSwitching`) [1, Theorem 1],
[3, Lemma 5]. -/
theorem indifferentiability_of_gameEquivalent (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    {simulators : Set (PrimitiveInterface p q_pub ⟶ SimROInterface p M q_pub)}
    (hadm : spongeSimulator p M encode q_pub ∈ simulators) :
    ({StrongURP (ByteState p.stateBytes) (q := w + q_pub)} :
        ConstructiveCryptography.Specification
          (TypedSystem (PrimitiveInterface p (w + q_pub)))) —[spongePublic p M spec q_pub]→
      Commons.Indifferentiability.specification (sharedIdealRO p M spec q_pub) simulators
        (indifferentiabilityBound p (w + q_pub)) :=
  Commons.Indifferentiability.constructs_of_simulator (spongeSimulator p M encode q_pub) hadm
    (indifferentiability_distance_of_gameEquivalent p M hp henc spec q_pub)

/-- Indifferentiability construction into `Commons.Indifferentiability.specification` via
**Path B** (direct 1-hop H-coefficient) [1, Theorem 1], [3, Lemma 5]. -/
theorem indifferentiability_of_hCoefficient (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    {simulators : Set (PrimitiveInterface p q_pub ⟶ SimROInterface p M q_pub)}
    (hadm : spongeSimulator p M encode q_pub ∈ simulators) :
    ({StrongURP (ByteState p.stateBytes) (q := w + q_pub)} :
        ConstructiveCryptography.Specification
          (TypedSystem (PrimitiveInterface p (w + q_pub)))) —[spongePublic p M spec q_pub]→
      Commons.Indifferentiability.specification (sharedIdealRO p M spec q_pub) simulators
        (indifferentiabilityBound p (w + q_pub)) :=
  Commons.Indifferentiability.constructs_of_simulator (spongeSimulator p M encode q_pub) hadm
    (indifferentiability_distance_of_hCoefficient p M hp henc spec q_pub)

/-- Headline sponge indifferentiability construction into
`Commons.Indifferentiability.specification` [1, Theorem 1], [3, Lemma 5]. -/
theorem indifferentiability (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    {simulators : Set (PrimitiveInterface p q_pub ⟶ SimROInterface p M q_pub)}
    (hadm : spongeSimulator p M encode q_pub ∈ simulators) :
    ({StrongURP (ByteState p.stateBytes) (q := w + q_pub)} :
        ConstructiveCryptography.Specification
          (TypedSystem (PrimitiveInterface p (w + q_pub)))) —[spongePublic p M spec q_pub]→
      Commons.Indifferentiability.specification (sharedIdealRO p M spec q_pub) simulators
        (indifferentiabilityBound p (w + q_pub)) :=
  indifferentiability_of_gameEquivalent p M hp henc spec q_pub hadm

/-- Tight `Q^2 / |C|` sponge indifferentiability construction into
`Commons.Indifferentiability.specification` via the 1-hop H-coefficient engine. -/
theorem indifferentiability_tight (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    {simulators : Set (PrimitiveInterface p q_pub ⟶ SimROInterface p M q_pub)}
    (hadm : spongeSimulator p M encode q_pub ∈ simulators) :
    ({StrongURP (ByteState p.stateBytes) (q := w + q_pub)} :
        ConstructiveCryptography.Specification
          (TypedSystem (PrimitiveInterface p (w + q_pub)))) —[spongePublic p M spec q_pub]→
      Commons.Indifferentiability.specification (sharedIdealRO p M spec q_pub) simulators
        (indifferentiabilityBoundTight p (w + q_pub)) :=
  Commons.Indifferentiability.constructs_of_simulator (spongeSimulator p M encode q_pub) hadm
    (indifferentiability_distance_tight p M hp henc spec q_pub)

/-! ### Fixed-budget (`Evaluation M (ByteState p.outputBytes) q_honest`) packaging -/

/-- Fixed-budget sponge converter on `Evaluation M (ByteState p.outputBytes) q_honest`. -/
noncomputable abbrev spongePublicFixed (encode : M → List (BitVec 8)) (maxBlocks : ℕ)
    (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ) :
    HonestInterface p M q_honest ⊗ PrimitiveInterface p q_pub ⟶
      PrimitiveInterface p (q_honest * maxBlocks + q_pub) :=
  spongePublic p M (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest) q_pub

/-- Fixed-budget shared ideal RO on `Evaluation M (ByteState p.outputBytes) q_honest`. -/
noncomputable abbrev sharedIdealROFixed (encode : M → List (BitVec 8)) (maxBlocks : ℕ)
    (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ) :
    TypedSystem (HonestInterface p M q_honest ⊗ SimROInterface p M q_pub) :=
  sharedIdealRO p M (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest) q_pub

open Classical in
/-- Fixed-budget distance bound on `Evaluation M (ByteState p.outputBytes) q_honest` via
**Path A** (2-hop `≡g` game equivalence + `BidirectionalSwitching`). -/
theorem indifferentiability_fixedBudget_distance_of_gameEquivalent (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode)
    (maxBlocks : ℕ) (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ) :
    Δ (spongePublicFixed p M encode maxBlocks hmax q_honest q_pub •
        StrongURP (ByteState p.stateBytes) (q := q_honest * maxBlocks + q_pub))
      ((HonestInterface p M q_honest ◁ spongeSimulator p M encode q_pub) •
        sharedIdealROFixed p M encode maxBlocks hmax q_honest q_pub) ≤
      indifferentiabilityBound p (q_honest * maxBlocks + q_pub) :=
  indifferentiability_distance_of_gameEquivalent p M hp henc
    (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest) q_pub

/-- Fixed-budget distance bound on `Evaluation M (ByteState p.outputBytes) q_honest` via
**Path B** (direct 1-hop H-coefficient). -/
theorem indifferentiability_fixedBudget_distance_of_hCoefficient (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode)
    (maxBlocks : ℕ) (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ) :
    Δ (spongePublicFixed p M encode maxBlocks hmax q_honest q_pub •
        StrongURP (ByteState p.stateBytes) (q := q_honest * maxBlocks + q_pub))
      ((HonestInterface p M q_honest ◁ spongeSimulator p M encode q_pub) •
        sharedIdealROFixed p M encode maxBlocks hmax q_honest q_pub) ≤
      indifferentiabilityBound p (q_honest * maxBlocks + q_pub) :=
  indifferentiability_distance_of_hCoefficient p M hp henc
    (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest) q_pub

/-- Fixed-budget tight `Q^2 / |C|` distance bound on
`Evaluation M (ByteState p.outputBytes) q_honest`. -/
theorem indifferentiability_fixedBudget_distance_tight (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode)
    (maxBlocks : ℕ) (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ) :
    Δ (spongePublicFixed p M encode maxBlocks hmax q_honest q_pub •
        StrongURP (ByteState p.stateBytes) (q := q_honest * maxBlocks + q_pub))
      ((HonestInterface p M q_honest ◁ spongeSimulator p M encode q_pub) •
        sharedIdealROFixed p M encode maxBlocks hmax q_honest q_pub) ≤
      indifferentiabilityBoundTight p (q_honest * maxBlocks + q_pub) :=
  indifferentiability_distance_tight p M hp henc
    (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest) q_pub

open Classical in
/-- Fixed-budget indifferentiability construction into `Commons.Indifferentiability.specification`
for `Evaluation M (ByteState p.outputBytes) q_honest` via **Path A**. -/
theorem indifferentiability_fixedBudget_of_gameEquivalent (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode)
    (maxBlocks : ℕ) (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ)
    {simulators : Set (PrimitiveInterface p q_pub ⟶ SimROInterface p M q_pub)}
    (hadm : spongeSimulator p M encode q_pub ∈ simulators) :
    ({StrongURP (ByteState p.stateBytes) (q := q_honest * maxBlocks + q_pub)} :
        ConstructiveCryptography.Specification
          (TypedSystem (PrimitiveInterface p (q_honest * maxBlocks + q_pub))))
        —[spongePublicFixed p M encode maxBlocks hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed p M encode maxBlocks hmax q_honest q_pub) simulators
        (indifferentiabilityBound p (q_honest * maxBlocks + q_pub)) :=
  indifferentiability_of_gameEquivalent p M hp henc
    (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest) q_pub hadm

/-- Fixed-budget indifferentiability construction into `Commons.Indifferentiability.specification`
for `Evaluation M (ByteState p.outputBytes) q_honest` via **Path B**. -/
theorem indifferentiability_fixedBudget_of_hCoefficient (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode)
    (maxBlocks : ℕ) (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ)
    {simulators : Set (PrimitiveInterface p q_pub ⟶ SimROInterface p M q_pub)}
    (hadm : spongeSimulator p M encode q_pub ∈ simulators) :
    ({StrongURP (ByteState p.stateBytes) (q := q_honest * maxBlocks + q_pub)} :
        ConstructiveCryptography.Specification
          (TypedSystem (PrimitiveInterface p (q_honest * maxBlocks + q_pub))))
        —[spongePublicFixed p M encode maxBlocks hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed p M encode maxBlocks hmax q_honest q_pub) simulators
        (indifferentiabilityBound p (q_honest * maxBlocks + q_pub)) :=
  indifferentiability_of_hCoefficient p M hp henc
    (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest) q_pub hadm

/-- Headline fixed-budget indifferentiability construction into
`Commons.Indifferentiability.specification` for `Evaluation M (ByteState p.outputBytes) q_honest`.
-/
theorem indifferentiability_fixedBudget (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode)
    (maxBlocks : ℕ) (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ)
    {simulators : Set (PrimitiveInterface p q_pub ⟶ SimROInterface p M q_pub)}
    (hadm : spongeSimulator p M encode q_pub ∈ simulators) :
    ({StrongURP (ByteState p.stateBytes) (q := q_honest * maxBlocks + q_pub)} :
        ConstructiveCryptography.Specification
          (TypedSystem (PrimitiveInterface p (q_honest * maxBlocks + q_pub))))
        —[spongePublicFixed p M encode maxBlocks hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed p M encode maxBlocks hmax q_honest q_pub) simulators
        (indifferentiabilityBound p (q_honest * maxBlocks + q_pub)) :=
  indifferentiability_fixedBudget_of_gameEquivalent p M hp henc maxBlocks hmax q_honest q_pub hadm

/-- Tight `Q^2 / |C|` fixed-budget indifferentiability construction into
`Commons.Indifferentiability.specification` for `Evaluation M (ByteState p.outputBytes) q_honest`.
-/
theorem indifferentiability_fixedBudget_tight (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode)
    (maxBlocks : ℕ) (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks)
    (q_honest q_pub : ℕ)
    {simulators : Set (PrimitiveInterface p q_pub ⟶ SimROInterface p M q_pub)}
    (hadm : spongeSimulator p M encode q_pub ∈ simulators) :
    ({StrongURP (ByteState p.stateBytes) (q := q_honest * maxBlocks + q_pub)} :
        ConstructiveCryptography.Specification
          (TypedSystem (PrimitiveInterface p (q_honest * maxBlocks + q_pub))))
        —[spongePublicFixed p M encode maxBlocks hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed p M encode maxBlocks hmax q_honest q_pub) simulators
        (indifferentiabilityBoundTight p (q_honest * maxBlocks + q_pub)) :=
  indifferentiability_tight p M hp henc
    (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest) q_pub hadm

end PublicAPI

end Commons.Sponge
