module

public import Commons.Definitions.Indifferentiability
public import Commons.Schemes.Sponge.Indifferentiability.GameEquiv
public import Commons.Schemes.Sponge.Indifferentiability.HCoefficient
public import Commons.Schemes.Sponge.Simulator

/-!
# Generic indifferentiability of the byte-oriented sponge construction

The real system is `spongePublic • StrongURP`; the ideal system is
`(H ◁ spongeSimulator) • sharedIdealRO`, sharing one random oracle between the honest
interface `H` and the simulator. This is the statistical, single-squeeze case of
[1, Theorem 2, p. 15]: "A padded sponge construction calling a random permutation".

`indifferentiability` packages the simulator and distance bound into
`Commons.Indifferentiability.specification` [3, Lemma 5]. The proof has two routes:

* `GameEquiv` combines bidirectional switching with equal unset-game transcript masses,
  giving `Q² / |C| + choose(Q, 2) / |S|`.
* `HCoefficient` adds the good-transcript ratio loss and the public collision cost,
  giving `Q² / |C|` through `indifferentiability_tight`.

Here `Q = w + q_pub`, `|C|` is the capacity alphabet size, and `|S|` the state alphabet size.
`HonestWorkSpec` bounds absorbed block work; the fixed-budget corollaries charge the
maximum padded length per honest query. The simulator uses independent draws with
collision costs, as specified in `Commons.Schemes.Sponge.Simulator`.

## References

1. G. Bertoni, J. Daemen, M. Peeters, and G. Van Assche. *On the Indifferentiability of the Sponge
   Construction*. In *Advances in Cryptology — EUROCRYPT 2008*, LNCS 4965, pp. 181–197, 2008.
   Page references use https://keccak.team/files/SpongeIndifferentiability.pdf.
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

variable
  -- `p` fixes the state, rate, capacity and digest widths and the padding suffix.
  (p : Parameters)
  -- `M` is the finite message alphabet; each theorem supplies its byte encoding.
  (M : Type) [Fintype M] [DecidableEq M]

/-- The game-equivalence route pays capacity collisions and bidirectional switching:
`Q² / |C| + choose(Q, 2) / |S|`. -/
noncomputable def indifferentiabilityBound (Q : ℕ) : ℝ≥0 :=
  (Q : ℝ≥0) ^ 2 / Fintype.card (ByteState p.capacityBytes) +
    (Q.choose 2 : ℝ≥0) / Fintype.card (ByteState p.stateBytes)

/-- The direct transcript-ratio route pays the capacity-collision bound `Q² / |C|`. -/
noncomputable def indifferentiabilityBoundTight (Q : ℕ) : ℝ≥0 :=
  (Q : ℝ≥0) ^ 2 / Fintype.card (ByteState p.capacityBytes)

/-- The nonnegative error has the same real-valued expression used by the transcript bound. -/
lemma coe_indifferentiabilityBound (Q : ℕ) :
    (indifferentiabilityBound p Q : ENNReal) = ENNReal.ofReal
      ((Q : ℝ) ^ 2 / Fintype.card (ByteState p.capacityBytes) +
        (Q.choose 2 : ℝ) / Fintype.card (ByteState p.stateBytes)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  simp only [indifferentiabilityBound, NNReal.coe_add, NNReal.coe_div,
    NNReal.coe_pow, NNReal.coe_natCast]

/-- The direct-route error agrees with the real-valued transcript bound. -/
lemma coe_indifferentiabilityBoundTight (Q : ℕ) :
    (indifferentiabilityBoundTight p Q : ENNReal) = ENNReal.ofReal
      ((Q : ℝ) ^ 2 / Fintype.card (ByteState p.capacityBytes)) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  simp only [indifferentiabilityBoundTight, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_natCast]

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
      indifferentiabilityBound p (w + q_pub) := by
  rw [coe_indifferentiabilityBound]
  exact sponge_indifferentiability_of_gameEquivalent p M hp henc spec q_pub

/-- Distance bound via **Path B** (direct 1-hop H-coefficient via `RatioCost`). -/
theorem indifferentiability_distance_of_hCoefficient (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      indifferentiabilityBound p (w + q_pub) := by
  rw [coe_indifferentiabilityBound]
  exact sponge_indifferentiability_of_hCoefficient p M hp henc spec q_pub

/-- Tight `Q^2 / |C|` distance bound via **Path B** (direct 1-hop H-coefficient). -/
theorem indifferentiability_distance_tight (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      indifferentiabilityBoundTight p (w + q_pub) := by
  rw [coe_indifferentiabilityBoundTight]
  exact sponge_indifferentiability_hCoefficient_tight p M hp henc spec q_pub

open Classical in
/-- Indifferentiability construction into `Commons.Indifferentiability.specification` via
**Path A** (2-hop `≡g` game equivalence + `BidirectionalSwitching`) [1, Theorem 2, p. 15],
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
**Path B** (direct 1-hop H-coefficient) [1, Theorem 2, p. 15], [3, Lemma 5]. -/
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
`Commons.Indifferentiability.specification` [1, Theorem 2, p. 15], [3, Lemma 5]. -/
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
