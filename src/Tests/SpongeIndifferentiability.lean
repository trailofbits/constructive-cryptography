module

public import Commons.Schemes.Sponge.Indifferentiability
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution
public import RandomSystems.Typed.DSL.Syntax
public import RandomSystems.Typed.SamplingDistance

/-!
# Tests for generic sponge indifferentiability

Exercises `Commons.Schemes.Sponge.Indifferentiability` across both independent proof engines
(**Path A**: 2-hop `≡g` game equivalence + `BidirectionalSwitching`; **Path B**: 1-hop `RatioCost`
H-coefficient), on both work-budgeted (`HonestWorkSpec`) and fixed-budget
(`Evaluation M (ByteState p.outputBytes) q_honest`) interfaces:

* Concrete small 4-byte sponge `⟨4, 2, 1, 0x06⟩` and standard `sha3_256`, `sha3_384`, `sha3_512`.
* Composition via `Commons.Indifferentiability.compose` and
  `Commons.Indifferentiability.compose_mixed` on `Interface`.
* Tactic interoperability with `cc_normalize`, `cc_construct`, and `cc_calc statistical` under
  full CC custom notation (`Δ`, `•`, `∥`, `◁`, `▷`, `—[...]→`, `≡g`, `𝒰[...]`).
* Axiom audit (`#print axioms`) on headline exported theorems from both proof engines.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.SpongeIndifferentiability

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open SystemAlgebra Probability Commons Commons.Sponge Commons.BidirectionalSwitching
open scoped NNReal SystemAlgebra SystemAlgebra.DSL

/-! ### Concrete valid sponge parameter instances -/

/-- Small valid 4-byte sponge (2-byte rate, 2-byte capacity, 1-byte digest, suffix `0x06`). -/
def smallSponge : Parameters := ⟨4, 2, 1, 0x06⟩

lemma smallSponge_valid : smallSponge.Valid :=
  Parameters.valid_of_toNat (n := 6) (by omega) (by omega) (by omega) (by omega) rfl
    (by omega) (by omega)

/-- Fixed-length byte-vector encoding `ByteState k → List (BitVec 8)` via `List.ofFn`. -/
def encodeFixed (k : ℕ) (m : ByteState k) : List (BitVec 8) :=
  List.ofFn m

lemma encodeFixed_injective (k : ℕ) : Function.Injective (encodeFixed k) := by
  intro a b h
  funext i
  have hi := congrArg (fun l => l[i.val]?) h
  simpa only [encodeFixed, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.some.injEq] using hi

lemma encodeFixed_length (k : ℕ) (m : ByteState k) : (encodeFixed k m).length = k :=
  List.length_ofFn

/-! ### Small 4-byte sponge: Path A (`≡g`), Path B (`RatioCost`), work-budgeted and fixed-budget -/

/-- Path A (2-hop `≡g` + `BidirectionalSwitching`) on the 4-byte sponge with work budget `w`. -/
example (w q_pub : ℕ) :
    let spec := HonestWorkSpec.ofWorkBudget smallSponge (ByteState 1) smallSponge_valid
      (encodeFixed 1) w
    Δ (spongePublic smallSponge (ByteState 1) spec q_pub •
        StrongURP (ByteState smallSponge.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator smallSponge (ByteState 1) (encodeFixed 1) q_pub) •
        sharedIdealRO smallSponge (ByteState 1) spec q_pub) ≤
      indifferentiabilityBound smallSponge (w + q_pub) :=
  indifferentiability_distance_of_gameEquivalent smallSponge (ByteState 1) smallSponge_valid
    (encodeFixed_injective 1)
    (HonestWorkSpec.ofWorkBudget smallSponge (ByteState 1) smallSponge_valid (encodeFixed 1) w)
    q_pub

/-- Path B (1-hop H-coefficient) yields the exact same unified bound on the 4-byte sponge. -/
example (w q_pub : ℕ) :
    let spec := HonestWorkSpec.ofWorkBudget smallSponge (ByteState 1) smallSponge_valid
      (encodeFixed 1) w
    Δ (spongePublic smallSponge (ByteState 1) spec q_pub •
        StrongURP (ByteState smallSponge.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator smallSponge (ByteState 1) (encodeFixed 1) q_pub) •
        sharedIdealRO smallSponge (ByteState 1) spec q_pub) ≤
      indifferentiabilityBound smallSponge (w + q_pub) :=
  indifferentiability_distance_of_hCoefficient smallSponge (ByteState 1) smallSponge_valid
    (encodeFixed_injective 1)
    (HonestWorkSpec.ofWorkBudget smallSponge (ByteState 1) smallSponge_valid (encodeFixed 1) w)
    q_pub

/-- Fixed-budget (`Evaluation (ByteState 1) (ByteState 1) q_honest`) packaging on the 4-byte
sponge for both Path A and Path B. -/
example (q_honest q_pub : ℕ) :
    let hmax : ∀ m : ByteState 1,
        paddedBlockCount smallSponge (encodeFixed 1 m).length ≤ 1 := fun m => by
      rw [encodeFixed_length]; decide
    ({StrongURP (ByteState smallSponge.stateBytes) (q := q_honest * 1 + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface smallSponge (q_honest * 1 + q_pub))))
        —[spongePublicFixed smallSponge (ByteState 1) (encodeFixed 1) 1 hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed smallSponge (ByteState 1) (encodeFixed 1) 1 hmax q_honest q_pub)
        {spongeSimulator smallSponge (ByteState 1) (encodeFixed 1) q_pub}
        (indifferentiabilityBound smallSponge (q_honest * 1 + q_pub)) :=
  indifferentiability_fixedBudget smallSponge (ByteState 1) smallSponge_valid
    (encodeFixed_injective 1) 1 (fun m => by rw [encodeFixed_length]; decide)
    q_honest q_pub (Set.mem_singleton _)

/-- Explicit `GameEquivalent` (`≡g`) witness on the 4-byte sponge between `realSpongeGame` and
`idealSpongeGame`. -/
example (w q_pub : ℕ) :
    let spec := HonestWorkSpec.ofWorkBudget smallSponge (ByteState 1) smallSponge_valid
      (encodeFixed 1) w
    (realSpongeGame smallSponge (ByteState 1) spec q_pub).1.1.GameEquivalent
      (idealSpongeGame smallSponge (ByteState 1) spec q_pub).1.1 :=
  realSpongeGame_gameEquivalent_idealSpongeGame smallSponge (ByteState 1) smallSponge_valid
    (encodeFixed_injective 1)
    (HonestWorkSpec.ofWorkBudget smallSponge (ByteState 1) smallSponge_valid (encodeFixed 1) w)
    q_pub

/-! ### Standard SHA-3 instances (`sha3_256`, `sha3_384`, `sha3_512`) -/

/-- `sha3_256` indifferentiability via Path A (`≡g`) and Path B (`RatioCost`) on 32-byte inputs
(fixed budget `Evaluation (ByteState 32) (ByteState 32) q_honest`). -/
example (q_honest q_pub : ℕ) :
    let hmax : ∀ m : ByteState 32, paddedBlockCount sha3_256 (encodeFixed 32 m).length ≤ 1 :=
      fun m => by rw [encodeFixed_length]; decide
    ({StrongURP (ByteState sha3_256.stateBytes) (q := q_honest * 1 + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface sha3_256 (q_honest * 1 + q_pub))))
        —[spongePublicFixed sha3_256 (ByteState 32) (encodeFixed 32) 1 hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed sha3_256 (ByteState 32) (encodeFixed 32) 1 hmax q_honest q_pub)
        {spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub}
        (indifferentiabilityBound sha3_256 (q_honest * 1 + q_pub)) ∧
    ({StrongURP (ByteState sha3_256.stateBytes) (q := q_honest * 1 + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface sha3_256 (q_honest * 1 + q_pub))))
        —[spongePublicFixed sha3_256 (ByteState 32) (encodeFixed 32) 1 hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed sha3_256 (ByteState 32) (encodeFixed 32) 1 hmax q_honest q_pub)
        {spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub}
        (indifferentiabilityBoundTight sha3_256 (q_honest * 1 + q_pub)) :=
  ⟨indifferentiability_fixedBudget_of_gameEquivalent sha3_256 (ByteState 32) sha3_256_valid
      (encodeFixed_injective 32) 1 (fun m => by rw [encodeFixed_length]; decide)
      q_honest q_pub (Set.mem_singleton _),
    indifferentiability_fixedBudget_tight sha3_256 (ByteState 32) sha3_256_valid
      (encodeFixed_injective 32) 1 (fun m => by rw [encodeFixed_length]; decide)
      q_honest q_pub (Set.mem_singleton _)⟩

/-- `sha3_384` indifferentiability via Path A and Path B (work-budgeted). -/
example (w q_pub : ℕ) :
    let spec := HonestWorkSpec.ofWorkBudget sha3_384 (ByteState 32) sha3_384_valid
      (encodeFixed 32) w
    ({StrongURP (ByteState sha3_384.stateBytes) (q := w + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface sha3_384 (w + q_pub))))
        —[spongePublic sha3_384 (ByteState 32) spec q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealRO sha3_384 (ByteState 32) spec q_pub)
        {spongeSimulator sha3_384 (ByteState 32) (encodeFixed 32) q_pub}
        (indifferentiabilityBound sha3_384 (w + q_pub)) ∧
    ({StrongURP (ByteState sha3_384.stateBytes) (q := w + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface sha3_384 (w + q_pub))))
        —[spongePublic sha3_384 (ByteState 32) spec q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealRO sha3_384 (ByteState 32) spec q_pub)
        {spongeSimulator sha3_384 (ByteState 32) (encodeFixed 32) q_pub}
        (indifferentiabilityBound sha3_384 (w + q_pub)) :=
  ⟨indifferentiability_of_gameEquivalent sha3_384 (ByteState 32) sha3_384_valid
      (encodeFixed_injective 32)
      (HonestWorkSpec.ofWorkBudget sha3_384 (ByteState 32) sha3_384_valid (encodeFixed 32) w)
      q_pub (Set.mem_singleton _),
    indifferentiability_of_hCoefficient sha3_384 (ByteState 32) sha3_384_valid
      (encodeFixed_injective 32)
      (HonestWorkSpec.ofWorkBudget sha3_384 (ByteState 32) sha3_384_valid (encodeFixed 32) w)
      q_pub (Set.mem_singleton _)⟩

/-- `sha3_512` indifferentiability via Path A and Path B (fixed-budget). -/
example (q_honest q_pub : ℕ) :
    let hmax : ∀ m : ByteState 32, paddedBlockCount sha3_512 (encodeFixed 32 m).length ≤ 1 :=
      fun m => by rw [encodeFixed_length]; decide
    ({StrongURP (ByteState sha3_512.stateBytes) (q := q_honest * 1 + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface sha3_512 (q_honest * 1 + q_pub))))
        —[spongePublicFixed sha3_512 (ByteState 32) (encodeFixed 32) 1 hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed sha3_512 (ByteState 32) (encodeFixed 32) 1 hmax q_honest q_pub)
        {spongeSimulator sha3_512 (ByteState 32) (encodeFixed 32) q_pub}
        (indifferentiabilityBound sha3_512 (q_honest * 1 + q_pub)) ∧
    ({StrongURP (ByteState sha3_512.stateBytes) (q := q_honest * 1 + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface sha3_512 (q_honest * 1 + q_pub))))
        —[spongePublicFixed sha3_512 (ByteState 32) (encodeFixed 32) 1 hmax q_honest q_pub]→
      Commons.Indifferentiability.specification
        (sharedIdealROFixed sha3_512 (ByteState 32) (encodeFixed 32) 1 hmax q_honest q_pub)
        {spongeSimulator sha3_512 (ByteState 32) (encodeFixed 32) q_pub}
        (indifferentiabilityBound sha3_512 (q_honest * 1 + q_pub)) :=
  ⟨indifferentiability_fixedBudget_of_gameEquivalent sha3_512 (ByteState 32) sha3_512_valid
      (encodeFixed_injective 32) 1 (fun m => by rw [encodeFixed_length]; decide)
      q_honest q_pub (Set.mem_singleton _),
    indifferentiability_fixedBudget_of_hCoefficient sha3_512 (ByteState 32) sha3_512_valid
      (encodeFixed_injective 32) 1 (fun m => by rw [encodeFixed_length]; decide)
      q_honest q_pub (Set.mem_singleton _)⟩

/-! ### Composition (`compose`, `compose_mixed`) and tactic interoperability -/

/-- Serial composition of `sha3_256` indifferentiability with a downstream application via
`Commons.Indifferentiability.compose` and `cc_construct`. -/
example {H' : Interface} (w q_pub : ℕ)
    (spec : HonestWorkSpec sha3_256 (ByteState 32) (encodeFixed 32) w)
    (application : H' ⟶ spec.toInterface)
    (target : TypedSystem (H' ⊗ SimROInterface sha3_256 (ByteState 32) q_pub))
    {δ : ENNReal}
    (idealApp :
      Δ ((application ▷ SimROInterface sha3_256 (ByteState 32) q_pub) •
          sharedIdealRO sha3_256 (ByteState 32) spec q_pub) target ≤ δ) :
    ({StrongURP (ByteState sha3_256.stateBytes) (q := w + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface sha3_256 (w + q_pub))))
        —[(application ▷ PrimitiveInterface sha3_256 q_pub) ≫
            spongePublic sha3_256 (ByteState 32) spec q_pub]→
      Commons.Indifferentiability.specification target
        {spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub}
        (indifferentiabilityBound sha3_256 (w + q_pub) + δ) :=
  Commons.Indifferentiability.compose
    (indifferentiability sha3_256 (ByteState 32) sha3_256_valid (encodeFixed_injective 32)
      spec q_pub (Set.mem_singleton _))
    (by cc_construct; exact idealApp)

/-- Keyed/mixed composition of `sha3_256` indifferentiability via
`Commons.Indifferentiability.compose_mixed` and `TypedSystem.sample`. -/
example {H' : Interface} {K : Type} [Fintype K] [Nonempty K] (w q_pub : ℕ)
    (spec : HonestWorkSpec sha3_256 (ByteState 32) (encodeFixed 32) w)
    (application : K → (H' ⟶ spec.toInterface))
    (target : TypedSystem (H' ⊗ SimROInterface sha3_256 (ByteState 32) q_pub))
    {δ : ENNReal}
    (idealApp :
      Δ (sample k ← (𝒰[K]).1;
          (application k ▷ SimROInterface sha3_256 (ByteState 32) q_pub) •
            sharedIdealRO sha3_256 (ByteState 32) spec q_pub) target ≤ δ) :
    (sample k ← (𝒰[K]).1;
        ((application k ▷ PrimitiveInterface sha3_256 q_pub) ≫
          spongePublic sha3_256 (ByteState 32) spec q_pub) •
        StrongURP (ByteState sha3_256.stateBytes) (q := w + q_pub)) ∈
      Commons.Indifferentiability.specification target
        {spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub}
        (indifferentiabilityBound sha3_256 (w + q_pub) + δ) := by
  let ε : ℝ≥0 :=
    ⟨(((w + q_pub : ℕ) : ℝ) ^ 2 /
        (Fintype.card (ByteState sha3_256.capacityBytes) : ℝ) +
      (((w + q_pub).choose 2 : ℕ) : ℝ) /
        (Fintype.card (ByteState sha3_256.stateBytes) : ℝ)), by positivity⟩
  have hε : indifferentiabilityBound sha3_256 (w + q_pub) = (ε : ENNReal) := by
    unfold indifferentiabilityBound
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  rw [hε]
  exact Commons.Indifferentiability.compose_mixed
    (TypedSystem.sample (𝒰[K]).1) (TypedSystem.sample (𝒰[K]).1)
    (spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub) (Set.mem_singleton _)
    (fun f => TypedConverter.smul_sample
      (H' ◁ spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub) (𝒰[K]).1 f)
    (fun a b hab => by
      simpa only [Interface.cc_distance_eq] using
        TypedSystem.transcriptDistance_sample_le (𝒰[K]).1 a b ε hab)
    (hε ▸ indifferentiability_distance_of_gameEquivalent sha3_256 (ByteState 32) sha3_256_valid
      (encodeFixed_injective 32) spec q_pub)
    idealApp

/-- `cc_calc statistical` composes Hop 1 (`BidirectionalSwitching`) and Hop 2
(`lazyBidirectionalRF_sponge_dist_ideal_le`) cleanly under full CC custom notation. -/
example (w q_pub : ℕ) (spec : HonestWorkSpec sha3_256 (ByteState 32) (encodeFixed 32) w) :
    Δ (spongePublic sha3_256 (ByteState 32) spec q_pub •
        StrongURP (ByteState sha3_256.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub) •
        sharedIdealRO sha3_256 (ByteState 32) spec q_pub) ≤
      ENNReal.ofReal
        ((((w + q_pub).choose 2 : ℕ) : ℝ) / (Fintype.card (ByteState sha3_256.stateBytes) : ℝ)) +
      ENNReal.ofReal
        (((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState sha3_256.capacityBytes) : ℝ)) := by
  cc_calc statistical
    spongePublic sha3_256 (ByteState 32) spec q_pub •
        StrongURP (ByteState sha3_256.stateBytes) (q := w + q_pub)
      ≈[ENNReal.ofReal ((((w + q_pub).choose 2 : ℕ) : ℝ) /
          (Fintype.card (ByteState sha3_256.stateBytes) : ℝ))]
      spongePublic sha3_256 (ByteState 32) spec q_pub •
        LazyBidirectionalRF (ByteState sha3_256.stateBytes) (w + q_pub) :=
      strongURP_attach_dist_lazyBidirectionalRF_le (ByteState sha3_256.stateBytes) (w + q_pub)
        (spongePublic sha3_256 (ByteState 32) spec q_pub)
    _ ≈[ENNReal.ofReal (((w + q_pub : ℕ) : ℝ) ^ 2 /
          (Fintype.card (ByteState sha3_256.capacityBytes) : ℝ))]
      (spec.toInterface ◁ spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub) •
        sharedIdealRO sha3_256 (ByteState 32) spec q_pub :=
      lazyBidirectionalRF_sponge_dist_ideal_le sha3_256 (ByteState 32) sha3_256_valid
        (encodeFixed_injective 32) spec q_pub

/-- `Commons.Indifferentiability.compose` chains sponge indifferentiability with an arbitrary
ideal-world specification construction. -/
example {H' : Interface} (w q_pub : ℕ)
    (spec : HonestWorkSpec sha3_256 (ByteState 32) (encodeFixed 32) w)
    (application : H' ⟶ spec.toInterface)
    (target : Specification (TypedSystem (H' ⊗ SimROInterface sha3_256 (ByteState 32) q_pub)))
    {δ : ENNReal}
    (idealApp :
      ({sharedIdealRO sha3_256 (ByteState 32) spec q_pub} :
          Specification (TypedSystem (spec.toInterface ⊗ SimROInterface sha3_256 (ByteState 32)
            q_pub)))
        —[application ▷ SimROInterface sha3_256 (ByteState 32) q_pub; δ]→ target) :
    ({StrongURP (ByteState sha3_256.stateBytes) (q := w + q_pub)} :
        Specification (TypedSystem (PrimitiveInterface sha3_256 (w + q_pub))))
        —[(application ▷ PrimitiveInterface sha3_256 q_pub) ≫
            spongePublic sha3_256 (ByteState 32) spec q_pub]→
      epsilonRelaxation (indifferentiabilityBound sha3_256 (w + q_pub) + δ)
        (simulatorImage {spongeSimulator sha3_256 (ByteState 32) (encodeFixed 32) q_pub} target) :=
          by
  exact Commons.Indifferentiability.compose
    (indifferentiability sha3_256 (ByteState 32) sha3_256_valid (encodeFixed_injective 32)
      spec q_pub (Set.mem_singleton _))
    idealApp

/-- `cc_normalize` simplifies serial attachment of an application onto `spongePublic`. -/
example {H' : Interface} (w q_pub : ℕ)
    (spec : HonestWorkSpec sha3_256 (ByteState 32) (encodeFixed 32) w)
    (application : H' ⟶ spec.toInterface) :
    ((application ▷ PrimitiveInterface sha3_256 q_pub) ≫
        spongePublic sha3_256 (ByteState 32) spec q_pub) •
      StrongURP (ByteState sha3_256.stateBytes) (q := w + q_pub) =
    (application ▷ PrimitiveInterface sha3_256 q_pub) •
      (spongePublic sha3_256 (ByteState 32) spec q_pub •
        StrongURP (ByteState sha3_256.stateBytes) (q := w + q_pub)) := by
  cc_normalize

/-! ### Axiom audit of headline exported theorems (Path A and Path B) -/

#print axioms Commons.Sponge.realSpongeGame_gameEquivalent_idealSpongeGame
#print axioms Commons.Sponge.sponge_indifferentiability_of_gameEquivalent
#print axioms Commons.Sponge.sponge_indifferentiability_of_hCoefficient
#print axioms Commons.Sponge.sponge_indifferentiability_hCoefficient_tight
#print axioms Commons.Sponge.indifferentiability
#print axioms Commons.Sponge.indifferentiability_of_gameEquivalent
#print axioms Commons.Sponge.indifferentiability_of_hCoefficient
#print axioms Commons.Sponge.indifferentiability_tight
#print axioms Commons.Sponge.indifferentiability_fixedBudget
#print axioms Commons.Sponge.indifferentiability_fixedBudget_of_gameEquivalent
#print axioms Commons.Sponge.indifferentiability_fixedBudget_of_hCoefficient
#print axioms Commons.Sponge.indifferentiability_fixedBudget_tight

end Tests.SpongeIndifferentiability
