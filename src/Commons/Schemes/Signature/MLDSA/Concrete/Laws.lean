import Commons.Schemes.Signature.MLDSA.Signature
import Commons.Schemes.Signature.MLDSA.Concrete.Instance

/-!
# Laws of the Concrete ML-DSA Primitives

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLDSA/Concrete/LawBounds.lean` and `Extern/MLDSA/Laws.lean` at `f5119c6`), by Quang Dao, Oleksandr Vovkotrub.

The concrete FIPS 204 primitives satisfy `MLDSA.Primitives.Laws` at every approved parameter set,
so concrete ML-DSA is correct: a signature that does not abort verifies. The rounding and NTT
fields come from `Concrete.Rounding` and `Concrete.NTT`; the encoding fields from the decode
ranges of `Concrete.Encoding`; the sampler fields from the fuel induction of `Concrete.Sampling`;
and the challenge-product bound `‖c·s‖∞ ≤ τ·η = β` from the convolution bound
`‖f·g‖∞ ≤ ‖f‖₁·‖g‖∞` with `‖SampleInBall(c̃)‖₁ ≤ τ`.

## Main statements

* `MLDSA.Concrete.concretePrimitives_laws`: the laws of the concrete primitives
* `MLDSA.Concrete.fipsSign_fipsVerify`: correctness of concrete ML-DSA
-/

namespace MLDSA.Concrete

open MLDSA LatticeCrypto

attribute [local instance] concreteNTTRingOps

variable (p : Params)

/-- `Primitives.Laws.transform` for the concrete instance. -/
theorem concrete_transform : NTTRingLaws concreteNTTRingOps :=
  concreteNTTRingLaws

/-! ## Bit-width fit for the `w₁` packer

The concrete `w1Encode` packs each `High` coefficient via `simpleBitPackPoly` at the bit width
`simpleWidth ((q-1)/(2γ₂) - 1)`. On the valid commitment range — every component an actual
`highBits` output — each coefficient lies in `[0, (q-1)/(2γ₂) - 1]` (`highBits_coeff_val_lt_m`),
which fits in that bit width, so the packer is inverted by `simpleBitUnpackPoly` and is injective
there. -/

/-- Every approved-parameter `highBits` coefficient fits in the `w₁` packer's bit width. -/
theorem highBits_coeff_val_lt_width (hp : p.isApproved) (r : Rq) (c : Fin ringDegree) :
    ((MLDSA.Concrete.highBits p r).get c).val
      < 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) := by
  have hlt : ((MLDSA.Concrete.highBits p r).get c).val < (modulus - 1) / (2 * p.gamma2) :=
    MLDSA.Concrete.highBits_coeff_val_lt_m p hp r c
  -- `(q-1)/(2γ₂) ≤ 2 ^ simpleWidth ((q-1)/(2γ₂) - 1)`.
  have hwin : (modulus - 1) / (2 * p.gamma2)
      ≤ 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) := by
    rcases hp with rfl | rfl | rfl <;> exact Nat.le_of_ble_eq_true rfl
  omega


/-! ## Provable algebraic fields (banked) -/

/-- `Primitives.Laws.high_low_decomp` for the concrete instance. -/
theorem concrete_high_low_decomp (r : Rq) :
    (concretePrimitives p).highBitsShift ((concretePrimitives p).highBits r)
      + (concretePrimitives p).lowBits r = r :=
  concreteRounding_high_low_decomp p r

/-- `Primitives.Laws.lowBits_bound` for the concrete instance (approved parameters). -/
theorem concrete_lowBits_bound (hp : p.isApproved) (r : Rq) :
    polyNorm ((concretePrimitives p).lowBits r) ≤ p.gamma2 := by
  rw [polyNorm_eq_cInfNorm]
  exact concreteRounding_lowBits_bound p (by rcases hp with rfl | rfl | rfl <;> norm_num [mldsa44, mldsa65, mldsa87, ParameterSet.params, modulus])
    (by rcases hp with rfl | rfl | rfl <;> norm_num [mldsa44, mldsa65, mldsa87, ParameterSet.params, modulus]) r

/-- `Primitives.Laws.hide_low` for the concrete instance (approved parameters). -/
theorem concrete_hide_low (hp : p.isApproved) (r s : Rq) (b : ℕ)
    (hs : polyNorm s ≤ b)
    (hlow : polyNorm ((concretePrimitives p).lowBits r) + b < p.gamma2) :
    (concretePrimitives p).highBits (r + s) = (concretePrimitives p).highBits r := by
  apply concreteRounding_hide_low_of_isApproved p hp r s b
  · rwa [← polyNorm_eq_cInfNorm]
  · rw [← polyNorm_eq_cInfNorm]; exact hlow

/-- `Primitives.Laws.highBitsShift_injective` for the concrete instance (approved parameters). -/
theorem concrete_highBitsShift_injective (hp : p.isApproved) :
    Function.Injective (concretePrimitives p).highBitsShift :=
  highBitsShift_injective_of_isApproved p hp

/-- `Primitives.Laws.useHint_makeHint` for the concrete instance (approved parameters). -/
theorem concrete_useHint_makeHint (hp : p.isApproved) (z r : Rq) (hz : polyNorm z ≤ p.gamma2) :
    (concretePrimitives p).useHint ((concretePrimitives p).makeHint z r) r
      = (concretePrimitives p).highBits (r + z) := by
  apply concreteRounding_useHint_correct_of_isApproved p hp z r
  rwa [← polyNorm_eq_cInfNorm]

/-- `Primitives.Laws.power2Round_decomp` for the concrete instance. -/
theorem concrete_power2Round_decomp (r : Rq) :
    (concretePrimitives p).power2RoundShift ((concretePrimitives p).power2Round r).1
      + ((concretePrimitives p).power2Round r).2 = r :=
  concretePower2Round_high_low_decomp r

/-- `Primitives.Laws.power2Round_bound` for the concrete instance. -/
theorem concrete_power2Round_bound (r : Rq) :
    polyNorm ((concretePrimitives p).power2Round r).2 ≤ 2 ^ (droppedBits - 1) := by
  rw [polyNorm_eq_cInfNorm]
  change LatticeCrypto.cInfNorm (power2RoundLow r) ≤ 2 ^ (droppedBits - 1)
  rw [← concretePower2Round_remainder_eq_low]
  exact concretePower2Round_bound r

/-! ## `expandMask_bound` at the FIPS-204 `z`-range

The concrete `expandMask` decodes each coefficient through `polyZUnpack p`. The decode-range bound
`bitUnpackPoly_z_cInfNorm_le` holds for any byte input, so it applies to the opaque SHAKE stream
after generalizing the byte argument; the two side conditions on the `z`-range bit width come from
`approved_gamma1_width`. -/

/-- `Primitives.Laws.expandMask_bound` (bound `γ₁`) for the concrete instance, at any
approved parameter set. -/
theorem concrete_expandMask_bound (hp : p.isApproved) (rhoDoublePrime : Bytes 64) (kappa : ℕ) :
    polyVecBounded ((concretePrimitives p).expandMask rhoDoublePrime kappa) p.gamma1 := by
  rw [polyVecBounded, polyVecNorm, LatticeCrypto.PolyVec.cInfNorm_le_iff]
  intro j
  change polyNorm ((MLDSA.Concrete.expandMask rhoDoublePrime kappa p).get j) ≤ p.gamma1
  rw [polyNorm_eq_cInfNorm]
  exact MLDSA.Concrete.expandMask_get_cInfNorm_le p hp rhoDoublePrime kappa j

/-! ## `w1Encode_injective` as `Set.InjOn` on the valid range

On the valid commitment range — every component an actual `highBits` output — each coefficient fits
in the `w₁` packer's bit width (`highBits_coeff_val_lt_width`), so the packer is inverted by
`simpleBitUnpackPoly` and is injective. This is exactly the `Set.InjOn` predicate of the abstract
field, since the abstract validity set is the image of `highBits`. -/

/-- `Primitives.Laws.w1Encode_injective` for the concrete instance, at any
approved parameter set: `w1Encode` is injective on commitment vectors all of whose components are
`highBits` outputs. -/
theorem concrete_w1Encode_injOn (hp : p.isApproved) :
    Set.InjOn (concretePrimitives p).w1Encode
      { w : Vector (concretePrimitives p).High p.k |
          ∀ i : Fin p.k, w.get i ∈ Set.range (concretePrimitives p).highBits } := by
  -- The concrete validity set sits inside the bit-width set on which `w1Encode_injOn` applies.
  apply Set.InjOn.mono (s₂ := { w : Vector High p.k | ∀ i : Fin p.k, ∀ c : Fin ringDegree,
      ((w.get i).get c).val
        < 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) })
  · intro w hw i c
    obtain ⟨r, hr⟩ := hw i
    rw [show w.get i = MLDSA.Concrete.highBits p r from hr.symm]
    exact highBits_coeff_val_lt_width p hp r c
  · exact MLDSA.Concrete.w1Encode_injOn p

/-! ## Sampler-bound fields from the fuel-recursive samplers

The `sampleInBall` and `expandS` rejection samplers are defined by fuel-bounded structural recursion
(see `Commons.Schemes.Signature.MLDSA.Concrete.Sampling`), which exposes equation lemmas. Their structural output ranges
are banked as `sampleInBall_norm` and `expandS_bound` there; the `concrete_*` wrappers below state
them at the `concretePrimitives` interface. -/

/-- `Primitives.Laws.sampleInBall_norm` for the concrete instance: `SampleInBall(c̃)` has centered
infinity norm at most `1` (its coefficients lie in `{-1, 0, +1}`). -/
theorem concrete_sampleInBall_norm (cTilde : CommitHashBytes p) :
    polyNorm ((concretePrimitives p).sampleInBall cTilde) ≤ 1 :=
  MLDSA.Concrete.sampleInBall_norm p cTilde

/-- `Primitives.Laws.expandS_bound` for the concrete instance: `ExpandS(ρ')` produces secret vectors
with every coefficient bounded by `η`. -/
theorem concrete_expandS_bound (rhoPrime : Bytes 64) :
    polyVecBounded ((concretePrimitives p).expandS rhoPrime).1 p.eta ∧
      polyVecBounded ((concretePrimitives p).expandS rhoPrime).2 p.eta :=
  MLDSA.Concrete.expandS_bound rhoPrime p

/-- `Primitives.Laws.sampleInBall_smul_bound` for the concrete instance: the challenge–secret
product `c · sⱼ` has centered infinity norm at most `β = τ · η` whenever `‖s‖∞ ≤ η`. Assembled from
the generic negacyclic-convolution bound `‖c · sⱼ‖∞ ≤ ‖c‖₁ · ‖sⱼ‖∞` (`cInfNorm_mul_le`), the
challenge `ℓ₁` count `‖SampleInBall(c̃)‖₁ ≤ τ` (`sampleInBall_l1Norm`), and the component law
`(c • s).get j = c * sⱼ` (`coeffScalarVecMul_get`). -/
theorem concrete_sampleInBall_smul_bound
    (cTilde : CommitHashBytes p) {k : ℕ} (s : RqVec k)
    (hs : polyVecBounded s p.eta) :
    polyVecNorm (concreteNTTRingOps.coeffScalarVecMul
      ((concretePrimitives p).sampleInBall cTilde) s) ≤ p.beta := by
  rw [polyVecNorm, LatticeCrypto.PolyVec.cInfNorm_le_iff]
  intro j
  rw [LatticeCrypto.TransformOps.coeffScalarVecMul_get (laws := concreteNTTRingLaws)]
  change polyNorm _ ≤ p.beta
  rw [polyNorm_eq_cInfNorm]
  have hc : (concretePrimitives p).sampleInBall cTilde = MLDSA.Concrete.sampleInBall p cTilde := rfl
  rw [hc]
  refine le_trans
    (LatticeCrypto.cInfNorm_mul_le (MLDSA.Concrete.sampleInBall p cTilde) (s.get j)) ?_
  have hl1 : LatticeCrypto.l1Norm (MLDSA.Concrete.sampleInBall p cTilde) ≤ p.tau :=
    MLDSA.Concrete.sampleInBall_l1Norm p cTilde
  have hsj : LatticeCrypto.cInfNorm (s.get j) ≤ p.eta := by
    have := (LatticeCrypto.PolyVec.cInfNorm_le_iff (ops := normOps)).mp hs j
    rwa [← polyNorm_eq_cInfNorm]
  calc LatticeCrypto.l1Norm (MLDSA.Concrete.sampleInBall p cTilde)
        * LatticeCrypto.cInfNorm (s.get j)
      ≤ p.tau * p.eta := Nat.mul_le_mul hl1 hsj
    _ = p.beta := rfl

/-! ## The laws and correctness -/

/-- **The laws of the concrete ML-DSA primitives**, at every approved parameter set. -/
theorem concretePrimitives_laws (hp : p.isApproved) :
    Primitives.Laws (concretePrimitives p) concreteNTTRingOps where
  sampleInBall_norm := concrete_sampleInBall_norm p
  expandS_bound := concrete_expandS_bound p
  expandMask_bound := concrete_expandMask_bound p hp
  transform := concrete_transform
  high_low_decomp := concrete_high_low_decomp p
  lowBits_bound := concrete_lowBits_bound p hp
  hide_low := concrete_hide_low p hp
  highBitsShift_injective := concrete_highBitsShift_injective p hp
  useHint_makeHint := concrete_useHint_makeHint p hp
  power2Round_decomp := concrete_power2Round_decomp p
  power2Round_bound := concrete_power2Round_bound p
  w1Encode_injective := concrete_w1Encode_injOn p hp
  sampleInBall_smul_bound := concrete_sampleInBall_smul_bound p

/-- **Correctness of ML-DSA**: at an approved parameter set, a signature of `M'` under the key
pair generated from any seed `ξ`, with any randomness `rnd`, verifies unless signing aborted. -/
theorem fipsSign_fipsVerify (hp : p.isApproved) (seed : Bytes 32) (msg : List Byte)
    (rnd : Bytes 32) (maxAttempts : ℕ) (sig : FIPSSignature p (concretePrimitives p))
    (h : fipsSign p (concretePrimitives p)
      (keyGenFromSeed p (concretePrimitives p) seed).2
      msg rnd maxAttempts = some sig) :
    fipsVerify p (concretePrimitives p)
      (keyGenFromSeed p (concretePrimitives p) seed).1
      msg sig = true :=
  fipsSign_fipsVerify_correct p (concretePrimitives p) _ _ msg
    sig _ maxAttempts (keyGenFromSeed_validKeyPair p (concretePrimitives p) seed)
    (concretePrimitives_laws p hp) h

end MLDSA.Concrete
