import Init.Data.Array.Basic
import Init.Data.Vector.Algebra
import Commons.Schemes.Signature.MLDSA.Arithmetic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.ZMod.Defs
import Commons.Schemes.Lattice.NTTCert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Concrete NTT for ML-DSA

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLDSA/Concrete/NTT.lean` at `f5119c6`), by Quang Dao.

FIPS 204 Algorithms 41, 42 and 45 (NTT, NTT⁻¹, MultiplyNTT), specialized to `q = 8380417`,
`n = 256` and `ζ = 1753`.

The NTT is eight blocked butterfly layers, each computed as a coefficient vector; the inverse runs
the inverse layers in reverse order and normalizes by `256⁻¹`. Complementary bit-reversed twiddles
make the inverse layers cancel the forward ones, so the transforms are mutually inverse. The NTT
evaluates: coordinate `i` of the transform is the input at `ζ^{2·BitRev₈(i)+1}`, so it turns
negacyclic products into pointwise products, and the laws of `NTTRingLaws` follow.

## Main statements

* `invNTT_ntt`, `ntt_invNTT`: the transforms are mutually inverse
* `nttCoeffs_apply`: the NTT evaluates
* `ntt_negacyclicMul`: the NTT is multiplicative
* `concreteNTTRingLaws`: the laws of the NTT ring operations
-/




namespace MLDSA.Concrete

open MLDSA


/-- Reverse the low 8 bits of `i` (FIPS 204: `brv(k)`). -/
def bitRev8 (i : Nat) : Nat :=
  let b := fun k => (i >>> k) &&& 1
  (b 0 <<< 7) ||| (b 1 <<< 6) ||| (b 2 <<< 5) ||| (b 3 <<< 4) |||
  (b 4 <<< 3) ||| (b 5 <<< 2) ||| (b 6 <<< 1) ||| b 7

/-- Precomputed twiddle table: `zetas[k] = ζ^(brv(k))` for `k = 0 .. 255`,
where `brv` is 8-bit reversal per FIPS 204 §4.5.
The forward NTT uses indices `1 .. 255`; the inverse NTT uses the same indices
(negated) in reverse order `255 .. 1`. -/
def zetaTable : Array Coeff :=
  (Array.range 256).map fun i => zeta ^ bitRev8 i

/-- `256⁻¹ mod q`. -/
def nInv : Coeff := ((modulus - (modulus - 1) / ringDegree : ℕ) : Coeff)

/-- Safe array access with fallback to zero. -/
def getZ (a : Array Coeff) (i : Nat) : Coeff := a.getD i 0

theorem bitRev8_layer_partner :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      bitRev8 (2 ^ s.val + g.val) +
          bitRev8 (2 ^ (s.val + 1) - 1 - g.val) = 256 := by
  intro s g
  fin_cases s <;> fin_cases g <;> rfl

theorem layer_twiddle_index_bounds :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      2 ^ s.val + g.val < 256 ∧
        2 ^ (s.val + 1) - 1 - g.val < 256 := by
  intro s g
  fin_cases s <;> fin_cases g <;> norm_num

theorem getZ_zetaTable (i : Nat) (hi : i < 256) :
    getZ zetaTable i = zeta ^ bitRev8 i := by
  simp [getZ, zetaTable, hi]

theorem zeta_pow_256 : (zeta : Coeff) ^ 256 = -1 := by
  change (1753 : ZMod 8380417) ^ 256 = -1
  reduce_mod_char

/-- `ζ = 1753` is a primitive `512`-th root of unity in `ℤ_q` (FIPS 204 §7.5): the twiddle half
of the NTT correctness argument. -/
theorem zeta_isPrimitiveRoot : IsPrimitiveRoot (zeta : Coeff) 512 := by
  change IsPrimitiveRoot (1753 : ZMod 8380417) 512
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by reduce_mod_char) ?_
  intro p hp hdvd
  obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 9 by simpa using hdvd))
  reduce_mod_char
  exact ne_of_beq_false rfl

/-- Forward and complementary inverse-table twiddles in one layer multiply to `-1`. -/
theorem zetaTable_layer_partner :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      getZ zetaTable (2 ^ s.val + g.val) *
          getZ zetaTable (2 ^ (s.val + 1) - 1 - g.val) = -1 := by
  intro s g
  obtain ⟨hforward, hinverse⟩ := layer_twiddle_index_bounds s g
  rw [getZ_zetaTable _ hforward, getZ_zetaTable _ hinverse, ← pow_add]
  rw [bitRev8_layer_partner s g, zeta_pow_256]

theorem layer_shape :
    ∀ s : Fin 8, 2 ^ s.val * (2 * (128 / 2 ^ s.val)) = polyBackend.degree := by
  intro s
  fin_cases s <;> rfl

abbrev NTTCoord := Fin polyBackend.degree

def layerLayout (s : Fin 8) :
    LatticeCrypto.NTTCert.ButterflyLayout
      (Fin (2 ^ s.val) × Fin (128 / 2 ^ s.val)) NTTCoord where
  equiv := (LatticeCrypto.NTTCert.blockLayout (2 ^ s.val) (128 / 2 ^ s.val)).equiv.trans
    (finCongr (layer_shape s))

def nttStage (s : Fin 8) :
    LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord :=
  LatticeCrypto.NTTCert.butterflyStage (layerLayout s)
    (fun pair => getZ zetaTable (2 ^ s.val + pair.1.val))
    (fun pair => -getZ zetaTable (2 ^ (s.val + 1) - 1 - pair.1.val))
    (by
      intro pair
      have h := zetaTable_layer_partner s pair.1
      calc
        -getZ zetaTable (2 ^ (s.val + 1) - 1 - pair.1.val) *
            getZ zetaTable (2 ^ s.val + pair.1.val) =
          -(getZ zetaTable (2 ^ s.val + pair.1.val) *
            getZ zetaTable (2 ^ (s.val + 1) - 1 - pair.1.val)) := by ring
        _ = -(-1) := by rw [h]
        _ = 1 := by ring)

def nttStages :
    List (LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord) :=
  [nttStage 0, nttStage 1, nttStage 2, nttStage 3,
    nttStage 4, nttStage 5, nttStage 6, nttStage 7]

theorem nInv_stageScalar :
    nInv * LatticeCrypto.NTTCert.stageScalar nttStages = 1 := by
  change ((8347681 * 256 : Nat) : ZMod 8380417) = ((1 : Nat) : ZMod 8380417)
  rw [ZMod.natCast_eq_natCast_iff']

def nttCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.forwardStages nttStages input

def invNTTCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.scaleCoeffs nInv
    (LatticeCrypto.NTTCert.inverseStages nttStages input)

theorem invNTTCoeffs_nttCoeffs (input : NTTCoord → Coeff) :
    invNTTCoeffs (nttCoeffs input) = input := by
  unfold invNTTCoeffs nttCoeffs
  exact LatticeCrypto.NTTCert.scale_inverseStages_forwardStages
    nttStages nInv nInv_stageScalar input

theorem nttCoeffs_add (left right : NTTCoord → Coeff) :
    nttCoeffs (left + right) = nttCoeffs left + nttCoeffs right := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_add nttStages left right

theorem nttCoeffs_sub (left right : NTTCoord → Coeff) :
    nttCoeffs (left - right) = nttCoeffs left - nttCoeffs right := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_sub nttStages left right

theorem nttCoeffs_zero : nttCoeffs 0 = 0 := by
  unfold nttCoeffs
  exact LatticeCrypto.NTTCert.forwardStages_zero nttStages

/-! ### Evaluation

After `s` layers, each group `g` of `2^(8-s)` coefficients evaluates like the input at the roots
of its modulus `X^(256/2^s) - ζ^e`, with `e = 2·BitRev₈(2^s + g)`; after all eight, coordinate `i`
is the input at `ζ^{2·BitRev₈(i)+1}`, a root of `X^256 + 1`, so the NTT turns negacyclic products
into pointwise products. -/

theorem layerLayout_left_val (s : Fin 8) (g : Fin (2 ^ s.val)) (j : Fin (128 / 2 ^ s.val)) :
    ((layerLayout s).equiv ((g, j), false)).val = g.val * (2 * (128 / 2 ^ s.val)) + j.val := by
  simp [layerLayout]

theorem layerLayout_right_val (s : Fin 8) (g : Fin (2 ^ s.val)) (j : Fin (128 / 2 ^ s.val)) :
    ((layerLayout s).equiv ((g, j), true)).val =
      g.val * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + j.val := by
  simp [layerLayout]

/-- The exponent of the root at which group `g` evaluates after `s` layers; after all eight,
coordinate `i` evaluates at `ζ^{2·BitRev₈(i)+1}`. -/
def rootExponent (s g : ℕ) : ℕ :=
  if s < 8 then 2 * bitRev8 (2 ^ s + g) else 2 * bitRev8 g + 1

theorem rootExponent_children :
    ∀ (s : Fin 8) (g : Fin (2 ^ s.val)),
      rootExponent (s.val + 1) (2 * g.val) % 512 = bitRev8 (2 ^ s.val + g.val) % 512 ∧
      rootExponent (s.val + 1) (2 * g.val + 1) % 512 = (bitRev8 (2 ^ s.val + g.val) + 256) % 512 := by
  intro s g
  fin_cases s <;> fin_cases g <;> exact ⟨rfl, rfl⟩

theorem zeta_pow_mod (a : ℕ) : (zeta : Coeff) ^ a = zeta ^ (a % 512) := by
  conv_lhs => rw [← Nat.mod_add_div a 512]
  rw [pow_add, pow_mul, zeta_isPrimitiveRoot.pow_eq_one, one_pow, mul_one]

/-- **The evaluation invariant after `s` layers**: each group of `a`, of length `256 / 2 ^ s`,
evaluates like `f` at every root of its modulus, in every algebra over the coefficients. -/
def EvalInvariant (s : ℕ) (a f : NTTCoord → Coeff) : Prop :=
  ∀ g < 2 ^ s, ∀ (S : Type) [CommRing S] [Algebra Coeff S] (ω : S),
    ω ^ (256 / 2 ^ s) = algebraMap Coeff S (zeta ^ rootExponent s g) →
      LatticeCrypto.NTTCert.segmentEval a (g * (256 / 2 ^ s)) (256 / 2 ^ s) ω = LatticeCrypto.NTTCert.segmentEval f 0 256 ω

theorem evalInvariant_zero (f : NTTCoord → Coeff) : EvalInvariant 0 f f := by
  intro g hg S _ _ ω _
  obtain rfl : g = 0 := by simpa using hg
  simp

/-- **One layer preserves the invariant.** -/
theorem evalInvariant_step (s : Fin 8) {a f : NTTCoord → Coeff} (h : EvalInvariant s.val a f) :
    EvalInvariant (s.val + 1) ((nttStage s).forward a) f := by
  intro g' hg' S _ _ ω hω
  have hB : 256 / 2 ^ s.val = 2 * (128 / 2 ^ s.val) := by fin_cases s <;> rfl
  have hB' : 256 / 2 ^ (s.val + 1) = 128 / 2 ^ s.val := by fin_cases s <;> rfl
  obtain ⟨g, c, hc, rfl⟩ : ∃ g c, c < 2 ∧ g' = 2 * g + c :=
    ⟨g' / 2, g' % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod g' 2).symm⟩
  have hg : g < 2 ^ s.val := by rw [pow_succ] at hg'; omega
  have hbounds := (layer_twiddle_index_bounds s ⟨g, hg⟩).1
  obtain ⟨hc0, hc1⟩ := rootExponent_children s ⟨g, hg⟩
  simp only at hc0 hc1 hbounds
  have hz : getZ zetaTable (2 ^ s.val + g) = zeta ^ bitRev8 (2 ^ s.val + g) :=
    getZ_zetaTable _ hbounds
  have hstage : (nttStage s).forward a =
      LatticeCrypto.NTTCert.forwardStage (layerLayout s) (fun pair => getZ zetaTable (2 ^ s.val + pair.1.val)) a := rfl
  have hl : ∀ j < 128 / 2 ^ s.val, LatticeCrypto.NTTCert.coeffAt ((nttStage s).forward a) (g * (2 * (128 / 2 ^ s.val)) + j) =
      LatticeCrypto.NTTCert.coeffAt a (g * (2 * (128 / 2 ^ s.val)) + j) + getZ zetaTable (2 ^ s.val + g) *
        LatticeCrypto.NTTCert.coeffAt a (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + j) := by
    intro j hj
    rw [hstage]
    exact (LatticeCrypto.NTTCert.forwardStage_coeffAt (layerLayout s) (layerLayout_left_val s) (layerLayout_right_val s)
      (fun pair => getZ zetaTable (2 ^ s.val + pair.1.val)) a ⟨g, hg⟩ ⟨j, hj⟩).1
  have hr : ∀ j < 128 / 2 ^ s.val,
      LatticeCrypto.NTTCert.coeffAt ((nttStage s).forward a) (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + j) =
      LatticeCrypto.NTTCert.coeffAt a (g * (2 * (128 / 2 ^ s.val)) + j) - getZ zetaTable (2 ^ s.val + g) *
        LatticeCrypto.NTTCert.coeffAt a (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + j) := by
    intro j hj
    rw [hstage]
    exact (LatticeCrypto.NTTCert.forwardStage_coeffAt (layerLayout s) (layerLayout_left_val s) (layerLayout_right_val s)
      (fun pair => getZ zetaTable (2 ^ s.val + pair.1.val)) a ⟨g, hg⟩ ⟨j, hj⟩).2
  have hbf := LatticeCrypto.NTTCert.segmentEval_butterfly (S := S) a ((nttStage s).forward a)
    (g * (2 * (128 / 2 ^ s.val))) (128 / 2 ^ s.val) (getZ zetaTable (2 ^ s.val + g)) hl hr ω
  have hparent : ω ^ (128 / 2 ^ s.val) = algebraMap Coeff S (getZ zetaTable (2 ^ s.val + g)) ∨
      ω ^ (128 / 2 ^ s.val) = -algebraMap Coeff S (getZ zetaTable (2 ^ s.val + g)) →
      ω ^ (256 / 2 ^ s.val) = algebraMap Coeff S (zeta ^ rootExponent s.val g) := by
    rintro (hω' | hω') <;>
    · rw [hB, pow_mul', hω', rootExponent, if_pos s.isLt, pow_mul', hz]
      simp [map_pow]
  rw [hB'] at hω ⊢
  interval_cases c
  · simp only [add_zero] at hω ⊢
    have hω' : ω ^ (128 / 2 ^ s.val) = algebraMap Coeff S (getZ zetaTable (2 ^ s.val + g)) := by
      rw [hω, zeta_pow_mod, hc0, ← zeta_pow_mod, hz]
    rw [show 2 * g * (128 / 2 ^ s.val) = g * (2 * (128 / 2 ^ s.val)) by ring,
      hbf.1 hω', ← hB]
    exact h g hg S ω (hparent (Or.inl hω'))
  · have hω' : ω ^ (128 / 2 ^ s.val) = -algebraMap Coeff S (getZ zetaTable (2 ^ s.val + g)) := by
      rw [hω, zeta_pow_mod, hc1, ← zeta_pow_mod, pow_add, zeta_pow_256, hz]
      simp [map_neg]
    rw [show (2 * g + 1) * (128 / 2 ^ s.val) =
        g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val by ring, hbf.2 hω', ← hB]
    exact h g hg S ω (hparent (Or.inr hω'))

/-- The invariant after all eight layers. -/
theorem evalInvariant_nttCoeffs (f : NTTCoord → Coeff) : EvalInvariant 8 (nttCoeffs f) f := by
  have h1 := evalInvariant_step 0 (evalInvariant_zero f)
  have h2 := evalInvariant_step 1 h1
  have h3 := evalInvariant_step 2 h2
  have h4 := evalInvariant_step 3 h3
  have h5 := evalInvariant_step 4 h4
  have h6 := evalInvariant_step 5 h5
  have h7 := evalInvariant_step 6 h6
  exact evalInvariant_step 7 h7

/-- **The NTT evaluates** (FIPS 204, §7.5): coordinate `i` of `nttCoeffs f` is `f` at
`ζ^{2·BitRev₈(i)+1}`. -/
theorem nttCoeffs_apply (f : NTTCoord → Coeff) (i : NTTCoord) :
    nttCoeffs f i =
      LatticeCrypto.NTTCert.segmentEval f 0 256 (zeta ^ (2 * bitRev8 i.val + 1)) := by
  have h := evalInvariant_nttCoeffs f i.val i.isLt Coeff
    (zeta ^ (2 * bitRev8 i.val + 1)) (by simp [rootExponent])
  rw [← h]
  simp [LatticeCrypto.NTTCert.segmentEval, LatticeCrypto.NTTCert.coeffAt]

/-- The roots of the NTT satisfy `ω ^ 256 = -1`. -/
theorem nttRoot_pow_256 (i : ℕ) : ((zeta : Coeff) ^ (2 * bitRev8 i + 1)) ^ 256 = -1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta_pow_256, (odd_two_mul_add_one _).neg_one_pow]

/-- **The NTT turns negacyclic products into pointwise products.** -/
theorem nttCoeffs_negacyclicConv (f g : NTTCoord → Coeff) (i : NTTCoord) :
    nttCoeffs (fun k => LatticeCrypto.negacyclicConvCoeff f g k) i = nttCoeffs f i * nttCoeffs g i := by
  rw [nttCoeffs_apply, nttCoeffs_apply, nttCoeffs_apply]
  exact LatticeCrypto.NTTCert.segmentEval_negacyclicConv f g _ (nttRoot_pow_256 i.val)

/-- **The NTT** (FIPS 204 Algorithm 41): the eight butterfly layers, each computed as a
coefficient vector. -/
def ntt (f : Rq) : Tq :=
  ⟨polyBackend.build
    (LatticeCrypto.NTTCert.forwardStagesVec nttStages (Vector.ofFn (polyBackend.coeff f))).get⟩

/-- **The inverse NTT**: the inverse layers in reverse order, each computed as a coefficient
vector, and the normalization by `n⁻¹`. -/
def invNTT (fHat : Tq) : Rq :=
  polyBackend.build (LatticeCrypto.NTTCert.scaleCoeffs nInv
    (LatticeCrypto.NTTCert.inverseStagesVec nttStages
      (Vector.ofFn (polyBackend.coeff fHat.coeffs))).get)

/-- The NTT is the stage composite `nttCoeffs` on coefficient functions. -/
theorem ntt_eq (f : Rq) :
    ntt f = ⟨LatticeCrypto.NTTCert.applyCoeffTransform polyBackend nttCoeffs f⟩ := by
  simp only [ntt, LatticeCrypto.NTTCert.applyCoeffTransform, nttCoeffs,
    LatticeCrypto.NTTCert.forwardStagesVec_get, LatticeCrypto.NTTCert.get_ofFn]

/-- The inverse NTT is the stage composite `invNTTCoeffs` on coefficient functions. -/
theorem invNTT_eq (fHat : Tq) :
    invNTT fHat = LatticeCrypto.NTTCert.applyCoeffTransform polyBackend invNTTCoeffs fHat.coeffs := by
  simp only [invNTT, LatticeCrypto.NTTCert.applyCoeffTransform, invNTTCoeffs,
    LatticeCrypto.NTTCert.inverseStagesVec_get, LatticeCrypto.NTTCert.get_ofFn]

/-- **MultiplyNTT** (FIPS 204 Algorithm 45): the pointwise product in the NTT domain. -/
def multiplyNTT (fHat gHat : Tq) : Tq :=
  ⟨polyBackend.build fun i => polyBackend.coeff fHat.coeffs i * polyBackend.coeff gHat.coeffs i⟩

/-- The concrete inverse transform is a left inverse to the concrete forward transform. -/
theorem invNTT_ntt (f : Rq) : invNTT (ntt f) = f := by
  rw [invNTT_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_comp
    nttCoeffs invNTTCoeffs invNTTCoeffs_nttCoeffs f

def rqEquivCoeffFun : Rq ≃ (Fin ringDegree → Coeff) where
  toFun f i := f.get i
  invFun f := Vector.ofFn f
  left_inv f := by
    apply Vector.ext
    intro i hi
    exact Vector.getElem_ofFn (f := fun i => f.get i) hi
  right_inv f := by
    funext i
    exact Vector.get_ofFn f i

def rqEquivTq : Rq ≃ Tq where
  toFun f := ⟨f⟩
  invFun fHat := fHat.coeffs
  left_inv _ := rfl
  right_inv fHat := by cases fHat; rfl

theorem ntt_injective : Function.Injective ntt := by
  intro f g h
  have hInv := congrArg invNTT h
  simpa [invNTT_ntt] using hInv

theorem ntt_surjective : Function.Surjective ntt := by
  let : NeZero modulus := ⟨by norm_num [modulus]⟩
  let : Fintype Coeff := by
    dsimp [Coeff]
    exact ZMod.fintype modulus
  let : Finite Rq := Finite.of_equiv (Fin ringDegree → Coeff) rqEquivCoeffFun.symm
  exact ntt_injective.surjective_of_finite rqEquivTq

/-- The concrete forward transform is a left inverse to the concrete inverse transform. -/
theorem ntt_invNTT (fHat : Tq) : ntt (invNTT fHat) = fHat := by
  obtain ⟨f, hf⟩ := ntt_surjective fHat
  calc
    ntt (invNTT fHat) = ntt (invNTT (ntt f)) := by rw [hf]
    _ = ntt f := by rw [invNTT_ntt]
    _ = fHat := hf

theorem hadd_rq (f g : Rq) :
    polyBackend.coeff (f + g) = polyBackend.coeff f + polyBackend.coeff g := by
  funext i
  change ((LatticeCrypto.vectorNegacyclicRing Coeff ringDegree).add f g).get i = f.get i + g.get i
  simp

theorem hsub_rq (f g : Rq) :
    polyBackend.coeff (f - g) = polyBackend.coeff f - polyBackend.coeff g := by
  funext i
  change ((LatticeCrypto.vectorNegacyclicRing Coeff ringDegree).sub f g).get i = f.get i - g.get i
  simp

theorem hzero_rq : polyBackend.coeff (0 : Rq) = 0 := by
  funext i
  exact LatticeCrypto.vectorRing_zero_get i

/-- The concrete NTT is additive. -/
theorem ntt_add_toRq (f g : Rq) : (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_add nttCoeffs hadd_rq nttCoeffs_add f g

/-- The concrete NTT is additive. -/
theorem ntt_add (f g : Rq) : ntt (f + g) = ntt f + ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq)
  exact ntt_add_toRq f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub_toRq (f g : Rq) : (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_sub nttCoeffs hsub_rq nttCoeffs_sub f g

/-- The concrete NTT preserves subtraction. -/
theorem ntt_sub (f g : Rq) : ntt (f - g) = ntt f - ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq)
  exact ntt_sub_toRq f g

theorem invNTT_add (g h : Tq) : invNTT (g + h) = invNTT g + invNTT h := by
  apply ntt_injective
  rw [ntt_invNTT, ntt_add, ntt_invNTT, ntt_invNTT]

theorem invNTT_sub (g h : Tq) : invNTT (g - h) = invNTT g - invNTT h := by
  apply ntt_injective
  rw [ntt_invNTT, ntt_sub, ntt_invNTT, ntt_invNTT]

theorem negacyclicMul_coeff (a b : Rq) (k : Fin ringDegree) :
    polyBackend.coeff (negacyclicMul a b) k =
      LatticeCrypto.negacyclicConvCoeff (polyBackend.coeff a) (polyBackend.coeff b) k :=
  LatticeCrypto.negacyclicMul_coeff polyBackend a b k

/-- **The NTT is multiplicative**: it turns negacyclic products into pointwise products. -/
theorem ntt_negacyclicMul (f g : Rq) : ntt (negacyclicMul f g) = multiplyNTT (ntt f) (ntt g) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  apply LatticeCrypto.TransformPoly.ext
  show polyBackend.build (nttCoeffs (polyBackend.coeff (negacyclicMul f g))) =
    polyBackend.build fun i => polyBackend.coeff (polyBackend.build (nttCoeffs (polyBackend.coeff f))) i *
      polyBackend.coeff (polyBackend.build (nttCoeffs (polyBackend.coeff g))) i
  refine congrArg polyBackend.build (funext fun i => ?_)
  rw [polyBackend.coeff_build, polyBackend.coeff_build,
    show polyBackend.coeff (negacyclicMul f g) = fun k => LatticeCrypto.negacyclicConvCoeff
      (polyBackend.coeff f) (polyBackend.coeff g) k from funext (negacyclicMul_coeff f g)]
  exact nttCoeffs_negacyclicConv _ _ i

/-- The pointwise product is the negacyclic product transported through the NTT. -/
theorem multiplyNTT_eq (fHat gHat : Tq) :
    multiplyNTT fHat gHat = ntt (negacyclicMul (invNTT fHat) (invNTT gHat)) := by
  rw [ntt_negacyclicMul, ntt_invNTT, ntt_invNTT]

/-- Concrete `NTTRingOps` instance for ML-DSA. -/
@[reducible] def concreteNTTRingOps : NTTRingOps where
  toHat := ntt
  fromHat := invNTT
  mulHat := multiplyNTT

/-- Proof-oriented algebraic laws for the ML-DSA concrete NTT. -/
theorem concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  fromHat_toHat := invNTT_ntt
  toHat_fromHat := ntt_invNTT
  toHat_zero := by
    apply LatticeCrypto.TransformPoly.ext
    show (ntt 0).coeffs = _
    rw [ntt_eq]
    exact LatticeCrypto.NTTCert.applyCoeffTransform_zero nttCoeffs hzero_rq nttCoeffs_zero
  toHat_mul f g := ntt_negacyclicMul f g
  toHat_add f g := ntt_add f g
  toHat_sub f g := ntt_sub f g
  mul_add f g h := by
    change multiplyNTT f (g + h) = multiplyNTT f g + multiplyNTT f h
    simp only [multiplyNTT_eq, invNTT_add]
    rw [← ntt_add]
    exact congrArg ntt (LatticeCrypto.vectorRing_mul_add_right
      (Coeff := Coeff) (n := ringDegree) _ _ _)
  mul_sub f g h := by
    change multiplyNTT f (g - h) = multiplyNTT f g - multiplyNTT f h
    simp only [multiplyNTT_eq, invNTT_sub]
    rw [← ntt_sub]
    exact congrArg ntt (LatticeCrypto.vectorRing_mul_sub_right
      (Coeff := Coeff) (n := ringDegree) _ _ _)
  mul_comm f g := by
    change multiplyNTT f g = multiplyNTT g f
    simp only [multiplyNTT_eq, LatticeCrypto.vectorRing_mul_comm]
  mul_assoc f g h := by
    change multiplyNTT (multiplyNTT f g) h = multiplyNTT f (multiplyNTT g h)
    simp only [multiplyNTT_eq, invNTT_ntt]
    exact congrArg ntt (mul_assoc (invNTT f) (invNTT g) (invNTT h))

end MLDSA.Concrete
