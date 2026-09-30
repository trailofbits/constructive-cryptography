import Init.Data.Array.Basic
import Init.Data.Vector.Algebra
import Commons.Schemes.KEM.MLKEM.Arithmetic
import Mathlib.Tactic.ReduceModChar
import Commons.Schemes.KEM.MLKEM.Params
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.ZMod.Defs
import Commons.Schemes.Lattice.NTTCert
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Concrete NTT for ML-KEM

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLKEM/Concrete/NTT.lean` at `f5119c6`), by Quang Dao.

FIPS 203 Algorithms 9–12 (NTT, NTT⁻¹, MultiplyNTTs, BaseCaseMultiply), specialized to
`q = 3329`, `n = 256` and `ζ = 17`.

The NTT is seven blocked butterfly layers, each computed as a coefficient vector; the inverse runs
the inverse layers in reverse order and normalizes by `128⁻¹`. Complementary bit-reversed twiddles
make the inverse layers cancel the forward ones, so the transforms are mutually inverse. The NTT
evaluates: pair `i` of the transform, read as `a₀ + a₁ω`, is the input at the roots `ω` of
`X² − ζ^{2·BitRev₇(i)+1}`, so it turns negacyclic products into the base-case products of
`MultiplyNTTs`, and the laws of `NTTRingLaws` follow.

## Main statements

* `invNTT_ntt`, `ntt_invNTT`: the transforms are mutually inverse
* `nttCoeffs_pair_eval`: the NTT evaluates
* `ntt_negacyclicMul`: the NTT is multiplicative
* `concreteNTTRingLaws`: the laws of the NTT ring operations
-/




namespace MLKEM.Concrete

open MLKEM

/-! ## Bit reversal and zeta table -/

/-- Reverse the low 7 bits of `i`. -/
def bitRev7 (i : Nat) : Nat :=
  let b := fun k => (i >>> k) &&& 1
  (b 0 <<< 6) ||| (b 1 <<< 5) ||| (b 2 <<< 4) ||| (b 3 <<< 3) |||
  (b 4 <<< 2) ||| (b 5 <<< 1) ||| b 6

/-- Precomputed twiddle factors `ζ^{BitRev₇(i)}` for `i = 0 … 127`. -/
def zetaArray : Array Coeff :=
  (Array.range 128).map fun i => zeta ^ bitRev7 i

/-- The moduli of `MultiplyNTTs`, `ζ^{2·BitRev₇(i)+1}` for `i = 0 … 127` (FIPS 203, Appendix A). -/
def gammaArray : Array Coeff :=
  (Array.range 128).map fun i => zeta ^ (2 * bitRev7 i + 1)

/-- `128⁻¹ mod 3329 = 3303`. Applied after the inverse NTT. -/
def nInv : Coeff := 3303

/-- Safe array access with fallback to zero. -/
def getZ (a : Array Coeff) (i : Nat) : Coeff := a.getD i 0

theorem bitRev7_layer_partner :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      bitRev7 (2 ^ s.val + g.val) +
          bitRev7 (2 ^ (s.val + 1) - 1 - g.val) = 128 := by
  intro s g
  fin_cases s <;> fin_cases g <;> rfl

theorem layer_twiddle_index_bounds :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      2 ^ s.val + g.val < 128 ∧
        2 ^ (s.val + 1) - 1 - g.val < 128 := by
  intro s g
  fin_cases s <;> fin_cases g <;> norm_num

theorem getZ_zetaArray (i : Nat) (hi : i < 128) :
    getZ zetaArray i = zeta ^ bitRev7 i := by
  simp [getZ, zetaArray, hi]

theorem getZ_gammaArray (i : Nat) (hi : i < 128) :
    getZ gammaArray i = zeta ^ (2 * bitRev7 i + 1) := by
  simp [getZ, gammaArray, hi]

theorem zeta_pow_128 : (zeta : Coeff) ^ 128 = -1 := by
  change (17 : ZMod 3329) ^ 128 = -1
  reduce_mod_char

/-- `ζ = 17` is a primitive `256`-th root of unity in `ℤ_q` (FIPS 203 §4.3): the twiddle half of
the NTT correctness argument. -/
theorem zeta_isPrimitiveRoot : IsPrimitiveRoot (zeta : Coeff) 256 := by
  change IsPrimitiveRoot (17 : ZMod 3329) 256
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by reduce_mod_char) ?_
  intro p hp hdvd
  obtain rfl : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 8 by simpa using hdvd))
  reduce_mod_char
  exact ne_of_beq_false rfl

/-- The twiddle used by a forward butterfly and the complementary twiddle
used by its matching inverse butterfly multiply to `-1`. -/
theorem zetaArray_layer_partner :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      getZ zetaArray (2 ^ s.val + g.val) *
          getZ zetaArray (2 ^ (s.val + 1) - 1 - g.val) = -1 := by
  intro s g
  obtain ⟨hforward, hinverse⟩ := layer_twiddle_index_bounds s g
  rw [getZ_zetaArray _ hforward, getZ_zetaArray _ hinverse, ← pow_add]
  rw [bitRev7_layer_partner s g, zeta_pow_128]

/-! ## Forward NTT (Algorithm 9) -/

theorem layer_shape :
    ∀ s : Fin 7, 2 ^ s.val * (2 * (128 / 2 ^ s.val)) = polyBackend.degree := by
  intro s
  fin_cases s <;> rfl

abbrev NTTCoord := Fin polyBackend.degree

/-- The blocked coordinate layout used by layer `s` of Algorithms 9 and 10. -/
def layerLayout (s : Fin 7) :
    LatticeCrypto.NTTCert.ButterflyLayout
      (Fin (2 ^ s.val) × Fin (128 / 2 ^ s.val)) NTTCoord where
  equiv := (LatticeCrypto.NTTCert.blockLayout (2 ^ s.val) (128 / 2 ^ s.val)).equiv.trans
    (finCongr (layer_shape s))

/-- One structurally certified ML-KEM butterfly layer. The group coordinate chooses the
twiddle; the within-group coordinate selects one of the independent butterflies. -/
def nttStage (s : Fin 7) :
    LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord :=
  LatticeCrypto.NTTCert.butterflyStageRev (layerLayout s)
    (fun pair => getZ zetaArray (2 ^ s.val + pair.1.val))
    (fun pair => getZ zetaArray (2 ^ (s.val + 1) - 1 - pair.1.val))
    (by
      intro pair
      have h := zetaArray_layer_partner s pair.1
      calc
        -getZ zetaArray (2 ^ (s.val + 1) - 1 - pair.1.val) *
            getZ zetaArray (2 ^ s.val + pair.1.val) =
          -(getZ zetaArray (2 ^ s.val + pair.1.val) *
            getZ zetaArray (2 ^ (s.val + 1) - 1 - pair.1.val)) := by ring
        _ = -(-1) := by rw [h]
        _ = 1 := by ring)

/-- The seven forward layers, ordered as Algorithm 9 executes them. -/
def nttStages :
    List (LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord) :=
  [nttStage 0, nttStage 1, nttStage 2, nttStage 3, nttStage 4, nttStage 5, nttStage 6]

theorem nInv_stageScalar :
    nInv * LatticeCrypto.NTTCert.stageScalar nttStages = 1 := by
  change ((3303 * 128 : Nat) : ZMod 3329) = ((1 : Nat) : ZMod 3329)
  rw [ZMod.natCast_eq_natCast_iff']

/-- Named proof-facing coefficient transform. Keeping the assembled stage list behind this
boundary lets downstream algebraic proofs use focused interface lemmas. -/
def nttCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.forwardStages nttStages input

/-- Named proof-facing inverse coefficient transform, including the final normalization. -/
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
of its modulus `X^(256/2^s) - ζ^e`, with `e = 2·BitRev₇(2^s + g)`; after all seven, pair `i`
evaluates like the input at the roots of `X² − ζ^{2·BitRev₇(i)+1}`, which are roots of
`X^256 + 1`, so the NTT turns negacyclic products into base-case products. The roots are taken
in `ℤ_q[X]/(X² − γ)`, where the coordinates of `a₀ + a₁ω` are unique. -/

section Evaluation

open LatticeCrypto.NTTCert

theorem layerLayout_left_val (s : Fin 7) (g : Fin (2 ^ s.val)) (j : Fin (128 / 2 ^ s.val)) :
    ((layerLayout s).equiv ((g, j), false)).val = g.val * (2 * (128 / 2 ^ s.val)) + j.val := by
  simp [layerLayout]

theorem layerLayout_right_val (s : Fin 7) (g : Fin (2 ^ s.val)) (j : Fin (128 / 2 ^ s.val)) :
    ((layerLayout s).equiv ((g, j), true)).val =
      g.val * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + j.val := by
  simp [layerLayout]

/-- The exponent of the root at which group `g` evaluates after `s` layers; after all seven,
pair `i` evaluates at the roots of `X² − ζ^{2·BitRev₇(i)+1}`. -/
def rootExponent (s g : ℕ) : ℕ :=
  if s < 7 then 2 * bitRev7 (2 ^ s + g) else 2 * bitRev7 g + 1

theorem rootExponent_children :
    ∀ (s : Fin 7) (g : Fin (2 ^ s.val)),
      rootExponent (s.val + 1) (2 * g.val) % 256 = bitRev7 (2 ^ s.val + g.val) % 256 ∧
      rootExponent (s.val + 1) (2 * g.val + 1) % 256 =
        (bitRev7 (2 ^ s.val + g.val) + 128) % 256 := by
  intro s g
  fin_cases s <;> fin_cases g <;> exact ⟨rfl, rfl⟩

theorem zeta_pow_mod (a : ℕ) : (zeta : Coeff) ^ a = zeta ^ (a % 256) := by
  conv_lhs => rw [← Nat.mod_add_div a 256]
  rw [pow_add, pow_mul, zeta_isPrimitiveRoot.pow_eq_one, one_pow, mul_one]

/-- **The evaluation invariant after `s` layers**: each group of `a`, of length `256 / 2 ^ s`,
evaluates like `f` at every root of its modulus, in every algebra over the coefficients. -/
def EvalInvariant (s : ℕ) (a f : NTTCoord → Coeff) : Prop :=
  ∀ g < 2 ^ s, ∀ (S : Type) [CommRing S] [Algebra Coeff S] (ω : S),
    ω ^ (256 / 2 ^ s) = algebraMap Coeff S (zeta ^ rootExponent s g) →
      segmentEval a (g * (256 / 2 ^ s)) (256 / 2 ^ s) ω = segmentEval f 0 256 ω

theorem evalInvariant_zero (f : NTTCoord → Coeff) : EvalInvariant 0 f f := by
  intro g hg S _ _ ω _
  obtain rfl : g = 0 := by simpa using hg
  simp

/-- **One layer preserves the invariant.** -/
theorem evalInvariant_step (s : Fin 7) {a f : NTTCoord → Coeff} (h : EvalInvariant s.val a f) :
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
  have hz : getZ zetaArray (2 ^ s.val + g) = zeta ^ bitRev7 (2 ^ s.val + g) :=
    getZ_zetaArray _ hbounds
  have hstage : (nttStage s).forward a =
      forwardStage (layerLayout s) (fun pair => getZ zetaArray (2 ^ s.val + pair.1.val)) a := rfl
  have hl : ∀ j < 128 / 2 ^ s.val, coeffAt ((nttStage s).forward a) (g * (2 * (128 / 2 ^ s.val)) + j) =
      coeffAt a (g * (2 * (128 / 2 ^ s.val)) + j) + getZ zetaArray (2 ^ s.val + g) *
        coeffAt a (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + j) := by
    intro j hj
    rw [hstage]
    exact (forwardStage_coeffAt (layerLayout s) (layerLayout_left_val s) (layerLayout_right_val s)
      (fun pair => getZ zetaArray (2 ^ s.val + pair.1.val)) a ⟨g, hg⟩ ⟨j, hj⟩).1
  have hr : ∀ j < 128 / 2 ^ s.val,
      coeffAt ((nttStage s).forward a) (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + j) =
      coeffAt a (g * (2 * (128 / 2 ^ s.val)) + j) - getZ zetaArray (2 ^ s.val + g) *
        coeffAt a (g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val + j) := by
    intro j hj
    rw [hstage]
    exact (forwardStage_coeffAt (layerLayout s) (layerLayout_left_val s) (layerLayout_right_val s)
      (fun pair => getZ zetaArray (2 ^ s.val + pair.1.val)) a ⟨g, hg⟩ ⟨j, hj⟩).2
  have hbf := segmentEval_butterfly (S := S) a ((nttStage s).forward a)
    (g * (2 * (128 / 2 ^ s.val))) (128 / 2 ^ s.val) (getZ zetaArray (2 ^ s.val + g)) hl hr ω
  have hparent : ω ^ (128 / 2 ^ s.val) = algebraMap Coeff S (getZ zetaArray (2 ^ s.val + g)) ∨
      ω ^ (128 / 2 ^ s.val) = -algebraMap Coeff S (getZ zetaArray (2 ^ s.val + g)) →
      ω ^ (256 / 2 ^ s.val) = algebraMap Coeff S (zeta ^ rootExponent s.val g) := by
    rintro (hω' | hω') <;>
    · rw [hB, pow_mul', hω', rootExponent, if_pos s.isLt, pow_mul', hz]
      simp [map_pow]
  rw [hB'] at hω ⊢
  interval_cases c
  · simp only [add_zero] at hω ⊢
    have hω' : ω ^ (128 / 2 ^ s.val) = algebraMap Coeff S (getZ zetaArray (2 ^ s.val + g)) := by
      rw [hω, zeta_pow_mod, hc0, ← zeta_pow_mod, hz]
    rw [show 2 * g * (128 / 2 ^ s.val) = g * (2 * (128 / 2 ^ s.val)) by ring,
      hbf.1 hω', ← hB]
    exact h g hg S ω (hparent (Or.inl hω'))
  · have hω' : ω ^ (128 / 2 ^ s.val) = -algebraMap Coeff S (getZ zetaArray (2 ^ s.val + g)) := by
      rw [hω, zeta_pow_mod, hc1, ← zeta_pow_mod, pow_add, zeta_pow_128, hz]
      simp [map_neg]
    rw [show (2 * g + 1) * (128 / 2 ^ s.val) =
        g * (2 * (128 / 2 ^ s.val)) + 128 / 2 ^ s.val by ring, hbf.2 hω', ← hB]
    exact h g hg S ω (hparent (Or.inr hω'))

/-- The invariant after all seven layers. -/
theorem evalInvariant_nttCoeffs (f : NTTCoord → Coeff) : EvalInvariant 7 (nttCoeffs f) f := by
  have h1 := evalInvariant_step 0 (evalInvariant_zero f)
  have h2 := evalInvariant_step 1 h1
  have h3 := evalInvariant_step 2 h2
  have h4 := evalInvariant_step 3 h3
  have h5 := evalInvariant_step 4 h4
  have h6 := evalInvariant_step 5 h5
  exact evalInvariant_step 6 h6

/-- **The NTT evaluates**: pair `i` of `nttCoeffs f`, read as `a₀ + a₁ ω`, is `f` at every root
`ω` of `X² − ζ^{2·BitRev₇(i)+1}`. -/
theorem nttCoeffs_pair_eval (f : NTTCoord → Coeff) (i : ℕ) (hi : i < 128)
    {S : Type} [CommRing S] [Algebra Coeff S] (ω : S)
    (hω : ω ^ 2 = algebraMap Coeff S (zeta ^ (2 * bitRev7 i + 1))) :
    algebraMap Coeff S (coeffAt (nttCoeffs f) (2 * i)) +
        algebraMap Coeff S (coeffAt (nttCoeffs f) (2 * i + 1)) * ω =
      segmentEval f 0 256 ω := by
  have h := evalInvariant_nttCoeffs f i hi S ω (by simpa [rootExponent] using hω)
  rw [← h]
  simp [segmentEval, Finset.sum_range_succ, mul_comm]

theorem gamma_pow_128 (i : ℕ) : ((zeta : Coeff) ^ (2 * bitRev7 i + 1)) ^ 128 = -1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta_pow_128, (odd_two_mul_add_one _).neg_one_pow]

/-- **Base-case multiplication** (FIPS 203 Algorithm 12): the product of `a₀ + a₁X` and
`b₀ + b₁X` modulo `X² − γ`. -/
def baseCaseMultiply (a0 a1 b0 b1 γ : Coeff) : Coeff × Coeff :=
  (a0 * b0 + a1 * b1 * γ, a0 * b1 + a1 * b0)

/-- **The NTT turns negacyclic products into base-case products**: pair `i` of the transformed
product is the base-case product of pair `i` of the transformed factors modulo
`X² − ζ^{2·BitRev₇(i)+1}`. -/
theorem nttCoeffs_negacyclicConv (f g : NTTCoord → Coeff) (i : ℕ) (hi : i < 128) :
    (coeffAt (nttCoeffs fun k => LatticeCrypto.negacyclicConvCoeff f g k) (2 * i),
      coeffAt (nttCoeffs fun k => LatticeCrypto.negacyclicConvCoeff f g k) (2 * i + 1)) =
      baseCaseMultiply (coeffAt (nttCoeffs f) (2 * i)) (coeffAt (nttCoeffs f) (2 * i + 1))
        (coeffAt (nttCoeffs g) (2 * i)) (coeffAt (nttCoeffs g) (2 * i + 1))
        (zeta ^ (2 * bitRev7 i + 1)) := by
  have : Fact (1 < modulus) := ⟨by unfold modulus; norm_num⟩
  have hω := adjoinRoot_root_sq ((zeta : Coeff) ^ (2 * bitRev7 i + 1))
  have h256 : AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C ((zeta : Coeff) ^ (2 * bitRev7 i + 1))) ^ 256 = -1 := by
    rw [show 256 = 2 * 128 from rfl, pow_mul, hω, ← map_pow, gamma_pow_128, map_neg, map_one]
  have hconv : segmentEval (fun k => LatticeCrypto.negacyclicConvCoeff f g k) 0 256
      (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C ((zeta : Coeff) ^ (2 * bitRev7 i + 1)))) =
      segmentEval f 0 256 _ * segmentEval g 0 256 _ :=
    segmentEval_negacyclicConv f g _ h256
  have hH := nttCoeffs_pair_eval (fun k => LatticeCrypto.negacyclicConvCoeff f g k) i hi _ hω
  rw [hconv, ← nttCoeffs_pair_eval f i hi _ hω,
    ← nttCoeffs_pair_eval g i hi _ hω] at hH
  obtain ⟨h0, h1⟩ := adjoinRoot_pair_injective
      (c := coeffAt (nttCoeffs f) (2 * i) * coeffAt (nttCoeffs g) (2 * i) +
        coeffAt (nttCoeffs f) (2 * i + 1) * coeffAt (nttCoeffs g) (2 * i + 1) *
          zeta ^ (2 * bitRev7 i + 1))
      (d := coeffAt (nttCoeffs f) (2 * i) * coeffAt (nttCoeffs g) (2 * i + 1) +
        coeffAt (nttCoeffs f) (2 * i + 1) * coeffAt (nttCoeffs g) (2 * i)) (by
    rw [hH]
    simp only [map_add, map_mul]
    linear_combination (algebraMap Coeff _ (coeffAt (nttCoeffs f) (2 * i + 1)) *
      algebraMap Coeff _ (coeffAt (nttCoeffs g) (2 * i + 1))) * hω)
  simp only [baseCaseMultiply, Prod.mk.injEq]
  exact ⟨h0, h1⟩

end Evaluation

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

/-- **The NTT** (FIPS 203 Algorithm 9): the seven butterfly layers, each computed as a
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

/-- **MultiplyNTTs** (FIPS 203 Algorithm 11): pair `i` of the product is the base-case product
of pair `i` of the factors modulo `X² − ζ^{2·BitRev₇(i)+1}`. -/
def multiplyNTTs (fHat gHat : Tq) : Tq :=
  ⟨polyBackend.build fun k =>
    let i := k.val / 2
    let f := LatticeCrypto.NTTCert.coeffAt (polyBackend.coeff fHat.coeffs)
    let g := LatticeCrypto.NTTCert.coeffAt (polyBackend.coeff gHat.coeffs)
    let h := baseCaseMultiply (f (2 * i)) (f (2 * i + 1)) (g (2 * i)) (g (2 * i + 1))
      (getZ gammaArray i)
    if k.val % 2 = 0 then h.1 else h.2⟩

/-- The concrete inverse transform is a left inverse to the concrete forward transform. -/
theorem invNTT_ntt (f : Rq) : invNTT (ntt f) = f := by
  rw [invNTT_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_comp
    nttCoeffs invNTTCoeffs invNTTCoeffs_nttCoeffs f

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

theorem hadd_rq (f g : Rq) :
    polyBackend.coeff (f + g) = polyBackend.coeff f + polyBackend.coeff g := by
  funext i
  change (f + g).get i = f.get i + g.get i
  exact coeffRing.add_coeff f g i

theorem hsub_rq (f g : Rq) :
    polyBackend.coeff (f - g) = polyBackend.coeff f - polyBackend.coeff g := by
  funext i
  change (f - g).get i = f.get i - g.get i
  exact coeffRing.sub_coeff f g i

theorem hzero_rq : polyBackend.coeff (0 : Rq) = 0 := by
  funext i
  change (0 : Rq).get i = 0
  exact LatticeCrypto.vectorRing_zero_get i

/-- The concrete forward transform is a left inverse to the concrete inverse transform. -/
theorem ntt_invNTT (fHat : Tq) : ntt (invNTT fHat) = fHat := by
  obtain ⟨f, hf⟩ := ntt_surjective fHat
  calc
    ntt (invNTT fHat) = ntt (invNTT (ntt f)) := by rw [hf]
    _ = ntt f := by rw [invNTT_ntt]
    _ = fHat := hf

/-- The concrete NTT is additive on the coefficient-vector carrier of `T_q`. -/
theorem ntt_add_toRq (f g : Rq) : (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_add nttCoeffs hadd_rq
    nttCoeffs_add f g

/-- The concrete NTT preserves subtraction on the coefficient-vector carrier of `T_q`. -/
theorem ntt_sub_toRq (f g : Rq) : (ntt (f - g) : Rq) = (ntt f : Rq) - (ntt g : Rq) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  exact LatticeCrypto.NTTCert.applyCoeffTransform_sub nttCoeffs hsub_rq
    nttCoeffs_sub f g

/-- The concrete NTT is additive. -/
theorem ntt_add (f g : Rq) : ntt (f + g) = ntt f + ntt g := by
  apply LatticeCrypto.TransformPoly.ext
  change (ntt (f + g) : Rq) = (ntt f : Rq) + (ntt g : Rq)
  exact ntt_add_toRq f g

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

theorem hinvadd_tq (fHat gHat : Tq) :
    polyBackend.coeff (fHat + gHat).coeffs =
      fun i => polyBackend.coeff fHat.coeffs i + polyBackend.coeff gHat.coeffs i := by
  funext i; exact coeffRing.add_coeff fHat.coeffs gHat.coeffs i

theorem negacyclicMul_coeff (a b : Rq) (k : Fin ringDegree) :
    polyBackend.coeff (negacyclicMul a b) k =
      LatticeCrypto.negacyclicConvCoeff (polyBackend.coeff a) (polyBackend.coeff b) k :=
  LatticeCrypto.negacyclicMul_coeff polyBackend a b k

/-- **The NTT is multiplicative**: it turns negacyclic products into the products of
`MultiplyNTTs`. -/
theorem ntt_negacyclicMul (f g : Rq) : ntt (negacyclicMul f g) = multiplyNTTs (ntt f) (ntt g) := by
  rw [ntt_eq, ntt_eq, ntt_eq]
  apply LatticeCrypto.TransformPoly.ext
  unfold multiplyNTTs
  simp only [LatticeCrypto.NTTCert.applyCoeffTransform]
  refine congrArg polyBackend.build (funext fun k => ?_)
  have hk : k.val < 256 := k.isLt
  rw [show polyBackend.coeff (negacyclicMul f g) = fun k => LatticeCrypto.negacyclicConvCoeff
      (polyBackend.coeff f) (polyBackend.coeff g) k from funext (negacyclicMul_coeff f g),
    funext (polyBackend.coeff_build (nttCoeffs (polyBackend.coeff f))),
    funext (polyBackend.coeff_build (nttCoeffs (polyBackend.coeff g))), getZ_gammaArray _ (by omega)]
  obtain ⟨h0, h1⟩ := Prod.mk.inj
    (nttCoeffs_negacyclicConv (polyBackend.coeff f) (polyBackend.coeff g) (k.val / 2) (by omega))
  rw [show nttCoeffs (fun k => LatticeCrypto.negacyclicConvCoeff (polyBackend.coeff f)
      (polyBackend.coeff g) k) k = LatticeCrypto.NTTCert.coeffAt (nttCoeffs fun k =>
        LatticeCrypto.negacyclicConvCoeff (polyBackend.coeff f) (polyBackend.coeff g) k) k.val by
    simp [LatticeCrypto.NTTCert.coeffAt]]
  split_ifs with hpar
  · conv_lhs => rw [show k.val = 2 * (k.val / 2) by omega]
    rw [h0]; rfl
  · conv_lhs => rw [show k.val = 2 * (k.val / 2) + 1 by omega]
    rw [h1]; rfl

/-- `MultiplyNTTs` is the negacyclic product transported through the NTT. -/
theorem multiplyNTTs_eq (fHat gHat : Tq) :
    multiplyNTTs fHat gHat = ntt (negacyclicMul (invNTT fHat) (invNTT gHat)) := by
  rw [ntt_negacyclicMul, ntt_invNTT, ntt_invNTT]

/-- Concrete `NTTRingOps` instance for ML-KEM. -/
@[reducible] def concreteNTTRingOps : NTTRingOps where
  toHat := ntt
  fromHat := invNTT
  mulHat := multiplyNTTs

/-- Proof bundle showing that the concrete ML-KEM NTT implementation satisfies the abstract
`NTTRingLaws`. -/
theorem concreteNTTRingLaws : NTTRingLaws concreteNTTRingOps where
  fromHat_toHat := invNTT_ntt
  toHat_fromHat := ntt_invNTT
  toHat_zero := by
    apply LatticeCrypto.TransformPoly.ext
    show (ntt 0).coeffs = _
    rw [ntt_eq]
    exact LatticeCrypto.NTTCert.applyCoeffTransform_zero nttCoeffs hzero_rq nttCoeffs_zero
  toHat_mul f g := ntt_negacyclicMul f g
  toHat_add f g := by
    change ntt (f + g) = ntt f + ntt g
    exact ntt_add f g
  toHat_sub f g := by
    change ntt (f - g) = ntt f - ntt g
    exact ntt_sub f g
  mul_add f g h := by
    change multiplyNTTs f (g + h) = multiplyNTTs f g + multiplyNTTs f h
    simp only [multiplyNTTs_eq, invNTT_add]
    rw [← ntt_add]
    exact congrArg ntt (LatticeCrypto.vectorRing_mul_add_right
      (Coeff := Coeff) (n := ringDegree) _ _ _)
  mul_sub f g h := by
    change multiplyNTTs f (g - h) = multiplyNTTs f g - multiplyNTTs f h
    simp only [multiplyNTTs_eq, invNTT_sub]
    rw [← ntt_sub]
    exact congrArg ntt (LatticeCrypto.vectorRing_mul_sub_right
      (Coeff := Coeff) (n := ringDegree) _ _ _)
  mul_comm f g := by
    change multiplyNTTs f g = multiplyNTTs g f
    simp only [multiplyNTTs_eq, LatticeCrypto.vectorRing_mul_comm]
  mul_assoc f g h := by
    change multiplyNTTs (multiplyNTTs f g) h = multiplyNTTs f (multiplyNTTs g h)
    simp only [multiplyNTTs_eq, invNTT_ntt]
    exact congrArg ntt (mul_assoc (invNTT f) (invNTT g) (invNTT h))

end MLKEM.Concrete
