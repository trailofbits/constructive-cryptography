import Commons.Schemes.Signature.MLDSA.Scheme
import Commons.Schemes.Signature.MLDSA.Encoding
import Commons.Definitions.Signature
import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Sigma

/-!
# ML-DSA Signing and Verification

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLDSA/Signature.lean` at `f5119c6`), by Quang Dao.

The internal signing and verification algorithms of FIPS 204 (Algorithms 7 and 8) on the keys
of `Commons.Schemes.Signature.MLDSA.Scheme`, their correctness, and ML-DSA as a
`Commons.SignatureScheme`. Signing hashes the message to `μ = H(tr ‖ M')`, derives the mask seed
`ρ'' = H(K ‖ rnd ‖ μ)`, and retries with the counter `κ` advancing by `l`; verification
recomputes `c̃ = H(μ ‖ w1Encode(w₁'))`. The rejection loop is bounded by `maxAttempts`, and
signing returns `none` when every attempt aborts.

## Main definitions

* `MLDSA.FIPSSignature`: the signature `(c̃, z, h)`
* `MLDSA.fipsSignAttempt`, `MLDSA.fipsSignLoop`: one attempt at counter `κ`, and the bounded loop
* `MLDSA.fipsSign`: `ML-DSA.Sign_internal(sk, M', rnd)` (Algorithm 7)
* `MLDSA.fipsVerify`: `ML-DSA.Verify_internal(pk, M', σ)` (Algorithm 8)
* `MLDSA.Message L`: the messages `M'` of at most `L` bytes
* `MLDSA.toSignatureScheme`: ML-DSA as a `Commons.SignatureScheme` on `MLDSA.Message L`, with
  uniform `ξ` and `rnd`

## Main statements

* `MLDSA.fipsSign_fipsVerify_correct`: an honest key pair's signatures verify
-/

open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p)

section Scheme

variable [nttOps : NTTRingOps]

/-- The FIPS 204 signature format: `(c̃, z, h)`. -/
structure FIPSSignature where
  cTilde : CommitHashBytes p
  z : RqVec p.l
  h : Vector prims.Hint p.k

/-- Signatures are finite when the hints are. -/
instance [Fintype prims.Hint] : Fintype (FIPSSignature p prims) :=
  Fintype.ofEquiv (CommitHashBytes p × RqVec p.l × Vector prims.Hint p.k)
    ⟨fun x => ⟨x.1, x.2.1, x.2.2⟩, fun sig => (sig.cTilde, sig.z, sig.h), fun _ => rfl, fun _ => rfl⟩

instance [DecidableEq prims.Hint] : DecidableEq (FIPSSignature p prims) := fun x y =>
  decidable_of_iff ((x.cTilde, x.z, x.h) = (y.cTilde, y.z, y.h)) (by cases x; cases y; simp)

/-- **The messages `M'` of at most `L` bytes.** FIPS 204 signs byte strings of any length; a
finite message space bounds their length. -/
abbrev Message (L : ℕ) := {m : List Byte // m.length ≤ L}

noncomputable instance (L : ℕ) : Fintype (Message L) :=
  Fintype.ofInjective
    (fun m : Message L =>
      (⟨⟨m.1.length, Nat.lt_succ_of_le m.2⟩, ⟨m.1, rfl⟩⟩ : Σ n : Fin (L + 1), List.Vector Byte n))
    (by
      intro a b h
      apply Subtype.ext
      simpa using congrArg (fun x : Σ n : Fin (L + 1), List.Vector Byte n => x.2.toList) h)

/-! ### Signing -/

/-- A single signing attempt at counter value `κ` (Algorithm 7, lines 5–30).

Deterministic given all its inputs; randomness enters through `ρ''` which was
derived from a random `rnd` by the caller. -/
def fipsSignAttempt
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (kappa : ℕ) :
    Option (FIPSSignature p prims) :=
  let y := prims.expandMask rhoDoublePrime kappa
  let w := aHat * y
  let w1 := prims.highBitsVec w
  let cTilde := prims.hashCommitment mu (prims.w1Encode w1)
  let c := prims.sampleInBall cTilde
  let cs1 := c • sk.s1
  let cs2 := c • sk.s2
  let z := y + cs1
  let r0 := prims.lowBitsVec (w - cs2)
  if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then
    let ct0 := c • sk.t0
    let h := prims.makeHintVec (-ct0) (w - cs2 + ct0)
    if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
      some ⟨cTilde, z, h⟩
    else
      none
  else
    none

/-- The deterministic signing loop: try counter values `κ = 0, l, 2l, ...`
up to `maxAttempts` iterations (Algorithm 7, lines 4–31). -/
def fipsSignLoop
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ) :
    Option (FIPSSignature p prims) :=
  (List.range maxAttempts).findSome? fun i =>
    fipsSignAttempt p prims sk aHat mu rhoDoublePrime (i * p.l)

/-- **ML-DSA.Sign_internal** (Algorithm 7) with the randomness `rnd`:

1. Compute `μ = H(tr ‖ M')`
2. Compute `ρ'' = H(K ‖ rnd ‖ μ)`
3. Expand `Â = ExpandA(ρ)`
4. Try signing attempts with incrementing `κ`

Returns `none` if all `maxAttempts` attempts abort. -/
def fipsSign (sk : SecretKey p) (msg : List Byte) (rnd : Bytes 32) (maxAttempts : ℕ) :
    Option (FIPSSignature p prims) :=
  let mu := prims.hashMessage sk.tr msg
  let rhoDoublePrime := prims.hashPrivateSeed sk.key rnd mu
  fipsSignLoop p prims sk (prims.expandA sk.rho) mu rhoDoublePrime maxAttempts

/-! ### Verification -/

/-- ML-DSA.Verify (Algorithm 3 / Algorithm 8): verify a signature.

1. Expand `Â = ExpandA(ρ)` from the public key
2. Compute `tr = H(pk)`, `μ = H(tr ‖ M')`
3. Derive `c = SampleInBall(c̃)` and compute `w'_Approx = Az - c·(t₁·2^d)`
4. Apply hint: `w₁' = UseHint(h, w'_Approx)`
5. Recompute `c̃' = H(μ ‖ w1Encode(w₁'))`
6. Accept iff `‖z‖∞ < γ₁ - β`, `c̃' = c̃`, and `hintWeight(h) ≤ ω` -/
def fipsVerify (pk : PublicKey p prims) (msg : List Byte)
    (sig : FIPSSignature p prims) : Bool :=
  let aHat := prims.expandA pk.rho
  let tr := prims.hashPublicKey pk.rho pk.t1
  let mu := prims.hashMessage tr msg
  let c := prims.sampleInBall sig.cTilde
  let wApprox := computeWApprox p prims aHat c sig.z pk.t1
  let w1' := prims.useHintVec sig.h wApprox
  let cTildeRecomputed := prims.hashCommitment mu (prims.w1Encode w1')
  decide (polyVecNorm sig.z < p.gamma1 - p.beta) &&
  decide (cTildeRecomputed = sig.cTilde) &&
  decide (prims.hintWeight sig.h ≤ p.omega)

/-! ### ML-DSA as a signature scheme -/

open Probability.Distribution in
/-- **ML-DSA** as a `Commons.SignatureScheme` on the messages of at most `L` bytes: key
generation from a uniform seed `ξ` (Algorithm 6), signing with a uniform `rnd` (Algorithm 7, the
hedged variant) and at most `maxAttempts` attempts, and verification (Algorithm 8), which rejects
the abort `none`. -/
noncomputable def toSignatureScheme (maxAttempts L : ℕ) :
    Commons.SignatureScheme (PublicKey p prims) (SecretKey p) (Message L)
      (Option (FIPSSignature p prims)) where
  gen := ⟨fTransform (keyGenFromSeed p prims) (uniform (Bytes 32)),
    fTransform_isProbDist _ uniform_isProbDist⟩
  sign sk msg := ⟨fTransform (fun rnd => fipsSign p prims sk msg.1 rnd maxAttempts)
      (uniform (Bytes 32)),
    fTransform_isProbDist _ uniform_isProbDist⟩
  verify pk msg
    | some sig => fipsVerify p prims pk msg.1 sig
    | none => false

end Scheme

/-! ### Vector Arithmetic Helpers -/

lemma rq_sub_add_cancel (a b : Rq) : a - b + b = a :=
  LatticeCrypto.Poly.ext_get_eq fun i => by
    change ((coeffRing.add (coeffRing.sub a b) b) : Rq).get i = a.get i
    simp [sub_add_cancel]

lemma rq_add_neg_cancel (a b : Rq) : a + b + (-b) = a :=
  LatticeCrypto.Poly.ext_get_eq fun i => by
    change ((coeffRing.add (coeffRing.add a b) (coeffRing.neg b)) : Rq).get i = a.get i
    simp [add_neg_cancel_right]

lemma neg_rq_get (f : Rq) (i : Fin ringDegree) : (-f).get i = -(f.get i) := by
  change (coeffRing.neg f).get i = _
  simp

lemma polyNorm_neg (f : Rq) : polyNorm (-f) = polyNorm f := by
  unfold polyNorm normOps
  simp only [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView]
  unfold LatticeCrypto.cInfNormOf
  apply Finset.sup_congr rfl
  intro i _
  simp only [LatticeCrypto.zmodCenteredCoeffView, coeffRing.coeff_neg]
  exact LatticeCrypto.centeredRepr_natAbs_neg _

/-- Single-component recovery: `UseHint(MakeHint(-ct₀, r + ct₀), r + ct₀) = HighBits(r + s)`
when `‖ct₀‖ ≤ γ₂`, `‖LowBits(r)‖ < γ₂ - β`, and `‖s‖ ≤ β`, and `r + s = w`.

Proof strategy:
1. `useHint_makeHint` with `z = -ct₀`: need `polyNorm (-ct₀) ≤ γ₂`, from `cInfNorm_neg`.
2. Result: `highBits((r + ct₀) + (-ct₀)) = highBits(r)` — need `r + ct₀ + (-ct₀) = r`.
3. `hide_low` with perturbation `s`: `highBits(r + s) = highBits(r)` when
   `polyNorm s ≤ β` and `polyNorm(lowBits(r)) + β < γ₂`. -/
lemma useHint_makeHint_eq_highBits
    (h_useHint_makeHint : ∀ z r : Rq,
      polyNorm z ≤ p.gamma2 →
      prims.useHint (prims.makeHint z r) r = prims.highBits (r + z))
    (h_hide_low : ∀ (r s : Rq) (b : ℕ),
      polyNorm s ≤ b →
      polyNorm (prims.lowBits r) + b < p.gamma2 →
      prims.highBits (r + s) = prims.highBits r)
    (w_j r_j ct0_j s_j : Rq)
    (h_r_eq : r_j = w_j - s_j)
    (h_norm_ct0 : polyNorm ct0_j ≤ p.gamma2)
    (h_norm_r0 : polyNorm (prims.lowBits r_j) < p.gamma2 - p.beta)
    (h_s_bound : polyNorm s_j ≤ p.beta) :
    prims.useHint (prims.makeHint (-ct0_j) (r_j + ct0_j)) (r_j + ct0_j) =
      prims.highBits w_j := by
  have h_neg_norm : polyNorm (-ct0_j) ≤ p.gamma2 := by
    rw [polyNorm_neg]; exact h_norm_ct0
  rw [h_useHint_makeHint (-ct0_j) (r_j + ct0_j) h_neg_norm]
  rw [rq_add_neg_cancel r_j ct0_j]
  have h2 : polyNorm (prims.lowBits r_j) + p.beta < p.gamma2 := by omega
  rw [← h_hide_low r_j s_j p.beta h_s_bound h2]
  rw [h_r_eq, rq_sub_add_cancel w_j s_j]

/-- When all signing norm bounds hold, UseHint recovers the original commitment:
`UseHintVec(MakeHintVec(-ct₀, w - cs₂ + ct₀), w - cs₂ + ct₀) = HighBitsVec(w)`.

Follows componentwise from `useHint_makeHint_eq_highBits`. -/
lemma useHintVec_makeHintVec_eq_highBitsVec
    (h_useHint_makeHint : ∀ z r : Rq,
      polyNorm z ≤ p.gamma2 →
      prims.useHint (prims.makeHint z r) r = prims.highBits (r + z))
    (h_hide_low : ∀ (r s : Rq) (b : ℕ),
      polyNorm s ≤ b →
      polyNorm (prims.lowBits r) + b < p.gamma2 →
      prims.highBits (r + s) = prims.highBits r)
    (w cs2 ct0 : RqVec p.k)
    (h_norm_ct0 : polyVecNorm ct0 < p.gamma2)
    (h_norm_r0 : polyVecNorm (prims.lowBitsVec (w - cs2)) < p.gamma2 - p.beta)
    (h_cs2_bound : ∀ (j : Fin p.k),
      LatticeCrypto.cInfNorm (cs2.get j) ≤ p.beta) :
    prims.useHintVec (prims.makeHintVec (-ct0) (w - cs2 + ct0))
      (w - cs2 + ct0) = prims.highBitsVec w := by
  apply Vector.ext
  intro j hj
  unfold Primitives.useHintVec Primitives.makeHintVec Primitives.highBitsVec
  simp only [Vector.getElem_zipWith, Vector.getElem_neg, Vector.getElem_map]
  let jj : Fin p.k := ⟨j, hj⟩
  let r_j := (w - cs2)[j]
  have h_ct0_lt : polyNorm ct0[j] < p.gamma2 := by
      exact lt_of_le_of_lt
        (LatticeCrypto.PolyVec.component_cInfNorm_le normOps ct0 jj)
        h_norm_ct0
  have h_r0_lt : polyNorm ((prims.lowBitsVec (w - cs2))[j]) < p.gamma2 - p.beta := by
      exact lt_of_le_of_lt
        (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (prims.lowBitsVec (w - cs2)) jj)
        h_norm_r0
  have h_arg : (w - cs2 + ct0)[j] = r_j + ct0[j] := by
    simp only [Vector.getElem_add, Vector.getElem_sub, r_j]
  rw [h_arg]
  refine useHint_makeHint_eq_highBits (p := p) (prims := prims)
    h_useHint_makeHint h_hide_low
    w[j] (w - cs2)[j] ct0[j] cs2[j]
    ?_ ?_ ?_ ?_
  · change (w - cs2).get jj = w.get jj - cs2.get jj
    simp only [Vector.get_eq_getElem, Vector.getElem_sub]
  · exact Nat.le_of_lt h_ct0_lt
  · simpa [Primitives.lowBitsVec, r_j] using h_r0_lt
  · have hnorm : polyNorm (cs2.get jj) = LatticeCrypto.cInfNorm (cs2.get jj) :=
      LatticeCrypto.zmodPolyNormOps_cInfNorm (cs2.get jj)
    rw [show cs2[j] = cs2.get jj by rfl, hnorm]
    exact h_cs2_bound jj

variable [nttOps : NTTRingOps]

/-! ### Correctness -/

lemma fipsSignLoop_exists
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ)
    (sig : FIPSSignature p prims)
    (h : fipsSignLoop p prims sk aHat mu rhoDoublePrime maxAttempts = some sig) :
    ∃ i ∈ List.range maxAttempts,
      fipsSignAttempt p prims sk aHat mu rhoDoublePrime (i * p.l) = some sig :=
  List.exists_of_findSome?_eq_some h

lemma fipsSignAttempt_spec
    (sk : SecretKey p) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (rhoDoublePrime : Bytes 64) (kappa : ℕ)
    (sig : FIPSSignature p prims)
    (h : fipsSignAttempt p prims sk aHat mu rhoDoublePrime kappa = some sig) :
    let y := prims.expandMask rhoDoublePrime kappa
    let w := aHat * y
    let w1 := prims.highBitsVec w
    let c := prims.sampleInBall (prims.hashCommitment mu (prims.w1Encode w1))
    let cs2 := c • sk.s2
    let z := y + c • sk.s1
    let ct0 := c • sk.t0
    sig.cTilde = prims.hashCommitment mu (prims.w1Encode w1) ∧
    sig.z = z ∧
    sig.h = prims.makeHintVec (-ct0) (w - cs2 + ct0) ∧
    polyVecNorm z < p.gamma1 - p.beta ∧
    polyVecNorm (prims.lowBitsVec (w - cs2)) < p.gamma2 - p.beta ∧
    polyVecNorm ct0 < p.gamma2 ∧
    prims.hintWeight sig.h ≤ p.omega := by
  unfold fipsSignAttempt at h
  dsimp only at h
  split_ifs at h with h_outer h_inner
  rw [Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl, rfl, h_outer.1, h_outer.2, h_inner.1, h_inner.2⟩

/-- Correctness of FIPS ML-DSA, conditional on the algebraic key identity (`h_wApprox_eq`)
and the challenge-product norm bound (`h_cs2_bound`, for the challenge `c = SampleInBall(c̃)`).
These conditions follow from the key generation relationship `t = A·s₁ + s₂`,
`(t₁,t₀) = Power2Round(t)`, and the weight/norm structure of challenge polynomials and
secret keys. -/
theorem fipsSign_fipsVerify_correct'
    (pk : PublicKey p prims) (sk : SecretKey p)
    (msg : List Byte) (sig : FIPSSignature p prims)
    (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ)
    (h_valid : validKeyPair p prims pk sk = true)
    (h_useHint_makeHint : ∀ z r : Rq,
      polyNorm z ≤ p.gamma2 →
      prims.useHint (prims.makeHint z r) r = prims.highBits (r + z))
    (h_hide_low : ∀ (r s : Rq) (b : ℕ),
      polyNorm s ≤ b →
      polyNorm (prims.lowBits r) + b < p.gamma2 →
      prims.highBits (r + s) = prims.highBits r)
    (h_wApprox_eq : ∀ (c : Rq) (y : RqVec p.l),
      computeWApprox p prims (prims.expandA pk.rho) c
        (y + c • sk.s1) pk.t1 =
      (prims.expandA pk.rho) * y - c • sk.s2 + c • sk.t0)
    (h_cs2_bound : ∀ (j : Fin p.k),
      LatticeCrypto.cInfNorm ((prims.sampleInBall sig.cTilde • sk.s2).get j) ≤ p.beta)
    (h_sign : fipsSignLoop p prims sk
      (prims.expandA pk.rho) (prims.hashMessage sk.tr msg)
      rhoDoublePrime maxAttempts = some sig) :
    fipsVerify p prims pk msg sig = true := by
  classical
  -- Recover the honest seed so the public-key / secret-key fields line up.
  obtain ⟨seed, hkeygen⟩ := (validKeyPair_eq_true_iff p prims pk sk).mp h_valid
  -- The transcript hash `tr` stored in `sk` equals `H(pk.ρ, pk.t₁)` used by `verify`.
  have h_tr : sk.tr = prims.hashPublicKey pk.rho pk.t1 := by
    simp only [keyGenFromSeed, Prod.mk.injEq] at hkeygen
    obtain ⟨hpk, hsk⟩ := hkeygen
    subst hpk hsk; rfl
  -- Extract the successful signing attempt and all its structural data and bounds.
  obtain ⟨i, -, h_attempt⟩ := fipsSignLoop_exists p prims sk _ _ _ _ _ h_sign
  obtain ⟨h_cTilde, h_z, h_h, h_zNorm, h_r0Norm, h_ct0Norm, h_weight⟩ :=
    fipsSignAttempt_spec p prims sk _ _ _ _ _ h_attempt
  -- Names for the attempt-local quantities.
  set y := prims.expandMask rhoDoublePrime (i * p.l) with hy_def
  set aHat := prims.expandA pk.rho with haHat_def
  set w := aHat * y with hw_def
  set c := prims.sampleInBall sig.cTilde with hc_def
  -- The challenge in `verify` is `sampleInBall sig.cTilde`; fold it through the spec data,
  -- whose hypotheses were generated with the unfolded commitment-hash form.
  rw [h_cTilde] at hc_def
  rw [← hc_def] at h_z h_h h_ct0Norm h_r0Norm h_zNorm
  -- Unfold `verify` and discharge its three Boolean checks.  Verify recomputes
  -- `tr = H(pk.ρ, pk.t₁)`, which equals the `sk.tr` used during signing.
  unfold fipsVerify
  simp only [← h_tr, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- `‖z‖∞ < γ₁ - β`.
    rw [h_z]; exact h_zNorm
  · -- RO consistency: the recomputed commitment hash equals `sig.cTilde`.
    -- `wApprox = A·y - c·s₂ + c·t₀` via the key identity (with `z = y + c·s₁`).
    have hwa : computeWApprox p prims aHat c sig.z pk.t1
        = aHat * y - c • sk.s2 + c • sk.t0 := by
      rw [h_z]
      exact h_wApprox_eq c y
    rw [hwa]
    -- `sig.h = makeHintVec (-c·t₀) (w - c·s₂ + c·t₀)`, so UseHint recovers `HighBits(w)`.
    have h_recover : prims.useHintVec sig.h (aHat * y - c • sk.s2 + c • sk.t0)
        = prims.highBitsVec w := by
      rw [h_h]
      exact useHintVec_makeHintVec_eq_highBitsVec p prims h_useHint_makeHint h_hide_low
        w (c • sk.s2) (c • sk.t0) h_ct0Norm h_r0Norm (fun j => h_cs2_bound j)
    rw [h_recover]
    -- The recomputed commitment hash now matches the one recorded during signing.
    rw [h_cTilde]
  · -- Hint weight `≤ ω`.
    exact h_weight

/-- Correctness of FIPS ML-DSA: if a key pair was generated honestly and signing succeeds,
then verification accepts the resulting signature.

The proof requires deriving the algebraic key identity and product norm bounds from
`validKeyPair` and `Primitives.Laws`; see `fipsSign_fipsVerify_correct'` for the
conditional version. -/
theorem fipsSign_fipsVerify_correct
    (pk : PublicKey p prims) (sk : SecretKey p)
    (msg : List Byte) (sig : FIPSSignature p prims)
    (rhoDoublePrime : Bytes 64) (maxAttempts : ℕ)
    (h_valid : validKeyPair p prims pk sk = true)
    (h_laws : Primitives.Laws prims nttOps)
    (h_sign : fipsSignLoop p prims sk
      (prims.expandA pk.rho) (prims.hashMessage sk.tr msg)
      rhoDoublePrime maxAttempts = some sig) :
    fipsVerify p prims pk msg sig = true := by
  classical
  obtain ⟨seed, hkeygen⟩ := (validKeyPair_eq_true_iff p prims pk sk).mp h_valid
  -- Honest secret vector `s₂` is `η`-bounded, so the challenge product is `β`-bounded.
  have hs2_bound : polyVecBounded sk.s2 p.eta := by
    have h := congrArg Prod.snd hkeygen
    simp only [keyGenFromSeed] at h
    rw [← h]
    exact (h_laws.expandS_bound _).2
  have hcs2_norm : polyVecNorm (prims.sampleInBall sig.cTilde • sk.s2) ≤ p.beta :=
    h_laws.sampleInBall_smul_bound sig.cTilde sk.s2 hs2_bound
  refine fipsSign_fipsVerify_correct' p prims pk sk msg sig rhoDoublePrime maxAttempts
    h_valid h_laws.useHint_makeHint h_laws.hide_low
    (keyGenFromSeed_wApprox_eq p prims h_laws seed hkeygen) ?_ h_sign
  -- Componentwise: each component of `c·s₂` is bounded by the vector norm bound `β`.
  intro j
  have hj : polyNorm ((prims.sampleInBall sig.cTilde • sk.s2).get j) ≤ p.beta :=
    le_trans (LatticeCrypto.PolyVec.component_cInfNorm_le normOps
      (prims.sampleInBall sig.cTilde • sk.s2) j) hcs2_norm
  unfold polyNorm normOps at hj
  simpa [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView,
    LatticeCrypto.cInfNorm] using hj

end MLDSA
