import Commons.Schemes.KEM.MLKEM.Params
import Commons.Schemes.Lattice.SchoolbookCert
import Commons.Schemes.Lattice.Transform

/-!
# ML-KEM Arithmetic Assembly

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLKEM/Arithmetic.lean` at `f5119c6`), by Quang Dao.

Instantiates the generic negacyclic ring architecture for the ML-KEM coefficient
ring `ℤ_q[X]/(X^256 + 1)` where `q = 3329`, and exposes scheme-local type
and operation aliases consumed by downstream ML-KEM files.

Provides:
- `coeffRing` / `polyBackend` / `polyKernel` / `coeffSemantics`: the bundled
  executable ring, backend, kernel, and proof-facing semantics.
- `Rq`, `Tq`, `RqVec`, `TqVec`, `TqMatrix`, `Quotient`: scheme-local
  carrier aliases.
- `negacyclicMul`, `quotientOfRq`: coefficient-domain multiplication and
  quotient embedding.
- `NTTRingOps` / `NTTRingLaws`: transform-domain interface and law aliases.

The `NeZero modulus` instance makes `Coeff` finite.

ML-KEM does not use rounding or norm bundles at the arithmetic layer.

This module is mixed: the executable aliases are computable, while
`coeffSemantics` and `quotientOfRq` are `noncomputable`.
-/



namespace MLKEM

/-- Coefficients in the ML-KEM base ring. -/
abbrev Coeff := ZMod modulus

/-- The FIPS 203 modulus `q = 3329` is nonzero, so `Coeff = ZMod modulus` is a finite,
sampleable type. -/
instance : NeZero modulus := ⟨by
  unfold modulus
  norm_num
⟩

/-- The canonical bundled coefficient-domain ring used by the current ML-KEM development. -/
abbrev coeffRing : LatticeCrypto.NegacyclicRing Coeff :=
  LatticeCrypto.vectorNegacyclicRing Coeff ringDegree

/-- The semantic backend used by the bundled ML-KEM ring. -/
abbrev polyBackend : LatticeCrypto.PolyBackend Coeff :=
  coeffRing.backend

/-- The executable kernel used by the bundled ML-KEM ring. -/
abbrev polyKernel : LatticeCrypto.PolyKernel Coeff polyBackend :=
  coeffRing.kernel

/-- The proof-facing semantic interpretation of the bundled ML-KEM ring. -/
noncomputable abbrev coeffSemantics : LatticeCrypto.NegacyclicRingSemantics coeffRing :=
  LatticeCrypto.vectorNegacyclicSemantics Coeff (by norm_num [ringDegree])

/-- The proof-facing quotient `Z_q[X] / (X^256 + 1)`. -/
abbrev Quotient := LatticeCrypto.NegacyclicRingSemantics.Quotient coeffSemantics

/-- Coefficient-domain polynomials in `R_q = Z_q[X] / (X^256 + 1)`. -/
abbrev Rq := coeffRing.Poly

/-- Transform-domain polynomials for the ML-KEM bundled ring. -/
abbrev Tq := LatticeCrypto.TransformPoly coeffRing

instance : DecidableEq Rq := by
  change DecidableEq (LatticeCrypto.Poly Coeff ringDegree)
  infer_instance

instance : DecidableEq Tq := by
  change DecidableEq (LatticeCrypto.TransformPoly coeffRing)
  infer_instance

/-- Length-`k` vectors over `R_q`. -/
abbrev RqVec (k : ℕ) := LatticeCrypto.PolyVec Rq k

/-- Length-`k` vectors over `T_q`. -/
abbrev TqVec (k : ℕ) := LatticeCrypto.PolyVec Tq k

/-- `rows × cols` row-major matrices over `T_q`. -/
abbrev TqMatrix (rows cols : ℕ) := LatticeCrypto.PolyMatrix Tq rows cols

/-- The quotient interpretation of a coefficient-domain polynomial. -/
noncomputable abbrev quotientOfRq (f : Rq) : Quotient :=
  coeffSemantics.quotientOf f

/-- The canonical executable negacyclic multiplication on `Rq`. -/
abbrev negacyclicMul (f g : Rq) : Rq :=
  coeffRing.mul f g

/-- Optional transform-domain acceleration specialized to ML-KEM carriers. -/
abbrev NTTRingOps := LatticeCrypto.TransformOps coeffRing Tq

/-- Proof-oriented transform laws specialized to ML-KEM carriers. -/
abbrev NTTRingLaws (ops : NTTRingOps) := LatticeCrypto.TransformOps.Laws ops

end MLKEM
