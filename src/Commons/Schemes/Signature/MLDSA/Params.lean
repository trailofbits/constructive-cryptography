import Mathlib.Data.ZMod.Defs

/-!
# ML-DSA Parameters

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLDSA/Params.lean` at `f5119c6`), by Quang Dao.

This file collects the fixed constants and approved parameter sets from FIPS 204.
The development stays generic over the variable parameters while exposing the three
named NIST-approved instantiations.

## References

- NIST FIPS 204, Section 4 (Table 1: ML-DSA parameter sets)
-/



namespace MLDSA

/-- Byte values used by the concrete ML-DSA encodings and hash inputs. -/
abbrev Byte := UInt8

/-- Fixed-length byte vectors used by the FIPS 204 interfaces. -/
abbrev Bytes (n : ℕ) := Vector Byte n

/-- The variable parameters that distinguish the approved ML-DSA instantiations. -/
structure Params where
  /-- Number of rows in the matrix A. -/
  k : ℕ
  /-- Number of columns in the matrix A. -/
  l : ℕ
  /-- Private key coefficient range: secret vectors have coefficients in [-η, η]. -/
  eta : ℕ
  /-- Number of ±1 coefficients in the challenge polynomial c. -/
  tau : ℕ
  /-- Collision strength of c̃ (in bits). -/
  lambda : ℕ
  /-- Coefficient range of the masking vector y: coefficients in [-(γ₁-1), γ₁-1]. -/
  gamma1 : ℕ
  /-- Low-order rounding range: 2*γ₂ divides q-1. -/
  gamma2 : ℕ
  /-- Maximum number of 1's in the hint vector h. -/
  omega : ℕ
deriving Repr, DecidableEq

/-- The fixed ring degree used by FIPS 204. -/
def ringDegree : ℕ := 256

/-- The fixed modulus used by FIPS 204: q = 2^23 - 2^13 + 1 = 8380417. -/
def modulus : ℕ := 8380417

/-- The distinguished root of unity: ζ = 1753 is a 512th root of unity in Z_q. -/
def zeta : ZMod modulus := 1753

/-- Number of dropped bits from t in Power2Round: d = 13. -/
def droppedBits : ℕ := 13

namespace Params

/-- β = τ · η, the bound on ‖c · s‖∞ used in rejection sampling. -/
def beta (params : Params) : ℕ := params.tau * params.eta

end Params

/-- The approved named parameter sets from FIPS 204. -/
inductive ParameterSet where
  | MLDSA_44
  | MLDSA_65
  | MLDSA_87
deriving Repr, DecidableEq

namespace ParameterSet

/-- Interpret a named parameter set as the corresponding parameter record. -/
def params : ParameterSet → Params
  | .MLDSA_44 => {
      k := 4, l := 4, eta := 2, tau := 39, lambda := 128,
      gamma1 := 2^17, gamma2 := (modulus - 1) / 88, omega := 80 }
  | .MLDSA_65 => {
      k := 6, l := 5, eta := 4, tau := 49, lambda := 192,
      gamma1 := 2^19, gamma2 := (modulus - 1) / 32, omega := 55 }
  | .MLDSA_87 => {
      k := 8, l := 7, eta := 2, tau := 60, lambda := 256,
      gamma1 := 2^19, gamma2 := (modulus - 1) / 32, omega := 75 }

end ParameterSet

/-- The approved ML-DSA-44 parameter record. -/
def mldsa44 : Params := ParameterSet.params .MLDSA_44
/-- The approved ML-DSA-65 parameter record. -/
def mldsa65 : Params := ParameterSet.params .MLDSA_65
/-- The approved ML-DSA-87 parameter record. -/
def mldsa87 : Params := ParameterSet.params .MLDSA_87

/-- Recognize the approved FIPS 204 parameter sets. -/
def Params.isApproved (params : Params) : Prop :=
  params = mldsa44 ∨ params = mldsa65 ∨ params = mldsa87

end MLDSA
