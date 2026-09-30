import Commons.Schemes.KEM.MLKEM.Primitives
import Commons.Schemes.KEM.MLKEM.Concrete.NTT
import Commons.Schemes.KEM.MLKEM.Concrete.Encoding
import Commons.Schemes.KEM.MLKEM.Concrete.CBD
import Commons.Schemes.Hash.Keccak

/-!
# Concrete ML-KEM Instance

Adapted from VCVio (`Verified-zkEVM/VCVio`, `Extern/MLKEM/Instance.lean` at `f5119c6`), by Quang Dao.

Wires the pure-Lean NTT, encoding, and CBD implementations together with the SHA-3 and SHAKE
functions of `Commons.Schemes.Hash.Keccak` to produce fully executable `NTTRingOps`, `Encoding`,
and `Primitives` instances for ML-KEM.
-/



namespace MLKEM.Concrete

open MLKEM

/-! ## SampleNTT (FIPS 203 Algorithm 7) — rejection sampling from SHAKE-128 -/

/-- Rejection-sample 256 NTT-domain coefficients from a SHAKE-128 byte stream.
    Each 3-byte group yields up to two candidates `d₁, d₂ ∈ [0, 4096)`;
    a candidate is accepted iff it is `< q = 3329`. -/
def rejectionSample (stream : ByteArray) : Array Coeff := Id.run do
  let mut acc : Array Coeff := Array.mkEmpty 256
  let numChunks := stream.size / 3
  for chunk in [0:numChunks] do
    if acc.size < 256 then
      let pos := chunk * 3
      let b0 := stream.get! pos |>.toNat
      let b1 := stream.get! (pos + 1) |>.toNat
      let b2 := stream.get! (pos + 2) |>.toNat
      let d1 := b0 + 256 * (b1 % 16)
      let d2 := b1 / 16 + 16 * b2
      if d1 < modulus && acc.size < 256 then
        acc := acc.push (d1 : Coeff)
      if d2 < modulus && acc.size < 256 then
        acc := acc.push (d2 : Coeff)
  return acc

/-- Reject silent zero-padding by requiring a full 256-coefficient output. -/
def requireFullRejectionSample (coeffs : Array Coeff) : Array Coeff :=
  if _h : coeffs.size = ringDegree then
    coeffs
  else
    panic! s!"ML-KEM rejection sampler produced {coeffs.size} coefficients; expected {ringDegree}"

/-- FIPS 203 Algorithm 7: sample an NTT-domain polynomial from `SHAKE-128(ρ ‖ j ‖ i)`. -/
def concreteSampleNTT (rho : Seed32) (j i : Nat) : Tq :=
  let input := vectorToByteArray rho |>.push j.toUInt8 |>.push i.toUInt8
  -- A fixed 840-byte squeeze is enough to cover the acceptance process in practice.
  let stream := Commons.Keccak.shake128 input 840
  let coeffs := requireFullRejectionSample (rejectionSample stream)
  ⟨Vector.ofFn fun ⟨idx, _⟩ => coeffs.getD idx 0⟩

/-! ## PRF + CBD (FIPS 203 Algorithms 6 + 8) -/

/-- `PRF_η(σ, N) = SHAKE-256(σ ‖ N, 64η)` followed by `CBD_η`. -/
def prfCBD (eta : Nat) (sigma : Seed32) (n : Nat) : Rq :=
  let input := vectorToByteArray sigma |>.push n.toUInt8
  let prfOutput := Commons.Keccak.shake256 input (64 * eta)
  samplePolyCBD eta prfOutput

/-! ## Hash wrappers -/

/-- `G(input) = SHA3-512(input)`, split into two 32-byte halves. -/
def hashG (input : ByteArray) : Seed32 × Seed32 :=
  let hash := Commons.Keccak.sha3_512 input
  (byteArrayToVector hash 0 32, byteArrayToVector hash 32 32)

/-- `H(input) = SHA3-256(input)` as a 32-byte vector. -/
def hashH (input : ByteArray) : Vector UInt8 32 :=
  byteArrayToVector (Commons.Keccak.sha3_256 input) 0 32

/-! ## Concrete `Primitives` instance -/

/-- The concrete `Primitives` instance for a parameter set, on the concrete encoding. -/
def concretePrimitives (params : Params) : Primitives params (concreteEncoding params) where
  gKeygen := fun d =>
    hashG (vectorToByteArray d |>.push params.k.toUInt8)
  sampleNTT := fun rho j i =>
    concreteSampleNTT rho j.val i.val
  prfEta1 := prfCBD params.eta1
  prfEta2 := prfCBD params.eta2
  gEncaps := fun m ekHash =>
    hashG (vectorToByteArray m ++ vectorToByteArray ekHash)
  hEncapsulationKey := fun tHatEncoded rho =>
    hashH (vectorToByteArray tHatEncoded ++ vectorToByteArray rho)
  jReject := fun z uEncoded vEncoded =>
    byteArrayToVector
      (Commons.Keccak.shake256
        (vectorToByteArray z ++ vectorToByteArray uEncoded ++ vectorToByteArray vEncoded) 32) 0 32

/-! ## Assembled ML-KEM-768 bundle -/

/-- Concrete encoding for ML-KEM-768. -/
abbrev mlkem768Encoding : Encoding mlkem768 := concreteEncoding mlkem768

/-- Concrete encoding for ML-KEM-512. -/
abbrev mlkem512Encoding : Encoding mlkem512 := concreteEncoding mlkem512

/-- Concrete encoding for ML-KEM-1024. -/
abbrev mlkem1024Encoding : Encoding mlkem1024 := concreteEncoding mlkem1024

/-- Encoding roundtrip laws for ML-KEM-512. -/
theorem mlkem512EncodingLaws : mlkem512Encoding.Laws :=
  concreteEncodingLaws mlkem512
    (by norm_num [mlkem512, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem512, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem512, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem512, ParameterSet.params, modulus, Nat.shiftLeft_eq])

/-- Encoding roundtrip laws for ML-KEM-768. -/
theorem mlkem768EncodingLaws : mlkem768Encoding.Laws :=
  concreteEncodingLaws mlkem768
    (by norm_num [mlkem768, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem768, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem768, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem768, ParameterSet.params, modulus, Nat.shiftLeft_eq])

/-- Encoding roundtrip laws for ML-KEM-1024. -/
theorem mlkem1024EncodingLaws : mlkem1024Encoding.Laws :=
  concreteEncodingLaws mlkem1024
    (by norm_num [mlkem1024, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem1024, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem1024, ParameterSet.params, modulus, Nat.shiftLeft_eq])
    (by norm_num [mlkem1024, ParameterSet.params, modulus, Nat.shiftLeft_eq])

/-- Concrete primitives for ML-KEM-512. -/
def mlkem512Primitives : Primitives mlkem512 mlkem512Encoding :=
  concretePrimitives mlkem512

/-- Concrete primitives for ML-KEM-768. -/
def mlkem768Primitives : Primitives mlkem768 mlkem768Encoding :=
  concretePrimitives mlkem768

/-- Concrete primitives for ML-KEM-1024. -/
def mlkem1024Primitives : Primitives mlkem1024 mlkem1024Encoding :=
  concretePrimitives mlkem1024

end MLKEM.Concrete
