import Commons.Schemes.Signature.MLDSA.Encoding
import Commons.Schemes.Signature.MLDSA.Concrete.Rounding
import Commons.Schemes.Signature.MLDSA.Concrete.NTT
import Commons.Schemes.Signature.MLDSA.Concrete.Sampling
import Commons.Schemes.Signature.MLDSA.Concrete.Encoding
import Mathlib.Data.FinEnum

/-!
# Concrete ML-DSA Instance

Adapted from VCVio (`Verified-zkEVM/VCVio`, `Extern/MLDSA/Instance.lean` at `f5119c6`), by Quang Dao.

Wires the concrete rounding, NTT, sampling, hashing, and byte encoding layers into the
abstract `Primitives` and `Encoding` bundles used by the ML-DSA specification. The encoded keys
and signatures are byte strings of the FIPS 204 lengths, `Bytes (publicKeyBytes p)`,
`Bytes (secretKeyBytes p)` and `Bytes (signatureBytes p)`.
-/



namespace MLDSA.Concrete

open MLDSA

def hintWeightVec {k : Nat} (h : Vector Hint k) : Nat :=
  h.toList.foldl (fun acc hi => acc + MLDSA.Concrete.hintWeight hi) 0

/-- Concrete ML-DSA primitives obtained by wiring the concrete FIPS 204 algorithms into the
abstract `Primitives` interface. -/
def concretePrimitives (p : Params) : Primitives p where
  High := High
  Power2High := Power2High
  Hint := Hint
  expandSeed := fun seed => MLDSA.Concrete.expandSeed seed p
  expandA := fun rho => MLDSA.Concrete.expandA rho p
  expandS := fun rhoPrime => MLDSA.Concrete.expandS rhoPrime p
  expandMask := fun rhoPrime kappa => MLDSA.Concrete.expandMask rhoPrime kappa p
  sampleInBall := fun cTilde => MLDSA.Concrete.sampleInBall p cTilde
  hashMessage := MLDSA.Concrete.hashMessage
  hashPrivateSeed := MLDSA.Concrete.hashPrivateSeed
  hashCommitment := fun mu w1 =>
    MLDSA.Concrete.hashCommitmentBytes mu (ByteArray.mk w1.toArray) p
  hashPublicKey := fun rho t1 =>
    MLDSA.Concrete.hashPublicKeyBytes (MLDSA.Concrete.pkEncode p rho t1)
  highBits := MLDSA.Concrete.highBits p
  highBitsShift := MLDSA.Concrete.highBitsShift p
  lowBits := MLDSA.Concrete.lowBits p
  makeHint := MLDSA.Concrete.makeHint p
  useHint := MLDSA.Concrete.useHint p
  power2Round := MLDSA.Concrete.power2Round
  power2RoundShift := MLDSA.Concrete.power2RoundShift
  w1Encode := MLDSA.Concrete.w1Encode p
  hintWeight := hintWeightVec

/-- The high-order and power-2 representatives of the concrete primitives are polynomials, and
their hints bit vectors, so they are finite. Instance search does not unfold `concretePrimitives`,
so the instances are stated on its projections. -/
instance instFintypeConcretePower2High (p : Params) : Fintype (concretePrimitives p).Power2High :=
  inferInstanceAs (Fintype Rq)

instance instDecidableEqConcretePower2High (p : Params) :
    DecidableEq (concretePrimitives p).Power2High :=
  inferInstanceAs (DecidableEq Rq)

instance instFintypeConcreteHint (p : Params) : Fintype (concretePrimitives p).Hint :=
  inferInstanceAs (Fintype (Vector Bool ringDegree))

instance instDecidableEqConcreteHint (p : Params) : DecidableEq (concretePrimitives p).Hint :=
  inferInstanceAs (DecidableEq (Vector Bool ringDegree))

/-- Concrete ML-DSA byte encoding bundle for a parameter set. -/
def concreteEncoding (p : Params) : Encoding p (concretePrimitives p) where
  EncodedPK := Bytes (publicKeyBytes p)
  EncodedSK := Bytes (secretKeyBytes p)
  EncodedSig := Bytes (signatureBytes p)
  pkEncode rho t1 := ofByteArray (MLDSA.Concrete.pkEncode p rho t1) (pkEncode_size p rho t1)
  pkDecode bytes := MLDSA.Concrete.pkDecode p (vectorToByteArray bytes)
  skEncode rho key tr s1 s2 t0 :=
    ofByteArray (MLDSA.Concrete.skEncode p rho key tr s1 s2 t0) (skEncode_size p rho key tr s1 s2 t0)
  skDecode bytes := MLDSA.Concrete.skDecode p (vectorToByteArray bytes)
  sigEncode cTilde z h :=
    ofByteArray (MLDSA.Concrete.sigEncode p cTilde z h) (sigEncode_size p cTilde z h)
  sigDecode bytes := MLDSA.Concrete.sigDecode p (vectorToByteArray bytes)

/-- The encoded keys and signatures are fixed-length byte strings (FIPS 204, Table 2). Instance
search does not unfold `concreteEncoding`, so the instances are stated on its projections. -/
instance instFintypeConcreteEncodedPK (p : Params) : Fintype (concreteEncoding p).EncodedPK :=
  inferInstanceAs (Fintype (Bytes (publicKeyBytes p)))

instance instFintypeConcreteEncodedSK (p : Params) : Fintype (concreteEncoding p).EncodedSK :=
  inferInstanceAs (Fintype (Bytes (secretKeyBytes p)))

instance instFintypeConcreteEncodedSig (p : Params) : Fintype (concreteEncoding p).EncodedSig :=
  inferInstanceAs (Fintype (Bytes (signatureBytes p)))

instance instDecidableEqConcreteEncodedPK (p : Params) : DecidableEq (concreteEncoding p).EncodedPK :=
  inferInstanceAs (DecidableEq (Bytes (publicKeyBytes p)))

instance instDecidableEqConcreteEncodedSK (p : Params) : DecidableEq (concreteEncoding p).EncodedSK :=
  inferInstanceAs (DecidableEq (Bytes (secretKeyBytes p)))

instance instDecidableEqConcreteEncodedSig (p : Params) :
    DecidableEq (concreteEncoding p).EncodedSig :=
  inferInstanceAs (DecidableEq (Bytes (signatureBytes p)))

/-- Concrete primitives specialized to ML-DSA-44. -/
def mldsa44Primitives : Primitives mldsa44 :=
  concretePrimitives mldsa44

/-- Concrete primitives specialized to ML-DSA-65. -/
def mldsa65Primitives : Primitives mldsa65 :=
  concretePrimitives mldsa65

/-- Concrete primitives specialized to ML-DSA-87. -/
def mldsa87Primitives : Primitives mldsa87 :=
  concretePrimitives mldsa87

/-- Concrete encoding bundle specialized to ML-DSA-44. -/
def mldsa44Encoding : Encoding mldsa44 mldsa44Primitives :=
  concreteEncoding mldsa44

/-- Concrete encoding bundle specialized to ML-DSA-65. -/
def mldsa65Encoding : Encoding mldsa65 mldsa65Primitives :=
  concreteEncoding mldsa65

/-- Concrete encoding bundle specialized to ML-DSA-87. -/
def mldsa87Encoding : Encoding mldsa87 mldsa87Primitives :=
  concreteEncoding mldsa87

end MLDSA.Concrete
