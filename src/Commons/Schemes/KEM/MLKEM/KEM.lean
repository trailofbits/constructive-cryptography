import Commons.Schemes.KEM.MLKEM.Internal
import Commons.Definitions.KEM
import Mathlib.Data.FinEnum

/-!
# ML-KEM Top-Level KEM

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLKEM/KEM.lean` at `f5119c6`), by Quang Dao.

The top-level algorithms of FIPS 203 Section 7 on the deterministic internal algorithms of
`Commons.Schemes.KEM.MLKEM.Internal`: the input checks, checked decapsulation, and ML-KEM as a
`Commons.KEM`, with key generation from uniform seeds `d, z` and encapsulation of a uniform
message `m`.
-/



namespace MLKEM

variable {params : Params}

/-- Check the semantic public-key component against the abstract byte-level canonicality test. -/
def encapsulationKeyCheck (encoding : Encoding params) [DecidableEq encoding.EncodedTHat]
    (ek : EncapsulationKey params encoding) : Bool :=
  encoding.publicKeyCanonical ek.tHatEncoded

@[simp] theorem encapsulationKeyCheck_keygenFromSeed_eq_true (ring : NTTRingOps)
    (encoding : Encoding params) [DecidableEq encoding.EncodedTHat]
    (prims : Primitives params encoding) (d : Seed32) :
    encapsulationKeyCheck encoding (KPKE.keygenFromSeed ring encoding prims d).1 = true := by
  unfold encapsulationKeyCheck KPKE.keygenFromSeed
  simp

@[simp] theorem encapsulationKeyCheck_keygenInternal_eq_true (ring : NTTRingOps)
    (encoding : Encoding params) [DecidableEq encoding.EncodedTHat]
    (prims : Primitives params encoding) (d z : Seed32) :
    encapsulationKeyCheck encoding (keygenInternal ring encoding prims d z).1 = true := by
  simp [keygenInternal]

/-- Check the semantic decapsulation key against the stored encapsulation-key hash. -/
def decapsulationKeyCheck (encoding : Encoding params) (prims : Primitives params encoding)
    (dk : DecapsulationKey params encoding) : Bool :=
  encapsulationKeyHash encoding prims dk.ekPKE == dk.ekHash

/-- In the semantic model, ciphertexts are already well-typed, so the top-level runtime check is
reduced to `true`. A later byte-level refinement can strengthen this predicate. -/
def ciphertextCheck (encoding : Encoding params)
    (_c : Ciphertext params encoding) : Bool := true

/-- Combined decapsulation input check. -/
def decapsulationInputCheck (encoding : Encoding params) (prims : Primitives params encoding)
    (dk : DecapsulationKey params encoding) (c : Ciphertext params encoding) : Bool :=
  decapsulationKeyCheck encoding prims dk && ciphertextCheck encoding c

/-- `ML-KEM.Decaps` with its input checks made explicit. -/
def decaps (ring : NTTRingOps) (encoding : Encoding params)
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV]
    (prims : Primitives params encoding) (dk : DecapsulationKey params encoding)
    (c : Ciphertext params encoding) : Option SharedSecret :=
  if decapsulationInputCheck encoding prims dk c then
    some (decapsInternal ring encoding prims dk c)
  else
    none

/-- **ML-KEM as a key encapsulation mechanism** (FIPS 203, Algorithms 19–21): key generation
from uniform seeds `d, z`, encapsulation of a uniform message `m`, and checked decapsulation with
implicit rejection. Encapsulation takes an encapsulation key that passed `encapsulationKeyCheck`. -/
noncomputable def toKEM (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) [DecidableEq encoding.EncodedU]
    [DecidableEq encoding.EncodedV] :
    Commons.KEM (EncapsulationKey params encoding) (DecapsulationKey params encoding)
      (Ciphertext params encoding) SharedSecret where
  gen := ⟨Probability.Distribution.fTransform
      (fun dz : Seed32 × Seed32 => keygenInternal ring encoding prims dz.1 dz.2)
      (Probability.Distribution.uniform (Seed32 × Seed32)),
    Probability.Distribution.fTransform_isProbDist _ Probability.Distribution.uniform_isProbDist⟩
  encaps ek := ⟨Probability.Distribution.fTransform
      (fun m : Message => ((encapsInternal ring encoding prims ek m).2,
        (encapsInternal ring encoding prims ek m).1))
      (Probability.Distribution.uniform Message),
    Probability.Distribution.fTransform_isProbDist _ Probability.Distribution.uniform_isProbDist⟩
  decaps := decaps ring encoding prims

end MLKEM
