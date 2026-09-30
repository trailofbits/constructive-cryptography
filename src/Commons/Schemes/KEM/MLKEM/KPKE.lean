import Commons.Schemes.KEM.MLKEM.Encoding
import Commons.Schemes.KEM.MLKEM.Primitives
import Mathlib.Data.FinEnum

/-!
# ML-KEM K-PKE

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLKEM/KPKE.lean` at `f5119c6`), by Quang Dao.

This file gives a spec-level implementation of the `K-PKE` component used by ML-KEM. The
arithmetic, encoding, and primitive operations are supplied abstractly, but the algorithm structure
follows FIPS 203 Section 5 closely.
-/



namespace MLKEM
namespace KPKE

/-- The semantic public key for K-PKE. -/
structure PublicKey (params : Params) (encoding : Encoding params) where
  tHatEncoded : encoding.EncodedTHat
  rho : Seed32

/-- The semantic secret key for K-PKE. -/
structure SecretKey (params : Params) (encoding : Encoding params) where
  sHatEncoded : encoding.EncodedTHat

/-- The semantic ciphertext for K-PKE. -/
structure Ciphertext (params : Params) (encoding : Encoding params) where
  uEncoded : encoding.EncodedU
  vEncoded : encoding.EncodedV

variable {params : Params}
variable {encoding : Encoding params}

/-- Public keys have decidable equality when their encoded polynomial payload does. -/
instance [DecidableEq encoding.EncodedTHat] : DecidableEq (PublicKey params encoding) := by
  intro x y
  cases x
  cases y
  simp only [PublicKey.mk.injEq]
  infer_instance

/-- Secret keys have decidable equality when their encoded polynomial payload does. -/
instance [DecidableEq encoding.EncodedTHat] : DecidableEq (SecretKey params encoding) := by
  intro x y
  cases x
  cases y
  simp only [SecretKey.mk.injEq]
  infer_instance

/-- Ciphertexts have decidable equality when their encoded components do. -/
instance [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV] :
    DecidableEq (Ciphertext params encoding) := by
  intro x y
  cases x
  cases y
  simp only [Ciphertext.mk.injEq]
  infer_instance

/-- Public keys are finite when their encoded polynomial payload is. -/
instance [Fintype encoding.EncodedTHat] : Fintype (PublicKey params encoding) :=
  Fintype.ofEquiv (encoding.EncodedTHat × Seed32)
    ⟨fun x => ⟨x.1, x.2⟩, fun pk => (pk.tHatEncoded, pk.rho), fun _ => rfl, fun _ => rfl⟩

/-- Secret keys are finite when their encoded polynomial payload is. -/
instance [Fintype encoding.EncodedTHat] : Fintype (SecretKey params encoding) :=
  Fintype.ofEquiv encoding.EncodedTHat ⟨fun x => ⟨x⟩, fun sk => sk.sHatEncoded, fun _ => rfl, fun _ => rfl⟩

/-- Ciphertexts are finite when their encoded components are. -/
instance [Fintype encoding.EncodedU] [Fintype encoding.EncodedV] :
    Fintype (Ciphertext params encoding) :=
  Fintype.ofEquiv (encoding.EncodedU × encoding.EncodedV)
    ⟨fun x => ⟨x.1, x.2⟩, fun c => (c.uEncoded, c.vEncoded), fun _ => rfl, fun _ => rfl⟩

/-- K-PKE key generation from an explicit 32-byte seed.

This expands the input seed into the public matrix seed `rho` and sampling seed `sigma`,
samples the secret and error vectors, moves them into the NTT domain, and forms the public
key relation `tHat = Ahat * sHat + eHat` before serializing the public and secret outputs. -/
def keygenFromSeed (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (d : Seed32) :
    PublicKey params encoding × SecretKey params encoding :=
  let (rho, sigma) := prims.gKeygen d
  let aHat := prims.publicMatrix rho
  let s := prims.sampleVecEta1 sigma 0
  let e := prims.sampleVecEta1 sigma params.k
  let sHat := ring.nttVec s
  let eHat := ring.nttVec e
  let tHat := ring.matVecMul aHat sHat + eHat
  ({ tHatEncoded := encoding.byteEncode12Vec tHat, rho := rho },
    { sHatEncoded := encoding.byteEncode12Vec sHat })

/-- K-PKE encryption with explicit coins.

This decodes the public key, deterministically derives the ephemeral secret and noise terms from
`coins`, computes the ML-KEM ciphertext components `(u, v)`, and then compresses and serializes
them into the abstract ciphertext representation. -/
def encrypt (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (ek : PublicKey params encoding) (msg : Message)
    (coins : Coins) : Ciphertext params encoding :=
  let tHat := encoding.byteDecode12Vec ek.tHatEncoded
  let aHat := prims.publicMatrix ek.rho
  let y := prims.sampleVecEta1 coins 0
  let e1 := prims.sampleVecEta2 coins params.k
  let e2 := prims.prfEta2 coins (2 * params.k)
  let yHat := ring.nttVec y
  let u := ring.invNTTVec (ring.matTransposeVecMul aHat yHat) + e1
  let mu := encoding.decompress1 (encoding.byteDecode1 msg)
  let v := ring.invNTT (ring.dot tHat yHat) + e2 + mu
  { uEncoded := encoding.byteEncodeDUVec (encoding.compressDU u)
    vEncoded := encoding.byteEncodeDV (encoding.compressDV v) }

/-- K-PKE decryption.

This decodes the ciphertext into its semantic `(u, v)` components, subtracts the secret-key
contribution from `v`, and re-encodes the resulting message representative as the recovered
32-byte plaintext. -/
def decrypt (ring : NTTRingOps) (encoding : Encoding params)
    (_prims : Primitives params encoding) (dk : SecretKey params encoding)
    (c : Ciphertext params encoding) : Message :=
  let (u', v') := encoding.decodeCiphertext c.uEncoded c.vEncoded
  let sHat := encoding.byteDecode12Vec dk.sHatEncoded
  let w := v' - ring.invNTT (ring.dot sHat (ring.nttVec u'))
  encoding.byteEncode1 (encoding.compress1 w)

end KPKE
end MLKEM
