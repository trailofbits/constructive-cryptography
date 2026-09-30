import Commons.Schemes.KEM.MLKEM.Concrete.Encoding

/-!
# Concrete CBD Sampling for ML-KEM

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/MLKEM/Concrete/CBD.lean` at `f5119c6`), by Quang Dao.

Pure-Lean executable implementation of FIPS 203 Algorithm 8 (SamplePolyCBD_η).
-/



namespace MLKEM.Concrete

open MLKEM

/-- FIPS 203 Algorithm 8: sample a polynomial from the centered binomial distribution CBD_η.
    Input: `64 * eta` bytes. Output: a polynomial in `R_q`. -/
def samplePolyCBD (eta : Nat) (bytes : ByteArray) : Rq :=
  let bits : Array Nat := Id.run do
    let mut b := Array.mkEmpty (bytes.size * 8)
    for k in [0:bytes.size] do
      for j in [0:8] do
        b := b.push (bitOf (getByteD bytes k) j)
    return b
  Vector.ofFn fun idx =>
    let i := idx.val
    let x := Id.run do
      let mut acc := 0
      for j in [0:eta] do
        acc := acc + bits.getD (2 * i * eta + j) 0
      return acc
    let y := Id.run do
      let mut acc := 0
      for j in [0:eta] do
        acc := acc + bits.getD (2 * i * eta + eta + j) 0
      return acc
    (x : Coeff) - (y : Coeff)

end MLKEM.Concrete
