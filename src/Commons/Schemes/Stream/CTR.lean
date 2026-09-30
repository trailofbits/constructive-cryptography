import Commons.Schemes.Bytes
import Commons.Definitions.Ideal
import Mathlib.Data.List.Iterate

/-!
# Counter mode

CTR mode (NIST SP 800-38A, §6.5) over a block function on 128-bit blocks. The counter blocks
`T₁, T₂, …` follow from an initial block by the standard incrementing function on the last 32 bits
(Appendix B.1); their images `Oⱼ = CIPH(Tⱼ)` are the key stream, and the message is its exclusive or
with the key stream, the last block truncated. Decryption is the same function. From a nonce
followed by a zero counter as the initial block (Appendix B.2), it is a nonce-based stream cipher,
and as a converter it runs on any block function answering at the interface `Evaluation`: “all of
the counters must be distinct” (§6.5), so nonce uniqueness is the caller's obligation.

## Main definitions

* `CTR.inc32`, `CTR.counterBlocks`: the standard incrementing function and the counter blocks
* `CTR.crypt E T₁`: CTR encryption and decryption under the block function `E`
* `CTR.initialBlock nonce`: the initial block of a nonce
* `StreamCipher ℓ`: the interface of a nonce-based stream cipher on byte strings of length at
  most `ℓ`
* `CTR ℓ`: CTR as a converter from `Evaluation (Bytes 16) (Bytes 16)` to `StreamCipher ℓ`

## Main statements

* `CTR.crypt_crypt`: decryption inverts encryption
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL
open scoped SystemAlgebra.DSL

namespace CTR

/-- The value of the last four bytes of a block, big-endian. -/
def counter (T : Bytes 16) : ℕ :=
  (T.toList.drop 12).foldl (fun n b => 256 * n + b.toNat) 0

/-- `inc₃₂` (SP 800-38A, Appendix B.1): the last 32 bits incremented modulo `2³²`, the first 96
kept. -/
def inc32 (T : Bytes 16) : Bytes 16 :=
  let value := (counter T + 1) % 2 ^ 32
  Vector.ofFn fun i => if i.val < 12 then T[i] else (value / 2 ^ (8 * (15 - i.val))).toUInt8

/-- The `n` counter blocks `T₁, inc₃₂(T₁), …`. -/
def counterBlocks (T₁ : Bytes 16) (n : ℕ) : List (Bytes 16) := List.iterate inc32 T₁ n

/-- The number of blocks of a message of `length` bytes. -/
def blockCount (length : ℕ) : ℕ := (length + 15) / 16

/-- The message XORed with the concatenated output blocks, as far as the message goes. -/
def xorStream (message : List UInt8) (outputs : List (Bytes 16)) : List UInt8 :=
  List.zipWith (· ^^^ ·) message (outputs.flatMap Vector.toList)

/-- **CTR encryption** (SP 800-38A, §6.5) under the block function `E` from the initial counter
block `T₁`: `Cⱼ = Pⱼ ⊕ E(Tⱼ)`, the last block truncated. Decryption is the same function. -/
def crypt (E : Bytes 16 → Bytes 16) (T₁ : Bytes 16) (message : List UInt8) : List UInt8 :=
  xorStream message ((counterBlocks T₁ (blockCount message.length)).map E)

theorem length_xorStream (message : List UInt8) (outputs : List (Bytes 16)) :
    (xorStream message outputs).length ≤ message.length := by
  simp [xorStream]

theorem xorStream_xorStream (message : List UInt8) (outputs : List (Bytes 16))
    (h : message.length ≤ (outputs.flatMap Vector.toList).length) :
    xorStream (xorStream message outputs) outputs = message := by
  unfold xorStream
  generalize outputs.flatMap Vector.toList = pad at h ⊢
  induction message generalizing pad with
  | nil => simp
  | cons b message ih =>
    cases pad with
    | nil => simp at h
    | cons p pad =>
      simp only [List.zipWith_cons_cons, List.cons.injEq]
      exact ⟨by rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero],
        ih pad (by simpa using h)⟩

theorem length_xorStream_eq (message : List UInt8) (outputs : List (Bytes 16))
    (h : message.length ≤ (outputs.flatMap Vector.toList).length) :
    (xorStream message outputs).length = message.length := by
  simp only [xorStream, List.length_zipWith]
  exact Nat.min_eq_left h

theorem length_flatMap_toList (outputs : List (Bytes 16)) :
    (outputs.flatMap Vector.toList).length = 16 * outputs.length := by
  induction outputs with
  | nil => simp
  | cons b outputs ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; ring

theorem length_outputs (E : Bytes 16 → Bytes 16) (T₁ : Bytes 16) (length : ℕ) :
    length ≤ (((counterBlocks T₁ (blockCount length)).map E).flatMap Vector.toList).length := by
  rw [length_flatMap_toList, List.length_map, counterBlocks, List.length_iterate, blockCount]
  omega

/-- **Decryption inverts encryption.** -/
theorem crypt_crypt (E : Bytes 16 → Bytes 16) (T₁ : Bytes 16) (message : List UInt8) :
    crypt E T₁ (crypt E T₁ message) = message := by
  unfold crypt
  rw [length_xorStream_eq _ _ (length_outputs E T₁ _)]
  exact xorStream_xorStream _ _ (length_outputs E T₁ _)

/-- The initial counter block of a nonce: the nonce followed by a zero counter
(SP 800-38A, Appendix B.2). -/
def initialBlock (nonce : Bytes 12) : Bytes 16 := nonce ++ (0 : Bytes 4)

/-- The encryption of a byte string of length at most `ℓ`. -/
def xorStreamOf {ℓ : ℕ} (message : ByteString ℓ) (outputs : List (Bytes 16)) : ByteString ℓ :=
  ⟨xorStream message.val outputs, (length_xorStream _ _).trans message.property⟩

end CTR

noncomputable section

interface StreamCipher(ℓ : ℕ)
  crypt(nonce : Bytes 12, message : ByteString ℓ) → ByteString ℓ

-- CTR on the block function inside: query the block function at each counter block of the
-- nonce, and XOR the outputs into the message.
converter CTR(ℓ : ℕ) : StreamCipher ℓ
  inside cipher : Evaluation (Bytes 16) (Bytes 16)
  on crypt(nonce : Bytes 12, message : ByteString ℓ) → ByteString ℓ
    outputs ← ([] : List (Bytes 16))
    for T ∈ CTR.counterBlocks (CTR.initialBlock nonce) (CTR.blockCount message.val.length)
      output ← cipher.eval(T)
      outputs ← outputs ++ [output]
    return CTR.xorStreamOf message outputs

end

end Commons
