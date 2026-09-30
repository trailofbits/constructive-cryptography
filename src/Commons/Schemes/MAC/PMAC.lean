import Commons.Schemes.Bytes
import Commons.Definitions.Cipher
import Commons.Definitions.MAC

/-!
# PMAC

PMAC (Black–Rogaway, Figure 1 and §3, printed pp. 4–5) over a block function `E` on 128-bit
blocks, with full 128-bit tags. With `L = E(0¹²⁸)`, the message is partitioned into blocks
`M[1] ⋯ M[m]`, the empty message having one empty block; each block but the last is masked by the
offset `γᵢ · L` and enciphered, and the sum of these with the last block, masked by `L · x⁻¹` when
full and padded with `10*` otherwise, is enciphered to the tag. The offsets follow the Gray code,
`γᵢ · L = γᵢ₋₁ · L ⊕ L · x^{ntz(i)}`, with multiplication by `x` and `x⁻¹` in GF(2¹²⁸) modulo
`x¹²⁸ + x⁷ + x² + x + 1`. A message longer than `16 · 2¹²⁸` bytes, outside the message space, is
tagged with zero.

As a MAC it tags with PMAC under the key of a block cipher, and as a converter it tags and
verifies on any block function answering at the interface `Evaluation`.

## Main definitions

* `PMAC.pmac E M`: the tag of the bytes `M`
* `PMAC.mac E encode`: PMAC under the key of the block cipher `E`, on messages encoded as bytes
* `PMAC encode`: PMAC as a converter from `Evaluation (Bytes 16) (Bytes 16)` to
  `Tagging M (Bytes 16)`

## Main statements

* `PMAC.mac_correct`: every tag verifies
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra.DSL

namespace PMAC

/-- A block as a 128-bit word, big-endian. -/
def toWord (b : Bytes 16) : BitVec 128 :=
  BitVec.ofNat 128 (b.toList.foldl (fun n x => 256 * n + x.toNat) 0)

/-- A 128-bit word as a block, big-endian. -/
def ofWord (w : BitVec 128) : Bytes 16 :=
  Vector.ofFn fun i => (w.toNat / 2 ^ (8 * (15 - i.val))).toUInt8

/-- Multiplication by `x` in GF(2¹²⁸). -/
def double (b : Bytes 16) : Bytes 16 :=
  let w := toWord b
  ofWord ((w <<< 1) ^^^ (if w.msb then 0x87 else 0))

/-- Multiplication by `x⁻¹` in GF(2¹²⁸). -/
def halve (b : Bytes 16) : Bytes 16 :=
  let w := toWord b
  ofWord ((w >>> 1) ^^^ (if w.getLsbD 0 then 0x80000000000000000000000000000043 else 0))

/-- The number of trailing zero bits of `n`, and `0` for `n = 0`. -/
def ntz : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + ntz ((n + 1) / 2) else 0
termination_by n => n

/-- The step `L · x^{ntz(i)}` from the offset `γᵢ₋₁ · L` to `γᵢ · L`. -/
def offsetStep (L : Bytes 16) (i : ℕ) : Bytes 16 := double^[ntz i] L

/-- The number `m − 1` of blocks before the last. -/
def prefixCount (bytes : List UInt8) : ℕ := (bytes.length - 1) / 16

/-- The bytes as a block, padded with zeros. -/
def blockOf (bytes : List UInt8) : Bytes 16 := Vector.ofFn fun i => bytes.getD i.val 0

/-- Block `M[i + 1]`. -/
def block (bytes : List UInt8) (i : ℕ) : Bytes 16 := blockOf ((bytes.drop (16 * i)).take 16)

/-- The last block `M[m]`, masked by `L · x⁻¹` when full and padded with `10*` otherwise. -/
def lastBlock (L : Bytes 16) (bytes : List UInt8) : Bytes 16 :=
  let last := bytes.drop (16 * prefixCount bytes)
  if last.length = 16 then blockOf last ^^^ halve L else blockOf (last ++ [0x80])

/-- **PMAC** (Black–Rogaway, Figure 1) under the block function `E`. -/
def pmac (E : Bytes 16 → Bytes 16) (bytes : List UInt8) : Bytes 16 :=
  if bytes.length > 16 * 2 ^ 128 then 0 else
    let L := E 0
    let (_, checksum) := (List.range (prefixCount bytes)).foldl (fun (offset, checksum) i =>
      let offset := offset ^^^ offsetStep L (i + 1)
      (offset, checksum ^^^ E (block bytes i ^^^ offset))) ((0 : Bytes 16), (0 : Bytes 16))
    E (checksum ^^^ lastBlock L bytes)

variable {K M : Type} [Fintype K] [Nonempty K]

/-- **PMAC as a MAC** under the key of the block cipher `E`, on messages encoded as bytes: a
uniform key, the PMAC tag of the encoding under `E_k`, and verification by recomputing it. -/
noncomputable def mac (E : BlockCipher K (Bytes 16)) (encode : M → List UInt8) :
    MAC K M (Bytes 16) where
  gen := ⟨Distribution.uniform K, Distribution.uniform_isProbDist⟩
  tag k m := Distribution.ProbDist.single (pmac (E.encrypt k) (encode m))
  verify k m t := pmac (E.encrypt k) (encode m) == t

/-- **Correctness**: every tag verifies. -/
theorem mac_correct (E : BlockCipher K (Bytes 16)) (encode : M → List UInt8) :
    (mac E encode).Correct := by
  intro k _ m t ht
  simp only [mac, Distribution.ProbDist.single, Finsupp.support_single _ one_ne_zero,
    Finset.mem_singleton] at ht
  simp [mac, ht]

end PMAC

noncomputable section

variable {M : Type} [Fintype M]

-- PMAC on the block function inside: tag by the algorithm of `PMAC.pmac`, querying the block
-- function for `L`, each masked block and the checksum; verify by recomputing the tag.
converter PMAC(encode : M → List UInt8) : Tagging M (Bytes 16)
  inside cipher : Evaluation (Bytes 16) (Bytes 16)
  on tag(message : M) → Bytes 16
    bytes ← encode message
    if bytes.length > 16 * 2 ^ 128
      return (0 : Bytes 16)
    else
      L ← cipher.eval(0)
      offset ← (0 : Bytes 16)
      checksum ← (0 : Bytes 16)
      for i ∈ List.range (PMAC.prefixCount bytes)
        offset ← offset ^^^ PMAC.offsetStep L (i + 1)
        image ← cipher.eval(PMAC.block bytes i ^^^ offset)
        checksum ← checksum ^^^ image
      tag ← cipher.eval(checksum ^^^ PMAC.lastBlock L bytes)
      return tag
  on verify(message : M, tag : Bytes 16) → Bool
    bytes ← encode message
    if bytes.length > 16 * 2 ^ 128
      return decide (tag = 0)
    else
      L ← cipher.eval(0)
      offset ← (0 : Bytes 16)
      checksum ← (0 : Bytes 16)
      for i ∈ List.range (PMAC.prefixCount bytes)
        offset ← offset ^^^ PMAC.offsetStep L (i + 1)
        image ← cipher.eval(PMAC.block bytes i ^^^ offset)
        checksum ← checksum ^^^ image
      expected ← cipher.eval(checksum ^^^ PMAC.lastBlock L bytes)
      return decide (tag = expected)

end

end Commons
