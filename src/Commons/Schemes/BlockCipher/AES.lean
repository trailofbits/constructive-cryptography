import Commons.Schemes.Bytes
import Commons.Definitions.Cipher
import Mathlib.Tactic.IntervalCases

/-!
# AES

The Advanced Encryption Standard (FIPS 197), one algorithm for the key lengths of AES-128, AES-192
and AES-256, on 128-bit blocks. A block is sixteen bytes, read column by column as the state
`s_{r,c}` at index `r + 4c` (§3.4), and a byte is an element of GF(2⁸) (§4). The cipher
(Algorithm 1) adds a round key, runs `Nr − 1` rounds of `SubBytes`, `ShiftRows`, `MixColumns` and
`AddRoundKey`, and a last round without `MixColumns`; the round keys are the words of
`KeyExpansion` (Algorithm 2). The inverse cipher (Algorithm 3) runs the inverse transformations in
the reverse order.

Each transformation is inverted by its inverse: `InvSubBytes` through the inverse S-box,
`InvShiftRows` by the opposite shifts, `AddRoundKey` by itself, and `InvMixColumns` because
multiplication in GF(2⁸) is linear, so a column is inverted when each of its bytes is. So the
inverse cipher inverts the cipher, and AES is a block cipher.

## Main definitions

* `KeyLength`, `Key k`, `Block`: AES-128, AES-192 and AES-256, their keys, and the blocks
* `keyExpansion`, `cipher`, `invCipher`: Algorithms 2, 1 and 3
* `blockCipher k`: AES with key length `k`, as a block cipher

## Main statements

* `invCipher_cipher`: the inverse cipher inverts the cipher
-/

namespace Commons.AES

/-- **The key lengths of AES** (FIPS 197, Table 3): AES-128, AES-192 and AES-256. -/
inductive KeyLength
  | aes128
  | aes192
  | aes256
  deriving DecidableEq, Repr

namespace KeyLength

/-- `Nk`: the key length in 32-bit words. -/
def Nk : KeyLength → ℕ
  | aes128 => 4
  | aes192 => 6
  | aes256 => 8

/-- `Nr`: the number of rounds. -/
def Nr : KeyLength → ℕ
  | aes128 => 10
  | aes192 => 12
  | aes256 => 14

end KeyLength

/-- A block: the input, output and state of AES, with `s_{r,c}` at index `r + 4c`. -/
abbrev Block := Bytes 16

/-- A word of four bytes. -/
abbrev Word := Bytes 4

/-- A key of `Nk` words. -/
abbrev Key (k : KeyLength) := Bytes (4 * k.Nk)

/-! ## Multiplication in GF(2⁸) -/

/-- `XTIMES` (FIPS 197, Equation (4.5)): multiplication by `x` modulo `x⁸ + x⁴ + x³ + x + 1`. -/
def xTimes (b : UInt8) : UInt8 :=
  if b >>> 7 = 0 then b <<< 1 else (b <<< 1) ^^^ 0x1b

/-- The product `b • c` in GF(2⁸) (FIPS 197, §4.2): the sum of `xTimes^[i] c` over the bits `i` of
`b`. -/
def mul (b c : UInt8) : UInt8 :=
  (List.range 8).foldr
    (fun i acc => if (b >>> i.toUInt8) &&& 1 = 0 then acc else xTimes^[i] c ^^^ acc) 0

theorem shiftRight_seven (b : UInt8) : b >>> 7 = 0 ∨ b >>> 7 = 1 := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 256, UInt8.ofFin i = b := ⟨b.toFin, rfl⟩
  revert i
  decide +kernel

/-- `xTimes` is linear. -/
theorem xTimes_xor (x y : UInt8) : xTimes (x ^^^ y) = xTimes x ^^^ xTimes y := by
  unfold xTimes
  rw [UInt8.shiftRight_xor, UInt8.shiftLeft_xor]
  rcases shiftRight_seven x with hx | hx <;> rcases shiftRight_seven y with hy | hy <;>
    simp only [hx, hy] <;> simp <;>
    first
    | ac_rfl
    | rw [UInt8.xor_assoc, UInt8.xor_comm (y <<< 1) 27, ← UInt8.xor_assoc 27 27, UInt8.xor_self,
        UInt8.zero_xor]

theorem iterate_xTimes_xor (n : ℕ) (x y : UInt8) :
    xTimes^[n] (x ^^^ y) = xTimes^[n] x ^^^ xTimes^[n] y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, xTimes_xor, ih]

/-- Multiplication in GF(2⁸) is linear. -/
theorem mul_xor (b x y : UInt8) : mul b (x ^^^ y) = mul b x ^^^ mul b y := by
  unfold mul
  induction List.range 8 with
  | nil => simp
  | cons i is ih =>
    simp only [List.foldr_cons]
    split_ifs
    · exact ih
    · rw [ih, iterate_xTimes_xor]
      ac_rfl

/-! ## The S-box -/

/-- `SBOX` (FIPS 197, Table 4), indexed by the high and the low nibble. -/
def sboxTable : Vector (Vector UInt8 16) 16 := #v[
  #v[0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76],
  #v[0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0],
  #v[0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15],
  #v[0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75],
  #v[0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84],
  #v[0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf],
  #v[0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8],
  #v[0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2],
  #v[0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73],
  #v[0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb],
  #v[0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79],
  #v[0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08],
  #v[0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a],
  #v[0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e],
  #v[0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf],
  #v[0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16]]

/-- `SBOX(b)`. -/
def sbox (b : UInt8) : UInt8 :=
  (sboxTable[b.toNat / 16]'(by have := b.toNat_lt; omega))[b.toNat % 16]'(by omega)

/-- `INVSBOX` (FIPS 197, Table 6). -/
def invSboxTable : Vector (Vector UInt8 16) 16 := #v[
  #v[0x52,0x09,0x6a,0xd5,0x30,0x36,0xa5,0x38,0xbf,0x40,0xa3,0x9e,0x81,0xf3,0xd7,0xfb],
  #v[0x7c,0xe3,0x39,0x82,0x9b,0x2f,0xff,0x87,0x34,0x8e,0x43,0x44,0xc4,0xde,0xe9,0xcb],
  #v[0x54,0x7b,0x94,0x32,0xa6,0xc2,0x23,0x3d,0xee,0x4c,0x95,0x0b,0x42,0xfa,0xc3,0x4e],
  #v[0x08,0x2e,0xa1,0x66,0x28,0xd9,0x24,0xb2,0x76,0x5b,0xa2,0x49,0x6d,0x8b,0xd1,0x25],
  #v[0x72,0xf8,0xf6,0x64,0x86,0x68,0x98,0x16,0xd4,0xa4,0x5c,0xcc,0x5d,0x65,0xb6,0x92],
  #v[0x6c,0x70,0x48,0x50,0xfd,0xed,0xb9,0xda,0x5e,0x15,0x46,0x57,0xa7,0x8d,0x9d,0x84],
  #v[0x90,0xd8,0xab,0x00,0x8c,0xbc,0xd3,0x0a,0xf7,0xe4,0x58,0x05,0xb8,0xb3,0x45,0x06],
  #v[0xd0,0x2c,0x1e,0x8f,0xca,0x3f,0x0f,0x02,0xc1,0xaf,0xbd,0x03,0x01,0x13,0x8a,0x6b],
  #v[0x3a,0x91,0x11,0x41,0x4f,0x67,0xdc,0xea,0x97,0xf2,0xcf,0xce,0xf0,0xb4,0xe6,0x73],
  #v[0x96,0xac,0x74,0x22,0xe7,0xad,0x35,0x85,0xe2,0xf9,0x37,0xe8,0x1c,0x75,0xdf,0x6e],
  #v[0x47,0xf1,0x1a,0x71,0x1d,0x29,0xc5,0x89,0x6f,0xb7,0x62,0x0e,0xaa,0x18,0xbe,0x1b],
  #v[0xfc,0x56,0x3e,0x4b,0xc6,0xd2,0x79,0x20,0x9a,0xdb,0xc0,0xfe,0x78,0xcd,0x5a,0xf4],
  #v[0x1f,0xdd,0xa8,0x33,0x88,0x07,0xc7,0x31,0xb1,0x12,0x10,0x59,0x27,0x80,0xec,0x5f],
  #v[0x60,0x51,0x7f,0xa9,0x19,0xb5,0x4a,0x0d,0x2d,0xe5,0x7a,0x9f,0x93,0xc9,0x9c,0xef],
  #v[0xa0,0xe0,0x3b,0x4d,0xae,0x2a,0xf5,0xb0,0xc8,0xeb,0xbb,0x3c,0x83,0x53,0x99,0x61],
  #v[0x17,0x2b,0x04,0x7e,0xba,0x77,0xd6,0x26,0xe1,0x69,0x14,0x63,0x55,0x21,0x0c,0x7d]]

/-- `INVSBOX(b)`. -/
def invSbox (b : UInt8) : UInt8 :=
  (invSboxTable[b.toNat / 16]'(by have := b.toNat_lt; omega))[b.toNat % 16]'(by omega)

/-- The inverse S-box inverts the S-box. -/
theorem invSbox_sbox (b : UInt8) : invSbox (sbox b) = b := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 256, UInt8.ofFin i = b := ⟨b.toFin, rfl⟩
  revert i
  decide +kernel

/-! ## The round transformations -/

/-- `SUBBYTES` (§5.1.1): the S-box on each byte. -/
def subBytes (s : Block) : Block := s.map sbox

/-- `INVSUBBYTES` (§5.3.2): the inverse S-box on each byte. -/
def invSubBytes (s : Block) : Block := s.map invSbox

/-- `SHIFTROWS` (§5.1.2): row `r` shifts left by `r`, `s'_{r,c} = s_{r,(c+r) mod 4}`. -/
def shiftRows (s : Block) : Block :=
  Vector.ofFn fun i => s[i.val % 4 + 4 * ((i.val / 4 + i.val % 4) % 4)]'(by omega)

/-- `INVSHIFTROWS` (§5.3.1): row `r` shifts right by `r`, `s'_{r,c} = s_{r,(c−r) mod 4}`. -/
def invShiftRows (s : Block) : Block :=
  Vector.ofFn fun i => s[i.val % 4 + 4 * ((i.val / 4 + 4 - i.val % 4) % 4)]'(by omega)

/-- The column `c` of the state, `[s_{0,c}, s_{1,c}, s_{2,c}, s_{3,c}]`. -/
def column (s : Block) (c : Fin 4) : Word :=
  Vector.ofFn fun r => s[r.val + 4 * c.val]'(by omega)

/-- The state of four columns. -/
def ofColumns (columns : Vector Word 4) : Block :=
  Vector.ofFn fun i => (columns[i.val / 4]'(by omega))[i.val % 4]'(by omega)

/-- The column transformation of `MIXCOLUMNS` (§5.1.3, Equation (5.14)). -/
def mixColumn (a : Word) : Word :=
  #v[mul 2 a[0] ^^^ mul 3 a[1] ^^^ a[2] ^^^ a[3],
    a[0] ^^^ mul 2 a[1] ^^^ mul 3 a[2] ^^^ a[3],
    a[0] ^^^ a[1] ^^^ mul 2 a[2] ^^^ mul 3 a[3],
    mul 3 a[0] ^^^ a[1] ^^^ a[2] ^^^ mul 2 a[3]]

/-- The column transformation of `INVMIXCOLUMNS` (§5.3.3, Equation (5.21)). -/
def invMixColumn (a : Word) : Word :=
  #v[mul 0x0e a[0] ^^^ mul 0x0b a[1] ^^^ mul 0x0d a[2] ^^^ mul 0x09 a[3],
    mul 0x09 a[0] ^^^ mul 0x0e a[1] ^^^ mul 0x0b a[2] ^^^ mul 0x0d a[3],
    mul 0x0d a[0] ^^^ mul 0x09 a[1] ^^^ mul 0x0e a[2] ^^^ mul 0x0b a[3],
    mul 0x0b a[0] ^^^ mul 0x0d a[1] ^^^ mul 0x09 a[2] ^^^ mul 0x0e a[3]]

/-- `MIXCOLUMNS` (§5.1.3): the column transformation on each column. -/
def mixColumns (s : Block) : Block :=
  ofColumns (Vector.ofFn fun c => mixColumn (column s c))

/-- `INVMIXCOLUMNS` (§5.3.3): the inverse column transformation on each column. -/
def invMixColumns (s : Block) : Block :=
  ofColumns (Vector.ofFn fun c => invMixColumn (column s c))

/-! ## Key expansion -/

/-- `SUBWORD` (§5.2): the S-box on each byte of a word. -/
def subWord (w : Word) : Word := w.map sbox

/-- `ROTWORD` (§5.2): the cyclic rotation `[a₀, a₁, a₂, a₃] ↦ [a₁, a₂, a₃, a₀]`. -/
def rotWord (w : Word) : Word := #v[w[1], w[2], w[3], w[0]]

/-- `Rcon[j] = [x^{j−1}, {00}, {00}, {00}]` (§5.2, Table 5). -/
def rcon (j : ℕ) : Word := #v[xTimes^[j - 1] 1, 0, 0, 0]

/-- `KEYEXPANSION` (§5.2, Algorithm 2): the `4 (Nr + 1)` words of the round keys, the key followed
by the words `w[i] = w[i − Nk] ⊕ temp`. -/
def keyExpansion (k : KeyLength) (key : Key k) : Array Word :=
  let initial : Array Word := ((List.finRange k.Nk).map fun i =>
    Vector.ofFn fun j : Fin 4 => key[4 * i.val + j.val]'(by omega)).toArray
  (List.range' k.Nk (4 * k.Nr + 4 - k.Nk)).foldl (fun w i =>
    let temp := w.getD (i - 1) 0
    let temp :=
      if i % k.Nk = 0 then subWord (rotWord temp) ^^^ rcon (i / k.Nk)
      else if 6 < k.Nk ∧ i % k.Nk = 4 then subWord temp
      else temp
    w.push (w.getD (i - k.Nk) 0 ^^^ temp)) initial

/-- `ADDROUNDKEY` (§5.1.4): the words `w[4 round], …, w[4 round + 3]` added to the columns. -/
def addRoundKey (s : Block) (w : Array Word) (round : ℕ) : Block :=
  s ^^^ Vector.ofFn fun i =>
    (w.getD (4 * round + i.val / 4) 0)[i.val % 4]'(by omega)

/-! ## The cipher and the inverse cipher -/

/-- `CIPHER` (§5.1, Algorithm 1). -/
def cipher (k : KeyLength) (key : Key k) (input : Block) : Block :=
  let w := keyExpansion k key
  let state := addRoundKey input w 0
  let state := (List.range' 1 (k.Nr - 1)).foldl (fun state round =>
    addRoundKey (mixColumns (shiftRows (subBytes state))) w round) state
  addRoundKey (shiftRows (subBytes state)) w k.Nr

/-- `INVCIPHER` (§5.3, Algorithm 3). -/
def invCipher (k : KeyLength) (key : Key k) (input : Block) : Block :=
  let w := keyExpansion k key
  let state := addRoundKey input w k.Nr
  let state := (List.range' 1 (k.Nr - 1)).reverse.foldl (fun state round =>
    invMixColumns (addRoundKey (invSubBytes (invShiftRows state)) w round)) state
  addRoundKey (invSubBytes (invShiftRows state)) w 0

/-! ## The inverse cipher inverts the cipher -/

theorem addRoundKey_addRoundKey (s : Block) (w : Array Word) (round : ℕ) :
    addRoundKey (addRoundKey s w round) w round = s :=
  xor_cancel_right _ _

theorem invSubBytes_subBytes (s : Block) : invSubBytes (subBytes s) = s :=
  Vector.ext fun i hi => by simp [invSubBytes, subBytes, invSbox_sbox]

theorem invShiftRows_shiftRows (s : Block) : invShiftRows (shiftRows s) = s :=
  Vector.ext fun i hi => by
    interval_cases i <;> simp [invShiftRows, shiftRows]

/-- The byte with the single bit `j`. -/
def bit (j : ℕ) : UInt8 := 1 <<< j.toUInt8

/-- A byte is the sum of its bits. -/
theorem eq_xor_bits (x : UInt8) :
    x = (List.range 8).foldr (fun j acc => (x &&& bit j) ^^^ acc) 0 := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 256, UInt8.ofFin i = x := ⟨x.toFin, rfl⟩
  revert i
  decide +kernel

theorem and_bit (x : UInt8) (j : ℕ) (hj : j < 8) :
    x &&& bit j = 0 ∨ x &&& bit j = bit j := by
  obtain ⟨i, rfl⟩ : ∃ i : Fin 256, UInt8.ofFin i = x := ⟨x.toFin, rfl⟩
  obtain ⟨j, rfl⟩ : ∃ j' : Fin 8, j'.val = j := ⟨⟨j, hj⟩, rfl⟩
  revert i j
  decide +kernel

/-- **Linear maps of bytes are determined by the bits**: two maps from bytes to words that
preserve `^^^` and agree on each bit agree. -/
theorem eq_of_xor_of_bits {f g : UInt8 → Word} (hf : ∀ x y, f (x ^^^ y) = f x ^^^ f y)
    (hg : ∀ x y, g (x ^^^ y) = g x ^^^ g y)
    (hbits : ∀ j < 8, f (bit j) = g (bit j)) (x : UInt8) : f x = g x := by
  have zero : ∀ {h : UInt8 → Word}, (∀ x y, h (x ^^^ y) = h x ^^^ h y) → h 0 = 0 := by
    intro h hh
    have := hh 0 0
    rw [UInt8.xor_self] at this
    rw [this, LawfulXor.xor_self]
  have sum : ∀ {h : UInt8 → Word}, (∀ x y, h (x ^^^ y) = h x ^^^ h y) → ∀ l : List ℕ,
      h (l.foldr (fun j acc => (x &&& bit j) ^^^ acc) 0) =
        l.foldr (fun j acc => h (x &&& bit j) ^^^ acc) 0 := by
    intro h hh l
    induction l with
    | nil => exact zero hh
    | cons j l ih => simp only [List.foldr_cons, hh, ih]
  rw [eq_xor_bits x, sum hf, sum hg]
  refine List.foldr_ext _ _ _ fun j hj acc => ?_
  have hj := List.mem_range.mp hj
  rcases and_bit x j hj with h | h <;> rw [h]
  · rw [zero hf, zero hg]
  · rw [hbits j hj]

/-- The single-byte column `x` at row `r`. -/
def singleton (r : Fin 4) (x : UInt8) : Word := Vector.ofFn fun r' => if r' = r then x else 0

theorem singleton_xor (r : Fin 4) (x y : UInt8) :
    singleton r (x ^^^ y) = singleton r x ^^^ singleton r y :=
  Vector.ext fun i hi => by
    simp only [singleton, Vector.getElem_ofFn, Bytes.getElem_xor]
    split_ifs <;> simp

theorem mixColumn_xor (a b : Word) : mixColumn (a ^^^ b) = mixColumn a ^^^ mixColumn b :=
  Vector.ext fun i hi => by
    interval_cases i <;> simp [mixColumn, mul_xor] <;> ac_rfl

theorem invMixColumn_xor (a b : Word) :
    invMixColumn (a ^^^ b) = invMixColumn a ^^^ invMixColumn b :=
  Vector.ext fun i hi => by
    interval_cases i <;> simp [invMixColumn, mul_xor] <;> ac_rfl

theorem word_eq_singletons (a : Word) :
    a = singleton 0 a[0] ^^^ singleton 1 a[1] ^^^ singleton 2 a[2] ^^^ singleton 3 a[3] :=
  Vector.ext fun i hi => by
    interval_cases i <;> simp [singleton]

theorem invMixColumn_mixColumn_bits :
    ∀ r : Fin 4, ∀ j : Fin 8, invMixColumn (mixColumn (singleton r (bit j.val))) =
      singleton r (bit j.val) := by
  decide +kernel

/-- **`INVMIXCOLUMNS` inverts `MIXCOLUMNS` on a column**: both are linear, so it suffices that each
bit of each byte of a column is inverted. -/
theorem invMixColumn_mixColumn (a : Word) : invMixColumn (mixColumn a) = a := by
  have hbyte : ∀ r x, invMixColumn (mixColumn (singleton r x)) = singleton r x := fun r =>
    eq_of_xor_of_bits (f := fun x => invMixColumn (mixColumn (singleton r x)))
      (fun x y => by simp only [singleton_xor, mixColumn_xor, invMixColumn_xor])
      (singleton_xor r) (fun j hj => invMixColumn_mixColumn_bits r ⟨j, hj⟩)
  rw [word_eq_singletons a]
  simp only [mixColumn_xor, invMixColumn_xor, hbyte]

theorem column_ofColumns (columns : Vector Word 4) (c : Fin 4) :
    column (ofColumns columns) c = columns[c] :=
  Vector.ext fun r hr => by
    fin_cases c <;> interval_cases r <;> simp [column, ofColumns]

theorem ofColumns_column (s : Block) : ofColumns (Vector.ofFn fun c => column s c) = s :=
  Vector.ext fun i hi => by
    interval_cases i <;> simp [ofColumns, column]

theorem invMixColumns_mixColumns (s : Block) : invMixColumns (mixColumns s) = s := by
  simp only [invMixColumns, mixColumns, column_ofColumns, Fin.getElem_fin, Vector.getElem_ofFn,
    invMixColumn_mixColumn, Fin.eta, ofColumns_column]

/-- **The inverse rounds invert the rounds**: after `SubBytes` and `ShiftRows`, the inverse rounds
in the reverse order undo the rounds `rs`, the inverse of round `r` undoing `MixColumns` and
`AddRoundKey` of round `r` and `SubBytes` and `ShiftRows` of the round before. -/
theorem invRounds_rounds (w : Array Word) (rs : List ℕ) (s : Block) :
    rs.reverse.foldl (fun state round =>
        invMixColumns (addRoundKey (invSubBytes (invShiftRows state)) w round))
      (shiftRows (subBytes (rs.foldl (fun state round =>
        addRoundKey (mixColumns (shiftRows (subBytes state))) w round) s))) =
      shiftRows (subBytes s) := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons (l := rs), ih]
    simp only [List.foldl_cons, List.foldl_nil, invShiftRows_shiftRows, invSubBytes_subBytes,
      addRoundKey_addRoundKey, invMixColumns_mixColumns]

/-- **The inverse cipher inverts the cipher.** -/
theorem invCipher_cipher (k : KeyLength) (key : Key k) (input : Block) :
    invCipher k key (cipher k key input) = input := by
  simp only [cipher, invCipher, addRoundKey_addRoundKey, invRounds_rounds, invShiftRows_shiftRows,
    invSubBytes_subBytes]

/-- **AES** with the key length `k`, as a block cipher. -/
def blockCipher (k : KeyLength) : BlockCipher (Key k) Block where
  encrypt := cipher k
  decrypt := invCipher k
  decrypt_encrypt := invCipher_cipher k

end Commons.AES

