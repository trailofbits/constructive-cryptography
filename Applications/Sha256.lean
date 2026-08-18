/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/

/-!
# SHA-256 (FIPS 180-4), executable specification

Vendored from `trailofbits/galvanize-openvm-lean`
(`galvanize-lean/lean/OpenVMSha256/SHA256Spec.lean`, written for Lean
v4.28.0), namespace adapted.  Core-only: no Mathlib import, so this file
elaborates in milliseconds and nothing in the proof stack depends on it.

## Computability discipline (see `AGENTS.md`)

This file is the *instantiation* of the hash parameters (`H1`, `H2` in
`FrostProtocol`) at the carrier; the proof layer never unfolds it — there
the hash is a parameter and randomness enters via the random-oracle
*resource*.  Everything here is engineered so that concrete evaluation
never needs an elaborator-side unfold:

* all recursion is **structural** (`Nat.fold`, explicit `Nat`-recursion) —
  kernel-reducible, so `decide +kernel` works and `simp` cannot get stuck
  on `WellFounded.fix`;
* arithmetic is `UInt32`/`UInt64`/`ByteArray` — kernel-side these reduce
  through GMP-backed `Nat` literals;
* the readable definition (`sha256`) is the *semantics*; the flat-state
  `sha256Fast` is proved equal and registered `@[csimp]`, so `#eval` /
  `native_decide` run the fast version while the kernel only ever sees
  the readable one;
* known-answer tests live in the separate, non-default `Sha256Tests`
  target — the `Lean.ofReduceBool` axiom from `native_decide` never
  enters the library.
-/

namespace AbstractCryptography
namespace Sha256

/-- FIPS 180-4 §4.2.2 (SHA-224 and SHA-256 Constants): "SHA-224 and
SHA-256 use the same sequence of sixty-four constant 32-bit words,
`K₀^{256}, K₁^{256}, …, K₆₃^{256}`.  These words represent the first
thirty-two bits of the fractional parts of the cube roots of the first
sixty-four prime numbers.  In hex, these constant words are (from left to
right)". -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

/-- FIPS 180-4 §5.3.3 (SHA-256): "For SHA-256, the initial hash value,
`H⁽⁰⁾`, shall consist of the following eight 32-bit words, in hex: …
These words were obtained by taking the first thirty-two bits of the
fractional parts of the square roots of the first eight prime
numbers." -/
def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

/-! ## Bitwise helpers

FIPS 180-4 §4.1.2 (SHA-224 and SHA-256 Functions): "SHA-224 and SHA-256
both use six logical functions, where each function operates on 32-bit
words, which are represented as `x`, `y`, and `z`.  The result of each
function is a new 32-bit word."

  `Ch(x, y, z)   = (x ∧ y) ⊕ (¬x ∧ z)`                              (4.2)
  `Maj(x, y, z)  = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`                     (4.3)
  `Σ₀^{256}(x)   = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`                (4.4)
  `Σ₁^{256}(x)   = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`                (4.5)
  `σ₀^{256}(x)   = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`                  (4.6)
  `σ₁^{256}(x)   = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`                (4.7)
-/

def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> (n % 32)) ||| (x <<< ((32 - n % 32) % 32))

def ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (~~~x &&& z)

def maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def bigSig0 (x : UInt32) : UInt32 :=
  rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

def bigSig1 (x : UInt32) : UInt32 :=
  rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

def smallSig0 (x : UInt32) : UInt32 :=
  rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)

def smallSig1 (x : UInt32) : UInt32 :=
  rotr32 x 17 ^^^ rotr32 x 19 ^^^ (x >>> 10)

/-- Total array access (out-of-range reads 0) — keeps the executable
terms free of bound-proof dependencies. -/
private def getU32 (a : Array UInt32) (i : Nat) : UInt32 :=
  if h : i < a.size then a[i] else 0

/-- FIPS 180-4 §6.2.2, step 1: "Prepare the message schedule, `{Wₜ}`:

  `Wₜ = Mₜ⁽ⁱ⁾`                                                  `0 ≤ t ≤ 15`
  `Wₜ = σ₁^{256}(Wₜ₋₂) + Wₜ₋₇ + σ₀^{256}(Wₜ₋₁₅) + Wₜ₋₁₆`       `16 ≤ t ≤ 63`"

The `0 ≤ t ≤ 15` case is the incoming `block`; the fold appends the
remaining 48 words.  ("Addition (+) is performed modulo `2³²`" — §6.2.2;
that is `UInt32` addition here.) -/
def msgSchedule (block : Array UInt32) : Array UInt32 :=
  Nat.fold (init := block) 48 fun i _ w =>
    let idx := i + 16
    w.push (smallSig1 (getU32 w (idx - 2)) + getU32 w (idx - 7) +
            smallSig0 (getU32 w (idx - 15)) + getU32 w (idx - 16))

/-- FIPS 180-4 §6.2.2, step 3: "For `t=0` to `63`:

  `T₁ = h + Σ₁^{256}(e) + Ch(e, f, g) + Kₜ^{256} + Wₜ`
  `T₂ = Σ₀^{256}(a) + Maj(a, b, c)`
  `h = g;  g = f;  f = e;  e = d + T₁;`
  `d = c;  c = b;  b = a;  a = T₁ + T₂`"

Run for `n` rounds by structural recursion.  State
`(a, b, c, d, e, f, g, h)` is a `Fin 8 → UInt32` function. -/
def compressLoop (n : Nat) (s : Fin 8 → UInt32) (w : Array UInt32) : Fin 8 → UInt32 :=
  match n with
  | 0 => s
  | k + 1 =>
    let prev := compressLoop k s w
    let a := prev ⟨0, by omega⟩; let b := prev ⟨1, by omega⟩
    let c := prev ⟨2, by omega⟩; let d := prev ⟨3, by omega⟩
    let e := prev ⟨4, by omega⟩; let f := prev ⟨5, by omega⟩
    let g := prev ⟨6, by omega⟩; let h := prev ⟨7, by omega⟩
    let t1 := h + bigSig1 e + ch e f g + getU32 K k + getU32 w k
    let t2 := bigSig0 a + maj a b c
    fun i => match i with
    | ⟨0, _⟩ => t1 + t2
    | ⟨1, _⟩ => a
    | ⟨2, _⟩ => b
    | ⟨3, _⟩ => c
    | ⟨4, _⟩ => d + t1
    | ⟨5, _⟩ => e
    | ⟨6, _⟩ => f
    | ⟨7, _⟩ => g

/-- FIPS 180-4 §6.2.2: steps 2–4 — initialize the eight working
variables with the `(i-1)`st hash value, run the 64 rounds, then step 4,
"Compute the `i`th intermediate hash value `H⁽ⁱ⁾`":

  `H₀⁽ⁱ⁾ = a + H₀⁽ⁱ⁻¹⁾ ,  …  , H₇⁽ⁱ⁾ = h + H₇⁽ⁱ⁻¹⁾`

— the feed-forward.  "The SHA-256 hash computation uses functions and
constants previously defined in Sec. 4.1.2 and Sec. 4.2.2,
respectively.  Addition (+) is performed modulo `2³²`." -/
def compress (state : Array UInt32) (w : Array UInt32) : Array UInt32 :=
  let s0 : Fin 8 → UInt32 := fun i => getU32 state i
  let final := compressLoop 64 s0 w
  #[final ⟨0, by omega⟩ + getU32 state 0, final ⟨1, by omega⟩ + getU32 state 1,
    final ⟨2, by omega⟩ + getU32 state 2, final ⟨3, by omega⟩ + getU32 state 3,
    final ⟨4, by omega⟩ + getU32 state 4, final ⟨5, by omega⟩ + getU32 state 5,
    final ⟨6, by omega⟩ + getU32 state 6, final ⟨7, by omega⟩ + getU32 state 7]

private theorem getU32_ofFn (f : Fin 8 → UInt32) (i : Nat) (hi : i < 8) :
    getU32 (Array.ofFn f) i = f ⟨i, hi⟩ := by
  simp [getU32, Array.size_ofFn, hi, Array.getElem_ofFn]

theorem compress_size (state w : Array UInt32) : (compress state w).size = 8 := by
  simp [compress]

/-- Rewriting lemma: `getU32` on `Array.ofFn` gives `f`. -/
private theorem getU32_ofFn_fun (f : Fin 8 → UInt32) :
    (fun (i : Fin 8) => getU32 (Array.ofFn f) i.val) = f := by
  ext j; exact getU32_ofFn f j.val j.isLt

/-- Each element of `compress` is the `compressLoop` result plus the
initial state element — the Davies–Meyer structure, without leaking the
private `getU32`. -/
theorem compress_getElem_ofFn (f : Fin 8 → UInt32) (w : Array UInt32) (i : Fin 8) :
    (compress (Array.ofFn f) w)[i.val]'(by simp [compress_size]) =
      compressLoop 64 f w i + f i := by
  have hgu := getU32_ofFn_fun f
  unfold compress
  simp only [hgu,
    getU32_ofFn f 0 (by omega), getU32_ofFn f 1 (by omega),
    getU32_ofFn f 2 (by omega), getU32_ofFn f 3 (by omega),
    getU32_ofFn f 4 (by omega), getU32_ofFn f 5 (by omega),
    getU32_ofFn f 6 (by omega), getU32_ofFn f 7 (by omega)]
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl
  | ⟨6, _⟩ => rfl
  | ⟨7, _⟩ => rfl

/-- `compress_getElem_ofFn` generalized to an arbitrary size-8 state
array (not requiring `Array.ofFn` form). -/
theorem compress_getElem_gen (state : Array UInt32)
    (hs : state.size = 8) (w : Array UInt32) (i : Fin 8) :
    (compress state w)[i.val]'(by simp [compress_size]) =
      let f := fun j : Fin 8 => state[j.val]'(Nat.lt_of_lt_of_eq j.isLt hs.symm)
      compressLoop 64 f w i + f i := by
  have heq : state = Array.ofFn (fun j : Fin 8 => state[j.val]'(Nat.lt_of_lt_of_eq j.isLt hs.symm)) :=
    Array.ext (by simp [hs]) (fun j _ _ => by simp [Array.getElem_ofFn])
  have hcomp_eq : compress state w =
      compress (Array.ofFn (fun j : Fin 8 => state[j.val]'(Nat.lt_of_lt_of_eq j.isLt hs.symm))) w :=
    congrArg (compress · w) heq
  simp only [hcomp_eq]
  exact compress_getElem_ofFn _ w i

/-! ## Byte-level interface (padding, parsing, digest) -/

/-- Read a big-endian `UInt32` from 4 bytes. -/
def readBE32 (bs : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (if h : off < bs.size then bs[off] else 0).toUInt32
  let b1 := (if h : off + 1 < bs.size then bs[off + 1] else 0).toUInt32
  let b2 := (if h : off + 2 < bs.size then bs[off + 2] else 0).toUInt32
  let b3 := (if h : off + 3 < bs.size then bs[off + 3] else 0).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- Write a big-endian `UInt32` to bytes. -/
def writeBE32 (v : UInt32) : ByteArray :=
  ⟨#[(v >>> 24).toUInt8, (v >>> 16).toUInt8, (v >>> 8).toUInt8, v.toUInt8]⟩

/-- FIPS 180-4 §5.1.1 (SHA-1, SHA-224 and SHA-256): "Suppose that the
length of the message, `M`, is `ℓ` bits.  Append the bit '1' to the end
of the message, followed by `k` zero bits, where `k` is the smallest,
non-negative solution to the equation `ℓ + 1 + k ≡ 448 mod 512`.  Then
append the 64-bit block that is equal to the number `ℓ` expressed using a
binary representation.  For example, the (8-bit ASCII) message 'abc' has
length `8 × 3 = 24`, so the message is padded with a one bit, then
`448 − (24 + 1) = 423` zero bits, and then the message length, to become
the 512-bit padded message … The length of the padded message should now
be a multiple of 512 bits."

Byte-wise here (`ℓ` a multiple of 8), so the '1' bit is the `0x80`
byte. -/
def sha256Pad (msg : ByteArray) : ByteArray :=
  let len := msg.size
  let bitLen : UInt64 := len.toUInt64 * 8
  -- Number of zero-pad bytes: pad to 56 mod 64 after the 0x80 byte.
  -- NOT `(55 - len % 64) % 64` as in the upstream source: `Nat`
  -- subtraction truncates, so that collapses to 0 for
  -- `len % 64 ∈ [56, 63]` and the length bytes overflow into a block
  -- that `parseBlocks` never reads (caught by `decide +kernel` on the
  -- FIPS 448-bit vector; digest was wrong for those residues).
  let padZeros := (119 - len % 64) % 64
  let withBit := msg.push 0x80
  let withZeros := Nat.fold (init := withBit) padZeros fun _ _ acc => acc.push 0x00
  -- Append 64-bit big-endian bit length (8 bytes)
  let p := withZeros
  let p := p.push ((bitLen >>> 56).toUInt8)
  let p := p.push ((bitLen >>> 48).toUInt8)
  let p := p.push ((bitLen >>> 40).toUInt8)
  let p := p.push ((bitLen >>> 32).toUInt8)
  let p := p.push ((bitLen >>> 24).toUInt8)
  let p := p.push ((bitLen >>> 16).toUInt8)
  let p := p.push ((bitLen >>> 8).toUInt8)
  p.push bitLen.toUInt8

/-- FIPS 180-4 §5.2.1 (Parsing the Message — SHA-1, SHA-224 and
SHA-256): "the message and its padding are parsed into `N` 512-bit
blocks, `M⁽¹⁾, M⁽²⁾, …, M⁽ᴺ⁾`.  Since the 512 bits of the input block may
be expressed as sixteen 32-bit words, the first 32 bits of message block
`i` are denoted `M₀⁽ⁱ⁾`, the next 32 bits are `M₁⁽ⁱ⁾`, and so on up to
`M₁₅⁽ⁱ⁾`." -/
def parseBlocks (padded : ByteArray) : Array (Array UInt32) :=
  let nBlocks := padded.size / 64
  Nat.fold (init := #[]) nBlocks fun bi _ acc =>
    acc.push (Nat.fold (init := #[]) 16 fun wi _ block =>
      block.push (readBE32 padded (bi * 64 + wi * 4)))

/-- FIPS 180-4 §6.2.2: "After repeating steps one through four a total of
`N` times (i.e., after processing `M⁽ᴺ⁾`), the resulting 256-bit message
digest of the message, `M`, is

  `H₀⁽ᴺ⁾ ‖ H₁⁽ᴺ⁾ ‖ H₂⁽ᴺ⁾ ‖ H₃⁽ᴺ⁾ ‖ H₄⁽ᴺ⁾ ‖ H₅⁽ᴺ⁾ ‖ H₆⁽ᴺ⁾ ‖ H₇⁽ᴺ⁾`" -/
def sha256 (msg : ByteArray) : ByteArray :=
  let padded := sha256Pad msg
  let blocks := parseBlocks padded
  let finalHash := blocks.foldl (init := H0) fun state block =>
    let w := msgSchedule block
    compress state w
  finalHash.foldl (init := ByteArray.empty) fun acc word => acc ++ writeBE32 word

/-! ## Optimized SHA-256 for compiled evaluation

The compression loop uses a flat structure with 8 `UInt32` fields instead
of `Fin 8 → UInt32` closures.  This is not a constant-factor tweak: the
readable `compressLoop` returns a *function*, so compiled code re-enters
the recursion once per component read — `8^rounds`, divergent in
practice (the kernel survives only via whnf caching).  The equivalence
`sha256 = sha256Fast` is proved and registered `@[csimp]` — in exactly
that orientation: `@[csimp]` replaces the LHS's compiled implementation
with the RHS's, so the readable definition must be the LHS (the reversed
orientation silently pessimizes every compiled call, including
`sha256Fast`'s own, onto the exponential path).  The compiler (`#eval`,
`native_decide`) thus uses the fast version automatically while the
kernel only ever reduces the readable one. -/

structure State8 where
  s0 : UInt32
  s1 : UInt32
  s2 : UInt32
  s3 : UInt32
  s4 : UInt32
  s5 : UInt32
  s6 : UInt32
  s7 : UInt32

@[inline] def State8.get (st : State8) : Fin 8 → UInt32
  | ⟨0, _⟩ => st.s0 | ⟨1, _⟩ => st.s1 | ⟨2, _⟩ => st.s2 | ⟨3, _⟩ => st.s3
  | ⟨4, _⟩ => st.s4 | ⟨5, _⟩ => st.s5 | ⟨6, _⟩ => st.s6 | ⟨7, _⟩ => st.s7

@[inline] def State8.ofFn (f : Fin 8 → UInt32) : State8 :=
  { s0 := f ⟨0, by omega⟩, s1 := f ⟨1, by omega⟩,
    s2 := f ⟨2, by omega⟩, s3 := f ⟨3, by omega⟩,
    s4 := f ⟨4, by omega⟩, s5 := f ⟨5, by omega⟩,
    s6 := f ⟨6, by omega⟩, s7 := f ⟨7, by omega⟩ }

theorem State8.get_ofFn (f : Fin 8 → UInt32) (i : Fin 8) :
    (State8.ofFn f).get i = f i := by
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩
  | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ => rfl

/-- One round on the flat state. -/
@[inline] def roundStepS8 (st : State8) (ki wi : UInt32) : State8 :=
  let t1 := st.s7 + bigSig1 st.s4 + ch st.s4 st.s5 st.s6 + ki + wi
  let t2 := bigSig0 st.s0 + maj st.s0 st.s1 st.s2
  { s0 := t1 + t2, s1 := st.s0, s2 := st.s1, s3 := st.s2,
    s4 := st.s3 + t1, s5 := st.s4, s6 := st.s5, s7 := st.s6 }

/-- `compressLoop` on `State8` (same recursion structure). -/
def compressLoopS8 (n : Nat) (st : State8) (w : Array UInt32) : State8 :=
  match n with
  | 0 => st
  | k + 1 =>
    let prev := compressLoopS8 k st w
    roundStepS8 prev (getU32 K k) (getU32 w k)

theorem State8.ofFn_get (st : State8) : State8.ofFn st.get = st := by
  cases st; simp [State8.ofFn, State8.get]

/-- `roundStepS8` on `ofFn f` matches `compressLoop`'s one-step,
element-wise; each of the 8 cases is definitional. -/
private theorem roundStepS8_get_ofFn (f : Fin 8 → UInt32)
    (ki wi : UInt32) (i : Fin 8) :
    (roundStepS8 (State8.ofFn f) ki wi).get i =
    (let a := f ⟨0, by omega⟩; let b := f ⟨1, by omega⟩
     let c := f ⟨2, by omega⟩; let d := f ⟨3, by omega⟩
     let e := f ⟨4, by omega⟩; let ff := f ⟨5, by omega⟩
     let g := f ⟨6, by omega⟩; let h := f ⟨7, by omega⟩
     let t1 := h + bigSig1 e + ch e ff g + ki + wi
     let t2 := bigSig0 a + maj a b c
     (fun j : Fin 8 => match j with
      | ⟨0, _⟩ => t1 + t2 | ⟨1, _⟩ => a | ⟨2, _⟩ => b | ⟨3, _⟩ => c
      | ⟨4, _⟩ => d + t1 | ⟨5, _⟩ => e | ⟨6, _⟩ => ff | ⟨7, _⟩ => g) i) := by
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩
  | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ =>
    simp only [roundStepS8, State8.ofFn, State8.get]

/-- Two `State8` values with the same `.get` are equal. -/
private theorem State8.eq_of_get_eq (a b : State8) (h : ∀ i : Fin 8, a.get i = b.get i) :
    a = b := by
  have h0 := h ⟨0, by omega⟩; have h1 := h ⟨1, by omega⟩
  have h2 := h ⟨2, by omega⟩; have h3 := h ⟨3, by omega⟩
  have h4 := h ⟨4, by omega⟩; have h5 := h ⟨5, by omega⟩
  have h6 := h ⟨6, by omega⟩; have h7 := h ⟨7, by omega⟩
  cases a; cases b; simp [State8.get] at *; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- Core equivalence: `compressLoopS8` on `ofFn f` matches `compressLoop`
on `f`. -/
theorem compressLoopS8_eq_compressLoop (n : Nat) (f : Fin 8 → UInt32)
    (w : Array UInt32) (i : Fin 8) :
    (compressLoopS8 n (State8.ofFn f) w).get i = compressLoop n f w i := by
  induction n generalizing f i with
  | zero => simp [compressLoopS8, compressLoop, State8.get_ofFn]
  | succ k ih =>
    have hrepack : compressLoopS8 k (State8.ofFn f) w =
        State8.ofFn (compressLoop k f w) :=
      State8.eq_of_get_eq _ _ (fun j => by
        rw [State8.get_ofFn]
        exact ih f j)
    simp only [compressLoopS8, compressLoop]
    rw [hrepack]
    exact roundStepS8_get_ofFn (compressLoop k f w) (getU32 K k) (getU32 w k) i

/-- Fast `compress` using `State8`. -/
def compressFast (state w : Array UInt32) : Array UInt32 :=
  let s0 := State8.ofFn (fun i => getU32 state i)
  let sf := compressLoopS8 64 s0 w
  #[sf.s0 + getU32 state 0, sf.s1 + getU32 state 1,
    sf.s2 + getU32 state 2, sf.s3 + getU32 state 3,
    sf.s4 + getU32 state 4, sf.s5 + getU32 state 5,
    sf.s6 + getU32 state 6, sf.s7 + getU32 state 7]

theorem compressFast_eq_compress (state w : Array UInt32) :
    compressFast state w = compress state w := by
  simp only [compressFast, compress]
  have hrepack : compressLoopS8 64 (State8.ofFn fun i => getU32 state i) w =
      State8.ofFn (compressLoop 64 (fun i => getU32 state i) w) :=
    State8.eq_of_get_eq _ _ (fun j => by
      rw [State8.get_ofFn]
      exact compressLoopS8_eq_compressLoop 64 _ w j)
  rw [hrepack]; simp [State8.ofFn]

/-- Full optimized SHA-256. -/
def sha256Fast (msg : ByteArray) : ByteArray :=
  let padded := sha256Pad msg
  let blocks := parseBlocks padded
  let finalHash := blocks.foldl (init := H0) fun state block =>
    let w := msgSchedule block
    compressFast state w
  finalHash.foldl (init := ByteArray.empty) fun acc word => acc ++ writeBE32 word

@[csimp] theorem sha256_eq_sha256Fast : @sha256 = @sha256Fast := by
  funext msg; unfold sha256Fast sha256
  simp only [compressFast_eq_compress]

end Sha256
end AbstractCryptography
