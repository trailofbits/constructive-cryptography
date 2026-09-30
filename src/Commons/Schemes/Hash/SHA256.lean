/-!
# SHA-256

The SHA-256 hash function of FIPS 180-4: padding (§5.1.1), the message schedule and the
64-round compression function on 32-bit words (§6.2.2), iterated over the 512-bit blocks from
the initial hash value (§5.3.3).

## Main definitions

* `SHA256.compress`: the compression function on one 512-bit block
* `SHA256.pad`: the padding of a message to a multiple of 512 bits
* `SHA256.sha256`: the hash of a byte string
-/

namespace Commons.SHA256

/-- A 32-bit word. -/
abbrev Word := BitVec 32

/-- A byte. -/
abbrev Byte := BitVec 8

/-! ## Functions (§4.1.2) -/

/-- `ROTRⁿ(x)`, rotation to the right by `n` bits. -/
def rotr (x : Word) (n : Nat) : Word :=
  (x >>> n) ||| (x <<< (32 - n))

/-- `Ch(e, f, g) = (e ∧ f) ⊕ (¬e ∧ g)`. -/
def ch (e f g : Word) : Word :=
  (e &&& f) ^^^ (~~~e &&& g)

/-- `Maj(a, b, c) = (a ∧ b) ⊕ (a ∧ c) ⊕ (b ∧ c)`. -/
def maj (a b c : Word) : Word :=
  (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)

/-- `Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
def bigSigma0 (x : Word) : Word :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- `Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
def bigSigma1 (x : Word) : Word :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- `σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. -/
def smallSigma0 (x : Word) : Word :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

/-- `σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`. -/
def smallSigma1 (x : Word) : Word :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-! ## Constants (§4.2.2, §5.3.3) -/

/-- The initial hash value `H⁽⁰⁾`. -/
def H0 : Array Word := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

/-- The 64 round constants `K₀, …, K₆₃`. -/
def K : Array Word := #[
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

/-! ## Compression (§6.2.2) -/

/-- The message schedule `W₀, …, W₆₃` of a 16-word block. -/
def messageSchedule (block : Array Word) : Array Word :=
  let rec expand (w : Array Word) (t : Nat) : Array Word :=
    if t ≥ 64 then w
    else
      let wt := smallSigma1 w[t - 2]! + w[t - 7]! + smallSigma0 w[t - 15]! + w[t - 16]!
      expand (w.push wt) (t + 1)
  termination_by 64 - t
  expand block 16

/-- The working variables `a, …, h`. -/
structure Working where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word

/-- The working variables initialized from an intermediate hash value. -/
def Working.ofArray (s : Array Word) : Working :=
  { a := s[0]!, b := s[1]!, c := s[2]!, d := s[3]!, e := s[4]!, f := s[5]!, g := s[6]!,
    h := s[7]! }

/-- The working variables as an eight-word array. -/
def Working.toArray (w : Working) : Array Word :=
  #[w.a, w.b, w.c, w.d, w.e, w.f, w.g, w.h]

/-- One round, with round constant `kt` and schedule word `wt`. -/
def round (w : Working) (kt wt : Word) : Working :=
  let t1 := w.h + bigSigma1 w.e + ch w.e w.f w.g + kt + wt
  let t2 := bigSigma0 w.a + maj w.a w.b w.c
  { a := t1 + t2, b := w.a, c := w.b, d := w.c, e := w.d + t1, f := w.e, g := w.f, h := w.g }

/-- The 64 rounds over a message schedule. -/
def runRounds (schedule : Array Word) (w0 : Working) : Working :=
  let rec go (t : Nat) (w : Working) : Working :=
    if t ≥ 64 then w
    else go (t + 1) (round w K[t]! schedule[t]!)
  termination_by 64 - t
  go 0 w0

/-- Word-wise addition of two eight-word states. -/
def stateAdd (x y : Array Word) : Array Word :=
  let rec go (i : Nat) (acc : Array Word) : Array Word :=
    if i ≥ x.size then acc
    else go (i + 1) (acc.push (x[i]! + y[i]!))
  termination_by x.size - i
  go 0 #[]

/-- **The compression function**: the next intermediate hash value from the current one and a
16-word block. -/
def compress (h : Array Word) (block : Array Word) : Array Word :=
  stateAdd h (runRounds (messageSchedule block) (Working.ofArray h)).toArray

/-! ## Padding and parsing (§5.1.1, §5.2.1) -/

/-- The byte at position `pos` of a word, most significant first. -/
def wordByte (w : Word) (pos : Nat) : Byte :=
  (w >>> (8 * (3 - pos))).setWidth 8

/-- Four bytes as a word, most significant first. -/
def bytesToWord (b0 b1 b2 b3 : Byte) : Word :=
  (b0.setWidth 32 <<< 24) ||| (b1.setWidth 32 <<< 16) ||| (b2.setWidth 32 <<< 8) |||
    b3.setWidth 32

/-- Bytes as big-endian words. -/
def bytesToWords (bytes : Array Byte) : Array Word :=
  let nWords := bytes.size / 4
  let rec go (i : Nat) (acc : Array Word) : Array Word :=
    if i ≥ nWords then acc
    else
      go (i + 1)
        (acc.push (bytesToWord bytes[4 * i]! bytes[4 * i + 1]! bytes[4 * i + 2]! bytes[4 * i + 3]!))
  termination_by nWords - i
  go 0 #[]

/-- Words as big-endian bytes. -/
def wordsToBytes (words : Array Word) : Array Byte :=
  words.foldl (fun acc w => acc ++ #[wordByte w 0, wordByte w 1, wordByte w 2, wordByte w 3]) #[]

/-- The 64-bit big-endian encoding of `n`. -/
def encodeBE64 (n : Nat) : Array Byte :=
  #[BitVec.ofNat 8 (n / 2 ^ 56), BitVec.ofNat 8 (n / 2 ^ 48), BitVec.ofNat 8 (n / 2 ^ 40),
    BitVec.ofNat 8 (n / 2 ^ 32), BitVec.ofNat 8 (n / 2 ^ 24), BitVec.ofNat 8 (n / 2 ^ 16),
    BitVec.ofNat 8 (n / 2 ^ 8), BitVec.ofNat 8 n]

/-- The number of zero bytes after the `1` bit, so that the padded message fills whole blocks. -/
def zeroPadCount (msgLen : Nat) : Nat :=
  let used := (msgLen + 1 + 8) % 64
  if used == 0 then 0 else 64 - used

/-- **Padding** (§5.1.1): a `1` bit, zeros, and the message length in bits as 64 bits. -/
def pad (msg : Array Byte) : Array Byte :=
  msg ++ #[(0x80 : Byte)] ++ Array.replicate (zeroPadCount msg.size) 0 ++ encodeBE64 (msg.size * 8)

/-- The 512-bit blocks of a padded message, each as 16 words (§5.2.1). -/
def toBlocks (padded : Array Byte) : Array (Array Word) :=
  (Array.range (padded.size / 64)).map fun i => bytesToWords (padded.extract (64 * i) (64 * i + 64))

/-! ## The hash (§6.2) -/

/-- **SHA-256** of a byte string. -/
def sha256 (msg : ByteArray) : ByteArray :=
  let digest := (toBlocks (pad (msg.data.map UInt8.toBitVec))).foldl compress H0
  ⟨(wordsToBytes digest).map UInt8.ofBitVec⟩

end Commons.SHA256
