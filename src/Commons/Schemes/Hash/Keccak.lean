/-!
# Keccak, SHA-3 and SHAKE

The permutation Keccak-f[1600] and the sponge over it, with its instances: the SHA-3 hash
functions and the SHAKE extendable-output functions of FIPS 202, and Keccak-256, the original
Keccak padding used by Ethereum. The state is 25 lanes of 64 bits, lane `(x, y)` at index
`5y + x`; bytes enter and leave the lanes in little-endian order (FIPS 202, §3.1).

## Main definitions

* `Keccak.keccakF`: Keccak-f[1600], 24 rounds of `ι ∘ χ ∘ π ∘ ρ ∘ θ` (§3.2–3.4)
* `Keccak.sponge rate suffix input outputLen`: the sponge, with the multi-rate padding after the
  domain suffix (§4, §5.1)
* `Keccak.sha3_224`, `Keccak.sha3_256`, `Keccak.sha3_384`, `Keccak.sha3_512`: SHA-3 (§6.1)
* `Keccak.shake128`, `Keccak.shake256`: SHAKE (§6.2)
* `Keccak.keccak256`: Keccak-256
-/

namespace Commons.Keccak

/-! ## Keccak-f[1600] (§3.2–3.4) -/

/-- The rotation offsets of `ρ`, lane `(x, y)` at index `5y + x`. -/
def rotOffsets : Array UInt64 := #[
     0,   1,  62,  28,  27,
    36,  44,   6,  55,  20,
     3,  10,  43,  25,  39,
    41,  45,  15,  21,   8,
    18,   2,  61,  56,  14
]

/-- The round constants of `ι` for the 24 rounds. -/
def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
]

/-- Rotation of a lane to the left by `n` bits. -/
def rotl64 (x : UInt64) (n : UInt64) : UInt64 :=
  if n == 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- The index of lane `(x, y)`. -/
def laneIndex (x y : Nat) : Nat :=
  5 * y + x

/-- The parity of column `x`. -/
def thetaC (state : Array UInt64) (x : Nat) : UInt64 :=
  state[laneIndex x 0]! ^^^ state[laneIndex x 1]! ^^^ state[laneIndex x 2]! ^^^
    state[laneIndex x 3]! ^^^ state[laneIndex x 4]!

/-- The parities of the two columns neighbouring column `x`. -/
def thetaD (state : Array UInt64) (x : Nat) : UInt64 :=
  thetaC state ((x + 4) % 5) ^^^ rotl64 (thetaC state ((x + 1) % 5)) 1

/-- `θ`: each lane with the parities of two neighbouring columns. -/
def theta (state : Array UInt64) : Array UInt64 :=
  Array.ofFn (n := 25) fun i => state[laneIndex (i.val % 5) (i.val / 5)]! ^^^ thetaD state (i.val % 5)

/-- `ρ`: each lane rotated by its offset. -/
def rho (state : Array UInt64) : Array UInt64 :=
  Array.ofFn (n := 25) fun i => rotl64 state[i.val]! rotOffsets[i.val]!

/-- `π`: the lanes permuted, lane `(x, y)` moving to `(y, 2x + 3y)`. -/
def pi (state : Array UInt64) : Array UInt64 :=
  Array.ofFn (n := 25) fun i =>
    let x' := i.val % 5
    let y' := i.val / 5
    state[laneIndex ((x' + 3 * y') % 5) x']!

/-- `χ`: the nonlinear map on each row. -/
def chi (state : Array UInt64) : Array UInt64 :=
  Array.ofFn (n := 25) fun i =>
    let x := i.val % 5
    let y := i.val / 5
    state[laneIndex x y]! ^^^
      (~~~ state[laneIndex ((x + 1) % 5) y]! &&& state[laneIndex ((x + 2) % 5) y]!)

/-- `ι`: the round constant added to lane `(0, 0)`. -/
def iota (state : Array UInt64) (rc : UInt64) : Array UInt64 :=
  state.set! 0 (state[0]! ^^^ rc)

/-- One round, `ι ∘ χ ∘ π ∘ ρ ∘ θ`. -/
def keccakRound (state : Array UInt64) (rc : UInt64) : Array UInt64 :=
  iota (chi (pi (rho (theta state)))) rc

/-- **Keccak-f[1600]**: 24 rounds. -/
def keccakF (state : Array UInt64) : Array UInt64 :=
  (List.range 24).foldl (fun s i => keccakRound s roundConstants[i]!) state

/-! ## The sponge (§4, §5.1) -/

/-- Byte `i` of the state, lanes in order, each little-endian. -/
def stateByte (state : Array UInt64) (i : Nat) : UInt8 :=
  ((state[i / 8]! >>> (8 * (i % 8)).toUInt64) &&& 0xFF).toUInt8

/-- The 200 bytes of the state. -/
def stateToBytes (state : Array UInt64) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := 200) fun i => stateByte state i.val

/-- Eight bytes of the input as one little-endian lane. -/
def inputLane (input : ByteArray) (lane : Nat) : UInt64 :=
  (List.range 8).foldl
    (fun acc j =>
      let idx := 8 * lane + j
      let b : UInt64 := if idx < input.size then input.data[idx]!.toUInt64 else 0
      acc ||| (b <<< (8 * j).toUInt64))
    0

/-- One rate block added into the state. -/
def xorBytesIntoState (state : Array UInt64) (input : ByteArray) (rateBytes : Nat) :
    Array UInt64 :=
  Array.ofFn (n := 25) fun i =>
    if i.val < rateBytes / 8 then state[i.val]! ^^^ inputLane input i.val else state[i.val]!

/-- The number of complete rate blocks of the input. -/
def fullBlockCount (rateBytes : Nat) (input : ByteArray) : Nat :=
  input.size / rateBytes

/-- Complete rate block `blockIndex` of the input. -/
def inputBlock (rateBytes : Nat) (input : ByteArray) (blockIndex : Nat) : ByteArray :=
  ByteArray.mk (input.data.extract (blockIndex * rateBytes) (blockIndex * rateBytes + rateBytes))

/-- One complete rate block absorbed. -/
def absorbBlock (rateBytes : Nat) (input : ByteArray) (state : Array UInt64)
    (blockIndex : Nat) : Array UInt64 :=
  keccakF (xorBytesIntoState state (inputBlock rateBytes input blockIndex) rateBytes)

/-- The complete rate blocks absorbed from the zero state. -/
def absorbFullBlocks (rateBytes : Nat) (input : ByteArray) : Array UInt64 :=
  (List.range (fullBlockCount rateBytes input)).foldl (absorbBlock rateBytes input)
    (Array.replicate 25 0)

/-- **The final padded block**: the remaining input, the domain suffix with the first bit of the
multi-rate padding `pad10*1`, zeros, and its last bit (§5.1). -/
def paddedFinalBlock (rateBytes : Nat) (suffix : UInt8) (input : ByteArray) (offset : Nat) :
    ByteArray :=
  let remaining := input.size - offset
  ByteArray.mk <| Array.ofFn (n := rateBytes) fun i =>
    let b : UInt8 := if i.val < remaining then input.data[offset + i.val]! else 0
    let b := if i.val == remaining then b ||| suffix else b
    if i.val + 1 == rateBytes then b ||| 0x80 else b

/-- The first `outputLen` bytes of the output: the rate part of the state, block by block, with
the permutation applied between blocks. -/
def squeeze (rateBytes : Nat) (outputLen : Nat) (state : Array UInt64) : ByteArray :=
  let blocks := (outputLen + rateBytes - 1) / rateBytes
  let output := (List.range blocks).foldl
    (fun (acc : ByteArray × Array UInt64) _ =>
      (acc.1 ++ (stateToBytes acc.2).extract 0 rateBytes, keccakF acc.2))
    (ByteArray.empty, state)
  output.1.extract 0 outputLen

/-- **The sponge** on Keccak-f[1600] with rate `rateBytes` bytes, the domain suffix `suffix`
before the padding, and `outputLen` output bytes. -/
def sponge (rateBytes : Nat) (suffix : UInt8) (input : ByteArray) (outputLen : Nat) : ByteArray :=
  let state := absorbFullBlocks rateBytes input
  let finalBlock := paddedFinalBlock rateBytes suffix input (fullBlockCount rateBytes input * rateBytes)
  squeeze rateBytes outputLen (keccakF (xorBytesIntoState state finalBlock rateBytes))

/-! ## SHA-3 and SHAKE (§6), Keccak-256 -/

/-- **SHA3-224**: rate 1152 bits, suffix `01`. -/
def sha3_224 (input : ByteArray) : ByteArray := sponge 144 0x06 input 28

/-- **SHA3-256**: rate 1088 bits, suffix `01`. -/
def sha3_256 (input : ByteArray) : ByteArray := sponge 136 0x06 input 32

/-- **SHA3-384**: rate 832 bits, suffix `01`. -/
def sha3_384 (input : ByteArray) : ByteArray := sponge 104 0x06 input 48

/-- **SHA3-512**: rate 576 bits, suffix `01`. -/
def sha3_512 (input : ByteArray) : ByteArray := sponge 72 0x06 input 64

/-- **SHAKE128** with `outputLen` output bytes: rate 1344 bits, suffix `1111`. -/
def shake128 (input : ByteArray) (outputLen : Nat) : ByteArray := sponge 168 0x1F input outputLen

/-- **SHAKE256** with `outputLen` output bytes: rate 1088 bits, suffix `1111`. -/
def shake256 (input : ByteArray) (outputLen : Nat) : ByteArray := sponge 136 0x1F input outputLen

/-- **Keccak-256**: rate 1088 bits, no domain suffix (the original Keccak padding). -/
def keccak256 (input : ByteArray) : ByteArray := sponge 136 0x01 input 32

end Commons.Keccak
