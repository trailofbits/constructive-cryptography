/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/

/-!
# secp256k1 (SEC 2 §2.4.1), executable

The prime-order group of the FROST(secp256k1, SHA-256) ciphersuite
(RFC 9591 §6.5): affine short-Weierstrass arithmetic, scalar
multiplication by double-and-add, and the SEC 1 compressed point
encoding.

SEC 2 §2.4.1 fixes the curve — "The curve `E: y² = x³ + ax + b` over
`Fp` is defined by: `a = 00000000 … 00000000`, `b = 00000000 …
00000007`" — i.e. `y² = x³ + 7`, with cofactor `h = 01`, so the curve
group is prime-order as RFC 9591 §3.1 requires.

## Computability discipline (see `AGENTS.md`)

This is *carrier instantiation* material — the proof layer
(`Applications.Frost.Protocol`, `Applications.Frost.Algebra`) works over an abstract `F`-module and
never unfolds this file.  Everything here is engineered for concrete
evaluation:

* scalars and coordinates are plain `Nat` with explicit `% p` / `% q`
  (GMP-backed in the kernel — no `ZMod`, no `Fact p.Prime` obligation);
* all iteration is a fixed-width `Nat.fold` (256 bits) — structural,
  so `decide +kernel` reduces it;
* field inversion and square roots are Fermat exponentiations
  (`x^(p-2)`, `x^((p+1)/4)`; `p ≡ 3 mod 4`) — *defined* computationally,
  their correctness is exactly what the RFC 9591 known-answer tests
  in `FrostRfc9591Tests` validate;
* total functions throughout (identity handled as a constructor,
  out-of-range reads default) — no bound proofs inside terms the
  kernel must reduce.
-/

namespace AbstractCryptography
namespace Secp256k1

/-- SEC 2 §2.4.1 (Recommended Parameters secp256k1): "The elliptic curve
domain parameters over `Fp` associated with a Koblitz curve secp256k1 are
specified by the sextuple `T = (p, a, b, G, n, h)` where the finite field
`Fp` is defined by:

  `p = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F`
  `  = 2²⁵⁶ − 2³² − 2⁹ − 2⁸ − 2⁷ − 2⁶ − 2⁴ − 1`"

(The familiar `2²⁵⁶ − 2³² − 977` is the same number:
`2⁹+2⁸+2⁷+2⁶+2⁴+1 = 977`.) -/
def p : Nat :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

/-- SEC 2 §2.4.1: "Finally the order `n` of `G` and the cofactor are:

  `n = FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE BAAEDCE6 AF48A03B BFD25E8C D0364141`
  `h = 01`"

Cofactor 1, so the curve group *is* the prime-order group RFC 9591 §3.1
requires; the RFC calls this `G.Order()`. -/
def q : Nat :=
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- SEC 2 §2.4.1, the `x` of "The base point `G` … in uncompressed form
is: `G = 04 79BE667E F9DCBBAC 55A06295 CE870B07 029BFCDB 2DCE28D9
59F2815B 16F81798 483ADA77 26A3C465 5DA4FBFC 0E1108A8 FD17B448 A6855419
9C47D08F FB10D4B8`". -/
def Gx : Nat :=
  0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798

/-- SEC 2 §2.4.1, the `y` of the same uncompressed base point `G`. -/
def Gy : Nat :=
  0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

/-- Modular exponentiation for exponents `< 2^256`: square-and-multiply
over a fixed 256-step `Nat.fold` (structural, kernel-reducible). -/
def powMod (b e m : Nat) : Nat :=
  (Nat.fold 256 (fun i _ (acc : Nat × Nat) =>
    ((if (e >>> i) &&& 1 == 1 then acc.1 * acc.2 % m else acc.1),
      acc.2 * acc.2 % m))
    (1 % m, b % m)).1

/-- Field inverse by Fermat: `x⁻¹ = x^(p-2) mod p`. -/
def invP (x : Nat) : Nat := powMod x (p - 2) p

/-- Scalar inverse by Fermat: `x⁻¹ = x^(q-2) mod q`. -/
def invQ (x : Nat) : Nat := powMod x (q - 2) q

/-- Square root in `F_p` (when it exists): `a^((p+1)/4)`, valid since
`p ≡ 3 mod 4`.  Callers must check the result squares back to `a`. -/
def sqrtP (a : Nat) : Nat := powMod a ((p + 1) / 4) p

/-- Modular subtraction, total on `Nat`. -/
def subMod (a b m : Nat) : Nat := (a % m + (m - b % m)) % m

/-- A point of `E(F_p)`: the identity or an affine pair (coordinates
kept reduced mod `p` by the operations). -/
inductive Point where
  | infinity
  | affine (x y : Nat)
deriving DecidableEq, Repr

namespace Point

/-- Point doubling: `λ = 3x²/(2y)`, `x' = λ² - 2x`, `y' = λ(x - x') - y`
(the `a = 0` curve). -/
def double : Point → Point
  | infinity => infinity
  | affine x y =>
    if y % p == 0 then infinity
    else
      let lam := 3 * x % p * x % p * invP (2 * y % p) % p
      let x' := subMod (lam * lam) (2 * x) p
      let y' := subMod (lam * subMod x x' p) y p
      affine x' y'

/-- Point addition (affine, complete by case analysis). -/
def add : Point → Point → Point
  | infinity, Q => Q
  | P, infinity => P
  | affine x₁ y₁, affine x₂ y₂ =>
    if x₁ % p == x₂ % p then
      if (y₁ + y₂) % p == 0 then infinity
      else double (affine x₁ y₁)
    else
      let lam := subMod y₂ y₁ p * invP (subMod x₂ x₁ p) % p
      let x₃ := subMod (lam * lam) (x₁ + x₂) p
      let y₃ := subMod (lam * subMod x₁ x₃ p) y₁ p
      affine x₃ y₃

/-- Scalar multiplication by double-and-add, LSB first, over a fixed
256-bit `Nat.fold`. -/
def smul (k : Nat) (P : Point) : Point :=
  (Nat.fold 256 (fun i _ (acc : Point × Point) =>
    ((if (k >>> i) &&& 1 == 1 then add acc.1 acc.2 else acc.1),
      double acc.2))
    (infinity, P)).1

/-- Point negation. -/
def neg : Point → Point
  | infinity => infinity
  | affine x y => affine x ((p - y % p) % p)

end Point

/-- The base point `G`. -/
def basePoint : Point := .affine Gx Gy

/-- `G.ScalarBaseMult(k)`. -/
def baseMul (k : Nat) : Point := Point.smul k basePoint

/-! ### SEC 1 encodings (SEC 1 §2.3) -/

/-- `I2OSP` — SEC 1 §2.3.7 (Integer-to-Octet-String Conversion):
"Informally the idea is to represent the integer in binary then convert
the resulting bit string to an octet string."  Input "a non-negative
integer `x` together with the desired length `mlen` of the octet string.
It must be the case that: `2^{8(mlen)} > x`"; output `M` of `mlen`
octets, `Mᵢ = x_{mlen−1−i}` in base `2⁸`. -/
def natToBytesBE (n len : Nat) : ByteArray :=
  Nat.fold len (fun i _ acc => acc.push ((n >>> (8 * (len - 1 - i))).toUInt8))
    ByteArray.empty

/-- `OS2IP` — SEC 1 §2.3.8 (Octet-String-to-Integer Conversion):
"Informally the idea is simply to view the octet string as the base 256
representation of the integer." -/
def bytesToNatBE (bs : ByteArray) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- SEC 1 §2.3.3 (Elliptic-Curve-Point-to-Octet-String Conversion), the
compressed case (33 bytes) — RFC 9591 §6.5's `SerializeElement`.

"If point compression is being used, the idea is that the compressed
y-coordinate is placed in the leftmost octet of the octet string along
with an indication that point compression is on, and the x-coordinate is
placed in the remainder of the octet string."  Formally, for
`P = (x_P, y_P) ≠ O`: "2.2.1. If `q = p` is an odd prime, set
`ỹ_P = y_P (mod 2)`. … 2.3. Assign the value `02₁₆` to the single octet
`Y` if `ỹ_P = 0`, or the value `03₁₆` if `ỹ_P = 1`.  2.4. Output
`M = Y ‖ X`."

**Deviation from SEC 1**, deliberate: §2.3.3 step 1 says "If `P = O`,
output `M = 00₁₆`" — a *one*-octet string.  The identity maps to 33 zero
bytes here instead, keeping the function total and fixed-width; it stays
distinguishable from every valid encoding (whose leading octet is `02`
or `03`), and RFC 9591 §6.5's serializer rejects the identity
anyway. -/
def serializePoint : Point → ByteArray
  | .infinity => natToBytesBE 0 33
  | .affine x y =>
    (ByteArray.empty.push (if y % 2 == 0 then 0x02 else 0x03))
      ++ natToBytesBE x 32

/-- RFC 9591's `SerializeScalar` (32 bytes big-endian, reduced). -/
def serializeScalar (s : Nat) : ByteArray := natToBytesBE (s % q) 32

/-- Total byte access, default 0. -/
def getByte (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

/-- SEC 1 §2.3.4 (Octet-String-to-Elliptic-Curve-Point Conversion), the
compressed case — RFC 9591 §6.5's `DeserializeElement`, with its
validations: length, tag, `x < p`, on-curve (the recovered `y` squares
back to `x³ + 7`), and not the identity.  The parity of the recovered `y`
is matched against the tag, inverting §2.3.3's `ỹ_P = y_P (mod 2)`. -/
def deserializePoint (bs : ByteArray) : Option Point :=
  if bs.size == 33 then
    let tag := (getByte bs 0).toNat
    if tag == 2 || tag == 3 then
      let x := bytesToNatBE (Nat.fold 32
        (fun i _ acc => acc.push (getByte bs (i + 1))) ByteArray.empty)
      if x < p then
        let rhs := (x * x % p * x + 7) % p
        let y₀ := sqrtP rhs
        if y₀ * y₀ % p == rhs then
          some (.affine x (if y₀ % 2 == tag % 2 then y₀ else (p - y₀) % p))
        else none
      else none
    else none
  else none

end Secp256k1
end AbstractCryptography
