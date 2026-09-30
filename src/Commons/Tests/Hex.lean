import Commons.Schemes.Hash.Keccak

/-!
# Hexadecimal helpers for the known-answer tests

Byte strings to and from hexadecimal, fixed-length byte strings and 32-byte seeds, and SHA3-256
digests, for comparing long outputs against reference values.
-/

namespace Commons.Tests

/-- A byte string in lowercase hexadecimal. -/
def toHex (bytes : ByteArray) : String :=
  bytes.foldl (fun acc b => acc ++ String.ofList (Nat.toDigits 16 (b.toNat / 16)) ++
    String.ofList (Nat.toDigits 16 (b.toNat % 16))) ""

/-- The value of a hexadecimal digit. -/
def hexValue (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- The bytes of a hexadecimal string. -/
def parseHex (s : String) : ByteArray :=
  let digits := s.toList.toArray
  ⟨(Array.range (digits.size / 2)).map fun i =>
    (hexValue digits[2 * i]! * 16 + hexValue digits[2 * i + 1]!).toUInt8⟩

/-- The first `n` bytes of a hexadecimal string. -/
def hexBytes (n : Nat) (s : String) : Vector UInt8 n :=
  Vector.ofFn fun i => (parseHex s)[i.val]!

/-- A 32-byte seed from hexadecimal. -/
def seed (s : String) : Vector UInt8 32 := hexBytes 32 s

/-- The SHA3-256 digest of a byte string, in hexadecimal. -/
def digest (bytes : ByteArray) : String :=
  toHex (Commons.Keccak.sha3_256 bytes)

end Commons.Tests
