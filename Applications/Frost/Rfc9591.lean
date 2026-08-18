/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Applications.Sha256
import Applications.Secp256k1

/-!
# FROST(secp256k1, SHA-256), executable (RFC 9591)

The full RFC 9591 wire-level pipeline for the secp256k1/SHA-256
ciphersuite (§6.5): the hash suite `H1`–`H5` via `expand_message_xmd`
(RFC 9380 §5.3.1) and `hash_to_field`, the §4 helpers (binding factors,
group commitment, challenge, interpolation), and the §5 two-round
signing protocol with aggregation and Appendix B verification.

This file is the *carrier instantiation* of the abstract layer's
parameters: `FrostProtocol`'s `H1`/`H2` hashes and the group become
concrete here, and its per-share formula
`z = d + e·ρ + λ·s·c` (`Frost.signShare`) is re-read at the wire level
in `signShare` below — the abstract theorems (`verify_aggregate` etc.)
already prove the algebra; the RFC 9591 known-answer tests in
`FrostRfc9591Tests` validate the encodings, hashes, and group
arithmetic that the abstract layer deliberately treats as parameters.

Randomness is explicit input throughout (MauRen16 §3.5: coins are a
resource) — `nonceGenerate` takes the 32 randomness bytes, exactly as
the RFC's test vectors supply them.

Everything is total, structurally recursive, and core-only
(`AGENTS.md`, "Performance and computability"): the KATs discharge by
`decide +kernel` or `native_decide` without touching any heartbeat budget.
-/

namespace AbstractCryptography
namespace FrostRfc9591

open Secp256k1 (Point q powMod invQ subMod natToBytesBE bytesToNatBE
  serializePoint serializeScalar baseMul getByte)

/-! ### The hash suite (RFC 9591 §6.5, RFC 9380 §5.3.1) -/

/-- Byte-wise xor of the first `a.size` bytes. -/
def strxor (a b : ByteArray) : ByteArray :=
  Nat.fold a.size (fun i _ acc => acc.push (getByte a i ^^^ getByte b i))
    ByteArray.empty

/-- First `len` bytes (total; short inputs zero-pad, never hit here). -/
def takeBytes (bs : ByteArray) (len : Nat) : ByteArray :=
  Nat.fold len (fun i _ acc => acc.push (getByte bs i)) ByteArray.empty

/-- `expand_message_xmd` with SHA-256 (RFC 9380 §5.3.1): `b₀` from the
zero-padded block, then `bᵢ = H(strxor(b₀, bᵢ₋₁) ‖ i ‖ DST′)`. -/
def expandMessageXmd (msg dst : ByteArray) (len : Nat) : ByteArray :=
  let dstPrime := dst ++ ByteArray.empty.push dst.size.toUInt8
  let zPad := Nat.fold 64 (fun _ _ acc => acc.push 0) ByteArray.empty
  let b0 := Sha256.sha256
    (zPad ++ msg ++ natToBytesBE len 2 ++ ByteArray.empty.push 0 ++ dstPrime)
  let b1 := Sha256.sha256 (b0 ++ ByteArray.empty.push 1 ++ dstPrime)
  let ell := (len + 31) / 32
  let out := (Nat.fold (ell - 1) (fun i _ (acc : ByteArray × ByteArray) =>
    let bi := Sha256.sha256
      (strxor b0 acc.2 ++ ByteArray.empty.push (i + 2).toUInt8 ++ dstPrime)
    (acc.1 ++ bi, bi)) (b1, b1)).1
  takeBytes out len

/-- The ciphersuite context string, `"FROST-secp256k1-SHA256-v1"`. -/
def contextString : ByteArray := "FROST-secp256k1-SHA256-v1".toUTF8

/-- `hash_to_field` into the scalar field: `OS2IP(expand(m, DST, 48)) mod q`
(RFC 9380 §5.2 with `m = 1`, `L = 48`). -/
def hashToFieldQ (msg dst : ByteArray) : Nat :=
  bytesToNatBE (expandMessageXmd msg dst 48) % q

/-- `H1` — binding factors (DST suffix `"rho"`). -/
def H1 (m : ByteArray) : Nat := hashToFieldQ m (contextString ++ "rho".toUTF8)

/-- `H2` — the challenge (DST suffix `"chal"`). -/
def H2 (m : ByteArray) : Nat := hashToFieldQ m (contextString ++ "chal".toUTF8)

/-- `H3` — nonces (DST suffix `"nonce"`). -/
def H3 (m : ByteArray) : Nat := hashToFieldQ m (contextString ++ "nonce".toUTF8)

/-- `H4` — message pre-hash, plain SHA-256 with prefix. -/
def H4 (m : ByteArray) : ByteArray :=
  Sha256.sha256 (contextString ++ "msg".toUTF8 ++ m)

/-- `H5` — commitment-list pre-hash, plain SHA-256 with prefix. -/
def H5 (m : ByteArray) : ByteArray :=
  Sha256.sha256 (contextString ++ "com".toUTF8 ++ m)

/-! ### §4 helpers -/

/-- One participant's round-one output: identifier (a nonzero scalar,
carried as `Nat`) and the two nonce commitments. -/
structure Commitment where
  id : Nat
  D : Point
  E : Point

/-- `encode_group_commitment_list` (§4.3). -/
def encodeCommitmentList (l : List Commitment) : ByteArray :=
  l.foldl (fun acc c =>
    acc ++ serializeScalar c.id ++ serializePoint c.D
      ++ serializePoint c.E) ByteArray.empty

/-- The `rho_input_prefix` of §4.4:
`SerializeElement(PK) ‖ H4(msg) ‖ H5(encoded commitment list)`. -/
def bindingFactorPrefix (groupPk : Point) (l : List Commitment)
    (msg : ByteArray) : ByteArray :=
  serializePoint groupPk ++ H4 msg ++ H5 (encodeCommitmentList l)

/-- `compute_binding_factors` (§4.4): `ρᵢ = H1(prefix ‖ i)`. -/
def computeBindingFactors (groupPk : Point) (l : List Commitment)
    (msg : ByteArray) : List (Nat × Nat) :=
  let pre := bindingFactorPrefix groupPk l msg
  l.map fun c => (c.id, H1 (pre ++ serializeScalar c.id))

/-- `binding_factor_for_participant` (§4.3), total (unknown id ↦ 0). -/
def bindingFactorFor (bfl : List (Nat × Nat)) (id : Nat) : Nat :=
  ((bfl.find? (·.1 == id)).map (·.2)).getD 0

/-- `compute_group_commitment` (§4.5): `R = Σᵢ (Dᵢ + ρᵢ·Eᵢ)`. -/
def groupCommitment (l : List Commitment) (bfl : List (Nat × Nat)) : Point :=
  l.foldl (fun acc c =>
    Point.add (Point.add acc c.D)
      (Point.smul (bindingFactorFor bfl c.id) c.E)) .infinity

/-- `compute_challenge` (§4.6):
`c = H2(SerializeElement(R) ‖ SerializeElement(PK) ‖ msg)`. -/
def challenge (r groupPk : Point) (msg : ByteArray) : Nat :=
  H2 (serializePoint r ++ serializePoint groupPk ++ msg)

/-- `derive_interpolating_value` (§4.2): the Lagrange coefficient at 0,
`λᵢ = Π_{j≠i} xⱼ / Π_{j≠i} (xⱼ - xᵢ) mod q` (denominator inverted by
Fermat). -/
def interpolatingValue (l : List Nat) (xi : Nat) : Nat :=
  let num := l.foldl (fun acc xj =>
    if xj == xi then acc else acc * xj % q) 1
  let den := l.foldl (fun acc xj =>
    if xj == xi then acc else acc * subMod xj xi q % q) 1
  num * invQ den % q

/-! ### §5 signing, aggregation, verification -/

/-- `nonce_generate` (§4.1) with the randomness explicit:
`H3(random_bytes ‖ SerializeScalar(secret))`. -/
def nonceGenerate (randomness : ByteArray) (sk : Nat) : Nat :=
  H3 (randomness ++ serializeScalar sk)

/-- Round two, `sign` (§5.2): the signature share
`z_i = d_i + e_i·ρ_i + λ_i·sk_i·c` — `Frost.signShare` at the wire
level, with `ρ`, `λ`, `c` computed per the RFC rather than taken as
parameters. -/
def signShare (id sk : Nat) (groupPk : Point) (d e : Nat)
    (msg : ByteArray) (l : List Commitment) : Nat :=
  let bfl := computeBindingFactors groupPk l msg
  let rho := bindingFactorFor bfl id
  let lam := interpolatingValue (l.map (·.id)) id
  let c := challenge (groupCommitment l bfl) groupPk msg
  (d + e * rho + lam * sk % q * c) % q

/-- `aggregate` (§5.3): `(R, z = Σ zᵢ)`. -/
def aggregate (groupPk : Point) (msg : ByteArray) (l : List Commitment)
    (shares : List Nat) : Point × Nat :=
  let bfl := computeBindingFactors groupPk l msg
  (groupCommitment l bfl, shares.foldl (fun acc z => (acc + z) % q) 0)

/-- Canonical signature encoding (Appendix A):
`SerializeElement(R) ‖ SerializeScalar(z)`, 65 bytes. -/
def encodeSignature (sig : Point × Nat) : ByteArray :=
  serializePoint sig.1 ++ serializeScalar sig.2

/-- `prime_order_verify` (Appendix B): `g^z = R + c·PK`. -/
def verify (msg : ByteArray) (sig : Point × Nat) (groupPk : Point) : Bool :=
  let c := challenge sig.1 groupPk msg
  baseMul sig.2 == Point.add sig.1 (Point.smul c groupPk)

/-- Signature verification from the 65-byte wire encoding, with `R`
deserialized and validated (RFC 9591 §6.5 `DeserializeElement`). -/
def verifyBytes (msg sigBytes : ByteArray) (groupPk : Point) : Bool :=
  match Secp256k1.deserializePoint (takeBytes sigBytes 33) with
  | none => false
  | some r =>
    let z := bytesToNatBE (Nat.fold 32
      (fun i _ acc => acc.push (getByte sigBytes (i + 33))) ByteArray.empty)
    z < q && verify msg (r, z) groupPk

/-- `verify_signature_share` (§5.3):
`g^{z_i} = D_i + ρ_i·E_i + (c·λ_i)·PK_i`. -/
def verifySignatureShare (id : Nat) (pkI : Point) (hidingCom bindingCom : Point)
    (share : Nat) (l : List Commitment) (groupPk : Point)
    (msg : ByteArray) : Bool :=
  let bfl := computeBindingFactors groupPk l msg
  let rho := bindingFactorFor bfl id
  let lam := interpolatingValue (l.map (·.id)) id
  let c := challenge (groupCommitment l bfl) groupPk msg
  baseMul share ==
    Point.add (Point.add hidingCom (Point.smul rho bindingCom))
      (Point.smul (c * lam % q) pkI)

/-- Trusted-dealer share derivation (Appendix C.1,
`polynomial_evaluate` in Horner form): coefficients constant-first. -/
def polynomialEvaluate (coeffs : List Nat) (x : Nat) : Nat :=
  coeffs.foldr (fun c acc => (c + acc * x) % q) 0

end FrostRfc9591
end AbstractCryptography
