/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Applications.Frost

/-!
# FROST(secp256k1, SHA-256) known-answer tests — RFC 9591 Appendix E.5

The full E.5 vector (2-of-3, participants {1, 3}, message `"test"`),
exercised end to end: trusted-dealer shares, nonce generation,
nonce commitments, binding-factor inputs and binding factors,
signature shares, the aggregate signature bytes, and wire-level
verification (including a tamper check).

Separate, non-default lake target (`lake build FrostRfc9591Tests`),
like `Sha256Tests`.  Hash- and scalar-level KATs discharge by
`decide +kernel` (axiom-free); the point-multiplication KATs use
`native_decide` — one Fermat inversion per affine point-add makes
kernel reduction of a 256-bit scalar multiple too deep, and the
`Lean.ofReduceBool` trust stays quarantined in this target (see `AGENTS.md`,
"Performance and computability").
-/

namespace AbstractCryptography.FrostRfc9591.Tests

open AbstractCryptography.FrostRfc9591 AbstractCryptography.Secp256k1

private def hexNibble (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - 48
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87
  else 0

private def hexLoop : List Char → ByteArray → ByteArray
  | c₁ :: c₂ :: rest, acc =>
      hexLoop rest (acc.push (16 * hexNibble c₁ + hexNibble c₂).toUInt8)
  | _, acc => acc

/-- Hex string to bytes, structurally recursive (kernel-reducible,
unlike a `while`-loop parser). -/
private def hexToBytes (s : String) : ByteArray := hexLoop s.toList ByteArray.empty

/-! ### The E.5 vector -/

def sk : Nat := 0x0d004150d27c3bf2a42f312683d35fac7394b1e9e318249c1bfe7f0795a83114
def coeff : Nat := 0xfbf85eadae3058ea14f19148bb72b45e4399c0b16028acaf0395c9b03c823579
def groupPkHex : String := "02f37c34b66ced1fb51c34a90bdae006901f10625cc06c4f64663b0eae87d87b4f"
def msg : ByteArray := hexToBytes "74657374"

def share1 : Nat := 0x08f89ffe80ac94dcb920c26f3f46140bfc7f95b493f8310f5fc1ea2b01f4254c
def share2 : Nat := 0x04f0feac2edcedc6ce1253b7fab8c86b856a797f44d83d82a385554e6e401984
def share3 : Nat := 0x00e95d59dd0d46b0e303e500b62b7ccb0e555d49f5b849f5e748c071da8c0dbc

def randH1 : ByteArray := hexToBytes "7ea5ed09af19f6ff21040c07ec2d2adbd35b759da5a401d4c99dd26b82391cb2"
def randB1 : ByteArray := hexToBytes "47acab018f116020c10cb9b9abdc7ac10aae1b48ca6e36dc15acb6ec9be5cdc5"
def randH3 : ByteArray := hexToBytes "e6cc56ccbd0502b3f6f831d91e2ebd01c4de0479e0191b66895a4ffd9b68d544"
def randB3 : ByteArray := hexToBytes "7203d55eb82a5ca0d7d83674541ab55f6e76f1b85391d2c13706a89a064fd5b9"

def nonceH1 : Nat := 0x841d3a6450d7580b4da83c8e618414d0f024391f2aeb511d7579224420aa81f0
def nonceB1 : Nat := 0x8d2624f532af631377f33cf44b5ac5f849067cae2eacb88680a31e77c79b5a80
def nonceH3 : Nat := 0x2b19b13f193f4ce83a399362a90cdc1e0ddcd83e57089a7af0bdca71d47869b2
def nonceB3 : Nat := 0x7a443bde83dc63ef52dda354005225ba0e553243402a4705ce28ffaafe0f5b98

def comH1Hex : String := "03c699af97d26bb4d3f05232ec5e1938c12f1e6ae97643c8f8f11c9820303f1904"
def comB1Hex : String := "02fa2aaccd51b948c9dc1a325d77226e98a5a3fe65fe9ba213761a60123040a45e"
def comH3Hex : String := "03077507ba327fc074d2793955ef3410ee3f03b82b4cdc2370f71d865beb926ef6"
def comB3Hex : String := "02ad53031ddfbbacfc5fbda3d3b0c2445c8e3e99cbc4ca2db2aa283fa68525b135"

def bfInput1 : String := "02f37c34b66ced1fb51c34a90bdae006901f10625cc06c4f64663b0eae87d87b4fff9b5210ffbb3c07a73a7c8935be4a8c62cf015f6cf7ade6efac09a6513540fc3f5a816aaebc2114a811a415d7a55db7c5cbc1cf27183e79dd9def941b5d48010000000000000000000000000000000000000000000000000000000000000001"
def bfInput3 : String := "02f37c34b66ced1fb51c34a90bdae006901f10625cc06c4f64663b0eae87d87b4fff9b5210ffbb3c07a73a7c8935be4a8c62cf015f6cf7ade6efac09a6513540fc3f5a816aaebc2114a811a415d7a55db7c5cbc1cf27183e79dd9def941b5d48010000000000000000000000000000000000000000000000000000000000000003"
def bf1 : Nat := 0x3e08fe561e075c653cbfd46908a10e7637c70c74f0a77d5fd45d1a750c739ec6
def bf3 : Nat := 0x93f79041bb3fd266105be251adaeb5fd7f8b104fb554a4ba9a0becea48ddbfd7

def sigShare1 : Nat := 0xc4fce1775a1e141fb579944166eab0d65eefe7b98d480a569bbbfcb14f91c197
def sigShare3 : Nat := 0x0160fd0d388932f4826d2ebcd6b9eaba734f7c71cf25b4279a4ca2581e47b18d

def sigHex : String := "0205b6d04d3774c8929413e3c76024d54149c372d57aae62574ed74319b5ea14d0c65dde8492a7471437e6c2fe3da49b90d23f642b5c6dbe7e36089f096dd97324"

/-- The group public key and commitment points, deserialized from the
vector's wire encodings (`deserializePoint` costs one Fermat square
root each — kernel-feasible, and independently validated by the
`native_decide` recomputation below). -/
def groupPk : Point := (deserializePoint (hexToBytes groupPkHex)).getD .infinity
def comH1 : Point := (deserializePoint (hexToBytes comH1Hex)).getD .infinity
def comB1 : Point := (deserializePoint (hexToBytes comB1Hex)).getD .infinity
def comH3 : Point := (deserializePoint (hexToBytes comH3Hex)).getD .infinity
def comB3 : Point := (deserializePoint (hexToBytes comB3Hex)).getD .infinity

/-- The commitment list (ascending identifiers, per §5.2). -/
def commitmentList : List Commitment :=
  [⟨1, comH1, comB1⟩, ⟨3, comH3, comB3⟩]

/-! ### Scalar- and hash-level KATs (`decide +kernel`, axiom-free) -/

-- Trusted dealer (Appendix C.1): the shares are f(i) on f = sk + coeff·x.
theorem shares_kat :
    polynomialEvaluate [sk, coeff] 1 = share1 ∧
    polynomialEvaluate [sk, coeff] 2 = share2 ∧
    polynomialEvaluate [sk, coeff] 3 = share3 := by decide +kernel

-- Nonce generation (§4.1): H3(randomness ‖ SerializeScalar(share)).
theorem nonces_kat :
    nonceGenerate randH1 share1 = nonceH1 ∧
    nonceGenerate randB1 share1 = nonceB1 ∧
    nonceGenerate randH3 share3 = nonceH3 ∧
    nonceGenerate randB3 share3 = nonceB3 := by decide +kernel

-- Binding factor inputs (§4.4): prefix ‖ SerializeScalar(i), for both
-- participants (the deserialized commitments re-serialize into the
-- encoded commitment list inside the prefix).
theorem binding_factor_inputs_kat :
    (bindingFactorPrefix groupPk commitmentList msg
      ++ serializeScalar 1).data = (hexToBytes bfInput1).data ∧
    (bindingFactorPrefix groupPk commitmentList msg
      ++ serializeScalar 3).data = (hexToBytes bfInput3).data := by
  decide +kernel

-- Binding factors (§4.4): ρᵢ = H1(input).
theorem binding_factors_kat :
    computeBindingFactors groupPk commitmentList msg
      = [(1, bf1), (3, bf3)] := by decide +kernel

/-! ### Point-level KATs (`native_decide`: 256-bit scalar multiples) -/

-- Group public key: PK = g^sk (§5, PK = G.ScalarBaseMult(s)).
theorem group_pk_kat :
    (serializePoint (baseMul sk)).data = (hexToBytes groupPkHex).data := by
  native_decide

-- Nonce commitments (§5.1): D = g^d, E = g^e, in wire encoding.
theorem nonce_commitments_kat :
    (serializePoint (baseMul nonceH1)).data = (hexToBytes comH1Hex).data ∧
    (serializePoint (baseMul nonceB1)).data = (hexToBytes comB1Hex).data ∧
    (serializePoint (baseMul nonceH3)).data = (hexToBytes comH3Hex).data ∧
    (serializePoint (baseMul nonceB3)).data = (hexToBytes comB3Hex).data := by
  native_decide

-- Signature shares (§5.2): z_i = d_i + e_i·ρ_i + λ_i·sk_i·c.
theorem sig_shares_kat :
    signShare 1 share1 groupPk nonceH1 nonceB1 msg commitmentList = sigShare1 ∧
    signShare 3 share3 groupPk nonceH3 nonceB3 msg commitmentList = sigShare3 := by
  native_decide

-- Per-share verification (§5.3): both shares check against the
-- participants' public keys g^{sk_i}.
theorem verify_shares_kat :
    verifySignatureShare 1 (baseMul share1) comH1 comB1 sigShare1
      commitmentList groupPk msg = true ∧
    verifySignatureShare 3 (baseMul share3) comH3 comB3 sigShare3
      commitmentList groupPk msg = true := by
  native_decide

-- Aggregation (§5.3) + canonical encoding (Appendix A): the final
-- 65-byte signature.
theorem signature_kat :
    (encodeSignature
      (aggregate groupPk msg commitmentList [sigShare1, sigShare3])).data
      = (hexToBytes sigHex).data := by
  native_decide

-- Wire-level verification (Appendix B + §6.5 deserialization): the
-- vector's signature verifies under the group public key...
theorem signature_verifies :
    verifyBytes msg (hexToBytes sigHex) groupPk = true := by
  native_decide

-- ...and fails on a tampered message ("tesu").
theorem signature_rejects_tampered :
    verifyBytes (hexToBytes "74657375") (hexToBytes sigHex) groupPk = false := by
  native_decide

end AbstractCryptography.FrostRfc9591.Tests
