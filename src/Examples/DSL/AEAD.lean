module

public import Examples.DSL.AES
public import Commons.Schemes.Stream.CTR
public import Commons.Schemes.MAC.PMAC
public import Commons.Constructions.NonceEncryptThenMAC

/-!
AES-CTR followed by PMAC, with independent keys and associated data, from the CTR and PMAC
converters of `Commons.Schemes.Stream.CTR` and `Commons.Schemes.MAC.PMAC`. CTR runs from the
counter block of a caller-supplied 96-bit nonce, with a 32-bit block counter; nonce uniqueness is
the caller's security obligation, and decryption may repeat a nonce. PMAC authenticates the nonce,
the associated data and the ciphertext, with fixed-width lengths, and decryption checks the tag
with PMAC's verification.

The generic `Commons.nonceEncryptThenMAC` converter supplies the nonce/AD wiring. This example
supplies its CTR and PMAC components and the length-delimited authentication encoding.
-/

@[expose] public section

open SystemAlgebra SystemAlgebra.DSL Probability
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped SystemAlgebra SystemAlgebra.DSL

namespace DSLExamples.Authenticated
open Commons DSLExamples.Cipher

noncomputable section

/-- A 96-bit nonce. -/
abbrev Nonce := Bytes 12

/-- Byte strings fitting the 32-bit CTR block counter. -/
abbrev Message := ByteString (2 ^ 36)

/-- Big-endian encoding, with exactly `n` bytes. -/
def encodeNat (n value : Nat) : List UInt8 :=
  (List.range n).map fun i => UInt8.ofNat (value / 2 ^ (8 * (n - 1 - i)))

/-- Fixed-width nonce and lengths make the two variable strings unambiguous. -/
def authenticationBytes (input : Nonce × Message × Message) : List UInt8 :=
  let (nonce, associatedData, ciphertext) := input
  nonce.toList ++ encodeNat 8 associatedData.val.length ++ encodeNat 8 ciphertext.val.length ++
    associatedData.val ++ ciphertext.val

system AESCTR ≔ CTR (2 ^ 36) • AES
system AESPMAC ≔ PMAC authenticationBytes • AES
system AuthenticatedEncryption ≔
  nonceEncryptThenMAC Nonce Message Message Block • (AESCTR ∥ AESPMAC)

/-- The combined converter uses two independently keyed AES systems. -/
lemma authenticatedEncryption_eq (q : ℕ) :
    AuthenticatedEncryption (budget := q) =
      (nonceEncryptThenMAC Nonce Message Message Block ≫
        (CTR (2 ^ 36) ⊗ₘ PMAC authenticationBytes)) • (AES ∥ AES) := by
  unfold AuthenticatedEncryption AESCTR AESPMAC
  cc_normalize

end

end DSLExamples.Authenticated
