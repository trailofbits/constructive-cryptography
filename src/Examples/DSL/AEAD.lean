import Examples.DSL.AES
import Commons.Schemes.Stream.CTR
import Commons.Schemes.MAC.PMAC

/-!
AES-CTR followed by PMAC, with independent keys and associated data, from the CTR and PMAC
converters of `Commons.Schemes.Stream.CTR` and `Commons.Schemes.MAC.PMAC`. CTR runs from the
counter block of a caller-supplied 96-bit nonce, with a 32-bit block counter; nonce uniqueness is
the caller's security obligation, and decryption may repeat a nonce. PMAC authenticates the nonce,
the associated data and the ciphertext, with fixed-width lengths, and decryption checks the tag
with PMAC's verification.

The combination and its length-delimited authentication encoding are specified here; this is not
a claim of a standardized AEAD mode or a security reduction.
-/

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

interface AEAD
  encrypt(nonce : Nonce, associatedData : Message, message : Message) → Message × Block
  decrypt(nonce : Nonce, associatedData : Message, ciphertext : Message, tag : Block) →
    Option Message

converter EncryptThenMAC : AEAD
  inside cipher : StreamCipher (2 ^ 36)
  inside auth : Tagging (Nonce × Message × Message) Block
  on encrypt(nonce : Nonce, associatedData : Message, message : Message) → Message × Block
    ciphertext ← cipher.crypt(nonce, message)
    tag ← auth.tag(nonce, associatedData, ciphertext)
    return (ciphertext, tag)
  on decrypt(nonce : Nonce, associatedData : Message, ciphertext : Message, tag : Block) →
      Option Message
    valid ← auth.verify((nonce, associatedData, ciphertext), tag)
    if valid
      message ← cipher.crypt(nonce, ciphertext)
      return some message
    else
      return none

system AESCTR ≔ CTR (2 ^ 36) • AES
system AESPMAC ≔ PMAC authenticationBytes • AES
system AuthenticatedEncryption ≔ EncryptThenMAC • (AESCTR ∥ AESPMAC)

/-- The combined converter uses two independently keyed AES resources. -/
theorem authenticatedEncryption_eq (q : ℕ) :
    AuthenticatedEncryption (budget := q) =
      (EncryptThenMAC ≫ (CTR (2 ^ 36) ⊗ₘ PMAC authenticationBytes)) • (AES ∥ AES) := by
  unfold AuthenticatedEncryption AESCTR AESPMAC
  cc_normalize

end

end DSLExamples.Authenticated
