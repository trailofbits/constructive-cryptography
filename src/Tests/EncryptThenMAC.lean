module

public import Commons.Constructions.EncryptThenMAC

/-!
# Encrypt-then-MAC clients

A symbolic client substitutes supplied component presentations through the assembly.
Failed verification terminates without a decryption query; accepted verification requests
decryption and preserves the cipher’s own rejection.
-/

@[expose] public section

open Commons SystemAlgebra
open scoped SystemAlgebra

namespace EncryptThenMACTests

-- `K`, `L` carry independent component keys; `M`, `C`, `T` are the message, ciphertext and tag
-- alphabets. The DSL interfaces, `SymmetricEncryption.encryptions`, and `MAC.tags` require
-- finite alphabets.
variable {K L M C T : Type} [Fintype K] [Fintype L] [Fintype M] [Fintype C] [Fintype T]
  [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq C]

/-- Equal component systems can be substituted through the named assembly. -/
example
    -- `scheme`, `mac` supply components at budget `2 * q`; `q` is the outside budget.
    (scheme : SymmetricEncryption K M C) (mac : MAC L C T) (q : ℕ)
    -- `R`, `S` are supplied presentations of the two component systems, on their exact domains.
    (R : TypedSystem (AE M C (2 * q))) (S : TypedSystem (Tagging C T (2 * q)))
    (hR : AE.system scheme = R) (hS : MAC.system mac = S) :
    encryptThenMAC.system scheme mac q = encryptThenMAC M C T • (R ∥ S) := by
  rw [encryptThenMAC.system_eq, hR, hS]

omit [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    [DecidableEq M] [DecidableEq C] in
/-- A rejected tag has a complete one-call transcript, so the cipher receives no query. -/
example
    -- `c`, `t` are arbitrary: rejection imposes no support condition on the submitted pair.
    (c : C) (t : T) :
    encryptThenMAC.body M C T none .dec (c, t)
      [(⟨.inr .verify, (c, t)⟩, ⟨.inr .verify, false⟩)] = .inl (some (), none) :=
  encryptThenMAC.dec_eq_false none c t

omit [Fintype K] [Fintype L] [DecidableEq K] [DecidableEq L]
    [DecidableEq M] [DecidableEq C] in
/-- Acceptance calls decryption, whose own rejection remains an outside rejection. -/
example
    -- `c`, `t` are the accepted pair; the cipher replies `none` at the requested ciphertext.
    (c : C) (t : T) :
    encryptThenMAC.body M C T none .dec (c, t)
        [(⟨.inr .verify, (c, t)⟩, ⟨.inr .verify, true⟩)] = .inr ⟨.inl .dec, c⟩ ∧
    encryptThenMAC.body M C T none .dec (c, t)
        [(⟨.inr .verify, (c, t)⟩, ⟨.inr .verify, true⟩),
         (⟨.inl .dec, c⟩, ⟨.inl .dec, none⟩)] = .inl (some (), none) :=
  ⟨encryptThenMAC.dec_cipher_query_eq none c t, encryptThenMAC.dec_eq_true none c t none⟩

#print axioms Commons.encryptThenMAC
#print axioms Commons.encryptThenMAC.enc_eq
#print axioms Commons.encryptThenMAC.dec_eq_true
#print axioms Commons.encryptThenMAC.dec_eq_false
#print axioms Commons.encryptThenMAC.system_eq

end EncryptThenMACTests
