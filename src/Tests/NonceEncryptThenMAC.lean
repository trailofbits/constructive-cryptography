module

public import Commons.Constructions.NonceEncryptThenMAC

/-!
# Nonce/AD encrypt-then-MAC contracts

The symbolic client replaces cipher and tagging components using supplied functional contracts.
A heterogeneous instance has Boolean nonces and tags, unit associated data and three messages;
its roundtrip follows from the component function contracts alone.
-/

@[expose] public section

namespace NonceEncryptThenMACTests

open Commons SystemAlgebra
open scoped SystemAlgebra

-- `N`, `AD`, `M`, `T` are the four interface alphabets; `q` bounds outside queries.
-- Budget `0` below selects the same port alphabets as every other query allowance.
variable {N AD M T : Type} [Fintype N] [Fintype AD] [Fintype M] [Fintype T] {q : ℕ}

/-- Functional component contracts identify the complete attached system. -/
example
    -- `R` is the nonce cipher; `S` authenticates nonce/AD/ciphertext tuples.
    (R : TypedSystem (StreamCipher N M (2 * q)))
    (S : TypedSystem (Tagging (N × AD × M) T (2 * q)))
    -- `crypt`, `auth` give their replies through the supplied equalities `hR`, `hS`.
    (crypt : N × M → M)
    (auth : ∀ i, (Tagging (N × AD × M) T 0).X i → (Tagging (N × AD × M) T 0).Y i)
    (hR : R = TypedSystem.ofFunction (fun _ x => crypt x))
    (hS : S = TypedSystem.ofFunction (A := Tagging (N × AD × M) T (2 * q)) auth) :
    nonceEncryptThenMAC N AD M T • (R ∥ S) =
      TypedSystem.ofFunction (A := AEAD N AD M T q) (nonceEncryptThenMAC.reply crypt auth) := by
  rw [hR, hS, nonceEncryptThenMAC.smul_ofFunction]

/-- Tagging returns `true` and verification returns the submitted Boolean tag.
Budget `0` names the port alphabets, which are independent of the allowance. -/
def auth : ∀ i, (Tagging (Bool × Unit × Fin 3) Bool 0).X i →
    (Tagging (Bool × Unit × Fin 3) Bool 0).Y i
  | .tag, _ => true
  | .verify, (_, t) => t

/-- The identity cipher and `auth`, which accepts its generated tag `true`,
recover every message at every nonce. -/
example
    -- `n` is the common nonce and `m` is the encrypted message.
    (n : Bool) (m : Fin 3) :
    (nonceEncryptThenMAC Bool Unit (Fin 3) Bool (budget := 2) •
      (TypedSystem.ofFunction (A := StreamCipher Bool (Fin 3) 4) (fun _ x => x.2) ∥
       TypedSystem.ofFunction (A := Tagging (Bool × Unit × Fin 3) Bool 4) auth) :
        TypedSystem (AEAD Bool Unit (Fin 3) Bool 2)).1
      [(⟨.encrypt, (n, (), m)⟩, ⟨.encrypt, (m, true)⟩),
       (⟨.decrypt, (n, (), m, true)⟩, ⟨.decrypt, some m⟩)] = 1 :=
  nonceEncryptThenMAC.encrypt_decrypt_eq_of_correct
    Prod.snd (fun _ _ => rfl) auth (fun _ => rfl) (by omega) n () m

#print axioms Commons.nonceEncryptThenMAC.smul_ofFunction
#print axioms Commons.nonceEncryptThenMAC.encrypt_decrypt_eq_of_correct

end NonceEncryptThenMACTests
