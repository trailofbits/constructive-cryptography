import Commons.Definitions.Ideal

/-!
# Block ciphers

A block cipher over keys `K` and blocks `X`: a deterministic cipher `(E, D)` whose messages and
ciphertexts are the blocks, with decryption inverting encryption (Boneh–Shoup, §4.1), so that
encryption under each key is a permutation of the blocks. Under a uniform key it is a system on
the interface of a function, and, with decryption answering inverse queries, on the interface of
a permutation. A PRP and a strong PRP need no notion of their own: the security of a block cipher
is the substitution of these systems for `URP` and `StrongURP` of `Commons.Definitions.Ideal`,
and a PRF is a keyed function substituting for `URF`.

Planned: the syntax of a Shannon cipher and perfect secrecy (Boneh–Shoup, Chapter 2).

## Main definitions

* `BlockCipher K X`: the syntax
* `BlockCipher.perm`: encryption under a key, as a permutation of the blocks
* `BlockCipher.Real E`, `BlockCipher.StrongReal E`: `E_k`, and `E_k` with `D_k`, for a uniform key
-/

namespace Commons

open SystemAlgebra Probability

/-- **A block cipher** with keys `K` and blocks `X`: encryption `E` and decryption `D`, with `D`
inverting `E` under every key (Boneh–Shoup, §4.1). -/
structure BlockCipher (K X : Type) where
  /-- Encryption `E`. -/
  encrypt : K → X → X
  /-- Decryption `D`. -/
  decrypt : K → X → X
  /-- Decryption inverts encryption. -/
  decrypt_encrypt : ∀ k x, decrypt k (encrypt k x) = x

variable {K X : Type}

/-- Encryption under the key `k`, a permutation of the finitely many blocks, with decryption as
its inverse. -/
def BlockCipher.perm [Finite X] (E : BlockCipher K X) (k : K) : Equiv.Perm X :=
  have hinj : Function.Injective (E.encrypt k) :=
    Function.LeftInverse.injective (E.decrypt_encrypt k)
  { toFun := E.encrypt k
    invFun := E.decrypt k
    left_inv := E.decrypt_encrypt k
    right_inv := fun y => by
      obtain ⟨x, rfl⟩ := (Finite.injective_iff_surjective.mp hinj) y
      rw [E.decrypt_encrypt] }

/-- Encryption inverts decryption. -/
theorem BlockCipher.encrypt_decrypt [Finite X] (E : BlockCipher K X) (k : K) (y : X) :
    E.encrypt k (E.decrypt k y) = y :=
  (E.perm k).right_inv y

noncomputable section

variable [Fintype K] [Nonempty K] [Fintype X] {q : ℕ}

/-- **The block cipher under a uniform key**: `E_k` for `k` uniform, answering each input with its
encryption. -/
def BlockCipher.Real (E : BlockCipher K X) : Interface.Resource (Evaluation X X q) :=
  Interface.Resource.sample (Distribution.uniform K) fun k =>
    Interface.Resource.ofFunction fun _ x => E.encrypt k x

/-- **The block cipher and its inverse under a uniform key**: `E_k` answering forward queries and
`D_k` answering inverse queries, for `k` uniform. -/
def BlockCipher.StrongReal (E : BlockCipher K X) : Interface.Resource (Bidirectional X q) :=
  Interface.Resource.sample (Distribution.uniform K) fun k =>
    Interface.Resource.ofFunction fun
      | .forward => fun x => E.encrypt k x
      | .inverse => fun y => E.decrypt k y

end

end Commons
