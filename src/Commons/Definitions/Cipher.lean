module

public import Commons.Definitions.Ideal

/-!
# Block ciphers

`BlockCipher` records deterministic encryption and decryption on one block type `X`, with
decryption undoing encryption. When `X` is finite, `BlockCipher.perm` identifies encryption
under a key with a permutation [1, §4.1, p. 96]; `encrypt_decrypt` gives its inverse law.

`BlockCipher.system` draws one uniform key and exposes encryption on `Evaluation X X q`.
`BlockCipher.bidirectionalSystem` uses one shared key for forward encryption and inverse
decryption on `Bidirectional X q`. The budget `q` counts queries across the exposed ports.
These systems can be compared with `URP` and `StrongURP` from `Commons.Definitions.Ideal`.

## Main definitions

* `BlockCipher K X`: the syntax
* `BlockCipher.perm`: encryption under a key, as a permutation of the blocks
* `BlockCipher.system E`, `BlockCipher.bidirectionalSystem E`: `E_k`, and `E_k` with `D_k`,
  for one uniform key

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra Probability

/-- **A block cipher** with keys `K` and blocks `X`: encryption `E` and decryption `D`, with `D`
inverting `E` under every key [1, §4.1, p. 96]. -/
structure BlockCipher
    -- `K` carries keys; `X` is both the message and ciphertext block type.
    (K X : Type) where
  /-- Encryption `E` of the “deterministic cipher” in [1, §4.1, p. 96]. -/
  encrypt : K → X → X
  /-- Decryption `D`. -/
  decrypt : K → X → X
  /-- Decryption inverts encryption. -/
  decrypt_encrypt : ∀ k x, decrypt k (encrypt k x) = x

-- `K` carries keys; `X` carries the blocks permuted under each key.
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
lemma BlockCipher.encrypt_decrypt [Finite X] (E : BlockCipher K X) (k : K) (y : X) :
    E.encrypt k (E.decrypt k y) = y :=
  (E.perm k).right_inv y

noncomputable section

-- The finite nonempty key space has a uniform law; `q` bounds all exposed queries.
variable [Fintype K] [Nonempty K] [Fintype X] {q : ℕ}

/-- Retain `k ∼ 𝒰[K]`; each admitted `eval(x)` returns `E.encrypt k x`,
for at most `q` queries on `Evaluation X X q` [1, §4.1, p. 96]. -/
def BlockCipher.system
    -- `E.encrypt` supplies the block permutation under the sampled key.
    (E : BlockCipher K X) : TypedSystem (Evaluation X X q) :=
  TypedSystem.sample (Distribution.uniform K) fun k =>
    TypedSystem.ofFunction fun _ x => E.encrypt k x

/-- Retain one `k ∼ 𝒰[K]`; `forward(x)` returns `E.encrypt k x` and `inverse(y)` returns
`E.decrypt k y`, with at most `q` queries across both ports [1, §4.1, p. 96]. -/
def BlockCipher.bidirectionalSystem
    -- `E` supplies both operations, which share the retained key.
    (E : BlockCipher K X) : TypedSystem (Bidirectional X q) :=
  TypedSystem.sample (Distribution.uniform K) fun k =>
    TypedSystem.ofFunction fun
      | .forward => fun x => E.encrypt k x
      | .inverse => fun y => E.decrypt k y

end

end Commons
