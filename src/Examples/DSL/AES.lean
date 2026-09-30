import ConstructiveCryptography.DSL
import ConstructiveCryptography.Notation
import Commons.Schemes.BlockCipher.AES

/-!
# AES in the DSL

AES-256 as a system with a random key, and converters around it: whitening, double encryption,
a fresh mask, CBC-MAC over a finite message space, and a two-key cascade; at per-port budgets,
whitening and the fresh mask are endomorphisms of the interface of a block function. Whitened AES
beside an unrelated resource, and a two-step hybrid bound through an ideal block cipher. The block
cipher is AES-256 of `Commons.Schemes.BlockCipher.AES`, answering at the interface `Evaluation` of
`Commons.Definitions.Ideal`, on blocks of sixteen bytes with bytewise exclusive or.
-/

open SystemAlgebra SystemAlgebra.DSL Probability
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped SystemAlgebra SystemAlgebra.DSL

namespace DSLExamples.Cipher
open Commons

/-- A block of sixteen bytes. -/
abbrev Block := Commons.AES.Block

interface Authentication(M : Type) [Fintype M]
  mac(message : M) → Block

system AES : Evaluation Block Block
  initialize
    key ←$ 𝒰[Commons.AES.Key .aes256]
  on eval(x : Block) → Block
    return Commons.AES.cipher .aes256 key x

converter Whitening(mask : Block) : Evaluation Block Block
  inside aes : Evaluation Block Block
  on eval(block : Block) → Block
    output ← aes.eval(mask ^^^ block)
    return mask ^^^ output

converter Twice : Evaluation Block Block
  inside aes : Evaluation Block Block
  on eval(block : Block) → Block
    first ← aes.eval(block)
    second ← aes.eval(first)
    return second

converter RandomMask : Evaluation Block Block
  inside aes : Evaluation Block Block
  on eval(block : Block) → Block
    mask ←$ 𝒰[Block]
    output ← aes.eval(mask ^^^ block)
    return mask ^^^ output

variable {M : Type} [Fintype M]

converter CBC(blockForm : M → List Block) : Authentication M
  inside aes : Evaluation Block Block
  on mac(message : M) → Block
    tag ← (0 : Block)
    for block ∈ blockForm message
      tag ← aes.eval(tag ^^^ block)
    return tag

converter Cascade : Evaluation Block Block
  inside first : Evaluation Block Block
  inside second : Evaluation Block Block
  on eval(block : Block) → Block
    middle ← first.eval(block)
    output ← second.eval(middle)
    return output

interface Control
  enabled(flag : Bool) → Fin 2

system Switch : Control
  on enabled(flag : Bool) → Fin 2
    if flag
      return 1
    else
      return 0

system DoubleAES ≔ Twice • AES
system WhitenedAES(mask : Block) ≔ Whitening mask • AES
system RandomizedAES ≔ RandomMask • AES
system ComposedAES(mask : Block) ≔ (Whitening mask ≫ Twice) • AES
system CBCMAC(blockForm : M → List Block) ≔ CBC blockForm • AES
system IndependentKeys ≔ Cascade • (AES ∥ AES)
system ParallelAES ≔ (Twice ⊗ₘ Twice) • (AES ∥ AES)

/-- At per-port budgets, port-preserving converters are endomorphisms of the block-cipher
interface: they compose and attach without changing the budget. -/
noncomputable def WhitenedMaskedAES (mask : Block) (q : Evaluation.Port → ℕ) :
    Interface.Resource (Evaluation.perPort Block Block q) :=
  (Whitening.perPort mask ≫ RandomMask.perPort) • AES.perPort

/-- The same converter accepts messages with different block counts. -/
noncomputable example (q : ℕ) : Interface.Resource (Authentication (Bool × Block × Block) q) :=
  CBCMAC (fun (long, first, second) => if long then [first, second] else [first])

theorem composedAES_eq (mask : Block) (q : ℕ) :
    ComposedAES mask (budget := q) = Whitening mask • (Twice • AES) := by
  unfold ComposedAES
  cc_normalize

theorem parallelAES_eq (q : ℕ) : ParallelAES (budget := q) = DoubleAES ∥ DoubleAES := by
  unfold ParallelAES DoubleAES
  cc_normalize

theorem cbc_nonexpanding (blockForm : M → List Block) {q : ℕ}
    (R S : Interface.Resource (Evaluation Block Block (CBC.bound blockForm * q))) :
    Δ (CBC blockForm • R) (CBC blockForm • S) ≤ Δ R S := by
  cc_nonexpand

/-- Parallel components keep their own alphabets: whitening AES beside an unrelated resource
leaves that resource unchanged. -/
theorem whitening_beside_switch (mask : Block) (q n : ℕ) :
    (Whitening mask (budget := q) ⊗ₘ 𝟙 (Control n)) • (AES ∥ Switch) =
      (Whitening mask • AES) ∥ Switch := by
  cc_normalize

/-- A two-step hybrid: a bound on distinguishing AES from an ideal block cipher `R`, and a bound
on the ideal system, give a bound on the real system. -/
theorem aes_hybrid {A : Interface} {q : ℕ} (α : A ⟶ Evaluation Block Block q)
    (R : Interface.Resource (Evaluation Block Block q)) (V : Interface.Resource A) (ε δ : ENNReal)
    (aesBound : Δ AES R ≤ ε) (idealBound : Δ (α • R) V ≤ δ) :
    Δ (α • AES) V ≤ ε + δ := by
  calc
    Δ (α • AES) V
        ≤ Δ (α • AES) (α • R) + Δ (α • R) V := by
          cc_triangle via (α • R)
          · exact le_rfl
          · exact le_rfl
    _ ≤ Δ AES R + Δ (α • R) V := add_le_add (by cc_nonexpand) le_rfl
    _ ≤ ε + δ := add_le_add aesBound idealBound

end DSLExamples.Cipher
