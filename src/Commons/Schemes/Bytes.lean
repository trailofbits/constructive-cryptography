import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.LawfulXor.Basic

/-!
# Byte strings

Byte strings of a fixed length `n`, with bytewise exclusive or, a lawful exclusive or with the
zero string as its identity, and byte strings of length at most `ℓ`. Vectors over a finite type
are finite, so byte strings of a fixed length are, and so are those of a bounded length.

## Main definitions

* `Bytes n`: the byte strings of length `n`
* `Bytes.xor`: bytewise exclusive or, the `^^^` of `Bytes n`, lawful with `0` as identity
* `ByteString ℓ`: the byte strings of length at most `ℓ`
-/

namespace Commons

universe u

/-! ### Finiteness of vectors

From VCVio (`VCVio/OracleComp/Constructions/SampleableType/Basic.lean`), by Quang Dao. -/

/-- The array-backed `Vector α n` is equivalent to an `n`-indexed function. -/
def vectorEquivFun (α : Type u) (n : ℕ) : Vector α n ≃ (Fin n → α) where
  toFun v i := v[i.1]
  invFun := Vector.ofFn
  left_inv v := by
    change Vector.ofFn (fun i : Fin n => v[i.1]) = v
    exact Vector.ofFn_getElem
  right_inv f := funext fun i => by
    simp

/-- `Vector α n` is finite when `α` is finite. -/
instance instFintypeVector (α : Type u) (n : ℕ) [Fintype α] : Fintype (Vector α n) :=
  Fintype.ofEquiv (Fin n → α) (vectorEquivFun α n).symm

/-! ### Byte strings -/

/-- **Byte strings** of length `n`. -/
abbrev Bytes (n : ℕ) := Vector UInt8 n

/-- Bytewise exclusive or. -/
def Bytes.xor {n : ℕ} (a b : Bytes n) : Bytes n := Vector.zipWith (· ^^^ ·) a b

instance {n : ℕ} : XorOp (Bytes n) := ⟨Bytes.xor⟩

instance {n : ℕ} : Zero (Bytes n) := ⟨Vector.replicate n 0⟩

@[simp] theorem Bytes.getElem_xor {n : ℕ} (a b : Bytes n) (i : ℕ) (hi : i < n) :
    (a ^^^ b)[i] = a[i] ^^^ b[i] := by
  change (Vector.zipWith (· ^^^ ·) a b)[i] = _
  simp

@[simp] theorem Bytes.getElem_zero {n : ℕ} (i : ℕ) (hi : i < n) : (0 : Bytes n)[i] = 0 := by
  change (Vector.replicate n 0)[i] = _
  simp

instance {n : ℕ} : LawfulXor (Bytes n) where
  xor_assoc a b c := Vector.ext fun i hi => by simp [UInt8.xor_assoc]
  xor_self a := Vector.ext fun i hi => by simp
  xor_zero a := Vector.ext fun i hi => by simp
  xor_comm a b := Vector.ext fun i hi => by simp [UInt8.xor_comm]

/-- **Byte strings of length at most `ℓ`.** -/
abbrev ByteString (ℓ : ℕ) := { xs : List UInt8 // xs.length ≤ ℓ }

/-- Byte strings of bounded length are finite: a byte string is its length and its bytes. -/
noncomputable instance (ℓ : ℕ) : Fintype (ByteString ℓ) := by
  let encode (xs : ByteString ℓ) : Σ n : Fin (ℓ + 1), Fin n.val → UInt8 :=
    ⟨⟨xs.val.length, Nat.lt_succ_of_le xs.property⟩, xs.val.get⟩
  apply Fintype.ofInjective encode
  intro xs ys h
  apply Subtype.ext
  have := congrArg (fun p : Σ n : Fin (ℓ + 1), Fin n.val → UInt8 => List.ofFn p.2) h
  simpa only [encode, List.ofFn_get] using this

end Commons
