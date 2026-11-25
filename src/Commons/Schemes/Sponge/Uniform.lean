module

public import Commons.Schemes.Sponge.Basic
public import Probability.Counting
public import Mathlib.Data.BitVec

/-!
# Uniform sponge states

A uniform byte state has uniform capacity and digest projections.
`fTransform_capacityPart_uniform` and `fTransform_digestPart_uniform` apply the
coordinate-projection law to the sponge's existing byte slices; `card_byteState`
provides their alphabet sizes. Both security arguments use these same laws.
-/

@[expose] public section

namespace Commons.Sponge

open Probability

/-- `BitVec 8` is finite via `BitVec.equivFin`, giving `Fintype (ByteState n)`. -/
instance instFintypeByte : Fintype (BitVec 8) :=
  Fintype.ofEquiv (Fin (2 ^ 8)) BitVec.equivFin.toEquiv.symm

/-- A byte vector of length `n` has `256 ^ n` possible values. -/
lemma card_byteState (n : ℕ) : Fintype.card (ByteState n) = 256 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin]
  have hb : Fintype.card (BitVec 8) = 256 := by
    rw [Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin]
    norm_num
  rw [hb]

/-- Projecting a uniform state onto its capacity bytes yields the uniform capacity law. -/
lemma fTransform_capacityPart_uniform (p : Parameters) (hr : p.rateBytes ≤ p.stateBytes) :
    Distribution.fTransform (capacityPart p) (Distribution.uniform (ByteState p.stateBytes)) =
      Distribution.uniform (ByteState p.capacityBytes) := by
  let idx : Fin p.capacityBytes → Fin p.stateBytes := fun i =>
    ⟨p.rateBytes + i.val, by
      have hi := i.isLt
      simp only [Parameters.capacityBytes] at hi
      omega⟩
  have hinj : Function.Injective idx := by
    intro a b h
    have hv : p.rateBytes + a.val = p.rateBytes + b.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  have hfun : capacityPart p = fun s i => s (idx i) := by
    funext s i
    have hlt : p.rateBytes + i.val < p.stateBytes := by
      have hi := i.isLt
      simp only [Parameters.capacityBytes] at hi
      omega
    simp only [capacityPart, idx, hlt, ↓reduceDIte]
  rw [hfun]
  exact Counting.fTransform_eval_uniform_eq_uniform idx hinj

/-- Projecting a uniform state onto its digest bytes yields the uniform digest law. -/
lemma fTransform_digestPart_uniform (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes) :
    Distribution.fTransform (digestPart p) (Distribution.uniform (ByteState p.stateBytes)) =
      Distribution.uniform (ByteState p.outputBytes) := by
  let idx : Fin p.outputBytes → Fin p.stateBytes := fun i =>
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt ho⟩
  have hinj : Function.Injective idx := by
    intro a b h
    have hv : (idx a).val = (idx b).val := congrArg Fin.val h
    exact Fin.ext hv
  have hfun : digestPart p = fun s i => s (idx i) := by
    funext s i
    have hlt : i.val < p.stateBytes := Nat.lt_of_lt_of_le i.isLt ho
    simp only [digestPart, idx, hlt, ↓reduceDIte]
  rw [hfun]
  exact Counting.fTransform_eval_uniform_eq_uniform idx hinj

end Commons.Sponge
