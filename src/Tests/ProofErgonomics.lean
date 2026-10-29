import ConstructiveCryptography.Notation
import RandomSystems.Typed.ParallelAllAttachment
import RandomSystems.Typed.SamplingAlgebra
import Tests.TypedNaryParallel

/-!
# Direct systems: notation and deterministic assembly

Direct typed actions, categorical arrows and the selected CC attachment field normalize by
the same laws. The examples cover the selected distance and its non-expansion, notation
elaboration, finite-family locality, dependent
initial samples, serial attachment and construction proofs. `guard_target` checks the
elaborated goals; trace guards check the chosen rules. Negative tests preserve shared
randomness and leave a separately supplied action unrewritten.
-/

namespace SystemAlgebra.Tests.ProofErgonomics

open Probability CategoryTheory CategoryTheory.MonoidalCategory
open scoped SystemAlgebra

/-- The CC notation `Δ R S` is the systems-level transcript distance by definition
(`Interface.cc_distance_eq`). -/
example {A : Interface} (R S : TypedSystem A) : Δ R S = R.1.transcriptDistance S.1 := rfl

/-- With the full `Notation` imported, `Δ R S` on an arbitrary resource theory `Phi` is still
`distance R S` of its own selected `CompatiblePseudoMetric`: the typed-system handler fails on
`Phi A` and defers to the generic one, without substituting the transcript metric. -/
example {C : Type} [Category C] [MonoidalCategory C] {Phi : C → Type}
    [ConstructiveCryptography.ResourceTheory C Phi]
    [ConstructiveCryptography.CompatiblePseudoMetric C Phi] {A : C} (R S : Phi A) :
    Δ R S = ConstructiveCryptography.CryptographicAlgebra.distance R S := rfl

/-- Likewise `R ∥ S` on `Phi A`, `Phi B` is the theory's own selected `parallel R S`, not
`TypedSystem.parallel`: the typed handler fails and defers to the generic one. -/
example {C : Type} [Category C] [MonoidalCategory C] {Phi : C → Type}
    [ConstructiveCryptography.ResourceTheory C Phi]
    [ConstructiveCryptography.CryptographicAlgebra C Phi] {A B : C} (R : Phi A) (S : Phi B) :
    R ∥ S = ConstructiveCryptography.CryptographicAlgebra.parallel R S := rfl

/-- Attachment is non-expanding for the transcript metric, `Δ(αR, αS) ≤ Δ(R, S)`, by
`cc_nonexpand`; the instance proves this field from the closure bound (Maurer 2011, Lemma 1). -/
example {A B : Interface} (α : A ⟶ B) (R S : TypedSystem B) :
    Δ (α • R) (α • S) ≤ Δ R S := by
  cc_nonexpand

/-- The probability notation elaborates to a normalized law, with the raw law explicit. -/
example : (𝒰[Bool] : Distribution.ProbDist Bool).1 = Distribution.uniform Bool := by
  guard_target = (Distribution.ProbDist.uniform Bool).1 = Distribution.uniform Bool
  rfl

/-- Direct functional notation has the existing carrier as its elaborated goal. -/
example {A : Interface} (f : ∀ i, A.X i → A.Y i) :
    (system [A] i x => f i x) = TypedSystem.ofFunction f := by
  guard_target = TypedSystem.ofFunction f = TypedSystem.ofFunction f
  rfl

/-- Sampling notation elaborates to `TypedSystem.sample` of the raw law, without a DSL import. -/
example {A : Interface} (f : Bool → ∀ i, A.X i → A.Y i) :
    (sample b ←$ 𝒰[Bool]; system [A] i x => f b i x) =
      TypedSystem.sample (Distribution.uniform Bool) (fun b => TypedSystem.ofFunction (f b)) := by
  change TypedSystem.sample (Distribution.uniform Bool) (fun b => TypedSystem.ofFunction (f b)) =
    TypedSystem.sample (Distribution.uniform Bool) (fun b => TypedSystem.ofFunction (f b))
  rfl

/-- Finite-family locality by its law `TypedConverter.parallelAll_attach`:
`(⨂ₘ k, α k) • (∥ k, R k) = ∥ k, α k • R k` for arbitrary component systems `R k`. -/
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : ∀ k, TypedSystem (B k)) :
    TypedConverter.parallelAll α • TypedSystem.parallelAll R =
      TypedSystem.parallelAll (fun k => α k • R k) := by
  exact TypedConverter.parallelAll_attach α R

/-- The same equation in family notation, by `cc_normalize`; the target elaborates to
`parallelAll`. -/
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : ∀ k, TypedSystem (B k)) :
    (⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k) := by
  guard_target = TypedConverter.parallelAll α • TypedSystem.parallelAll R =
    TypedSystem.parallelAll (fun k => α k • R k)
  cc_normalize

/-- A categorical arrow enters an initial sample, `α • sample P R = sample P (fun s => α • R s)`,
for a normalized finite-support law `P` on an arbitrary, possibly infinite, type `S`. -/
example {A B : Interface} {S : Type} (α : A ⟶ B) (P : Distribution.ProbDist S)
    (R : S → TypedSystem B) :
    α • TypedSystem.sample P.1 R = TypedSystem.sample P.1 (fun s => α • R s) := by
  cc_normalize

/-- Nested samples `s ← P; t ← Q s`: the second law depends on the first draw, the carriers
`S` and `T s` need not be finite, and `α` enters both binders. -/
example {A B : Interface} {S : Type} {T : S → Type} (α : A ⟶ B)
    (P : Distribution.ProbDist S) (Q : ∀ s, Distribution.ProbDist (T s))
    (R : ∀ s, T s → TypedSystem B) :
    α • TypedSystem.sample P.1 (fun s => TypedSystem.sample (Q s).1 (R s)) =
      TypedSystem.sample P.1 (fun s => TypedSystem.sample (Q s).1 (fun t => α • R s t)) := by
  cc_normalize

/-- Serial order: `(α ≫ β) • sample P R = sample P (fun s => α • (β • R s))`, the inner `β`
attached first. -/
example {A B C : Interface} {S : Type} (α : A ⟶ B) (β : B ⟶ C)
    (P : Distribution.ProbDist S) (R : S → TypedSystem C) :
    (α ≫ β) • TypedSystem.sample P.1 R =
      TypedSystem.sample P.1 (fun s => α • (β • R s)) := by
  cc_normalize

/-- The same normal form for the direct composition `TypedConverter.comp α β`. -/
example {A B C : Interface} {S : Type} (α : TypedConverter A B) (β : TypedConverter B C)
    (P : Distribution.ProbDist S) (R : S → TypedSystem C) :
    TypedConverter.comp α β • TypedSystem.sample P.1 R =
      TypedSystem.sample P.1 (fun s => α • (β • R s)) := by
  cc_normalize

/-- `cc_construct` leaves `ResourceTheory.attach α (sample P R) = sample P (fun s => α • R s)`,
an equation in the attachment field, which normalizes by the same laws. -/
example {A B : Interface} {S : Type} (α : A ⟶ B) (P : Distribution.ProbDist S)
    (R : S → TypedSystem B) :
    {TypedSystem.sample P.1 R} —[α]→ {TypedSystem.sample P.1 (fun s => α • R s)} := by
  cc_construct
  cc_normalize

/-- The direct identity, `TypedConverter.id A • R = R`, by `cc_normalize`. -/
example {A : Interface} (R : TypedSystem A) : TypedConverter.id A • R = R := by
  cc_normalize

/-- Binary locality under one shared draw, with the direct `TypedConverter.parallel α β`:
`(α ∥ β) • sample P (fun s => R s ∥ T s) = sample P (fun s => α • R s ∥ β • T s)`. -/
example {A B C D : Interface} {S : Type}
    (α : TypedConverter A B) (β : TypedConverter C D) (P : Distribution.ProbDist S)
    (R : S → TypedSystem B) (T : S → TypedSystem D) :
    TypedConverter.parallel α β • TypedSystem.sample P.1 (fun s => R s ∥ T s) =
      TypedSystem.sample P.1 (fun s => (α • R s) ∥ (β • T s)) := by
  cc_normalize

/-- The same binary normal form from the categorical tensor `α ⊗ₘ β`. -/
example {A B C D : Interface} {S : Type} (α : A ⟶ B) (β : C ⟶ D)
    (P : Distribution.ProbDist S) (R : S → TypedSystem B) (T : S → TypedSystem D) :
    (α ⊗ₘ β) • TypedSystem.sample P.1 (fun s => R s ∥ T s) =
      TypedSystem.sample P.1 (fun s => (α • R s) ∥ (β • T s)) := by
  cc_normalize

/-- Serial composition of two families under one shared draw:
`((⨂ₘ k, α k) ≫ (⨂ₘ k, β k)) • sample P (fun s => ∥ k, R s k) =
sample P (fun s => ∥ k, α k • (β k • R s k))`. -/
example {K S : Type} [Fintype K] [DecidableEq K] {A B C : K → Interface}
    (α : ∀ k, A k ⟶ B k) (β : ∀ k, B k ⟶ C k)
    (P : Distribution.ProbDist S) (R : S → ∀ k, TypedSystem (C k)) :
    ((⨂ₘ k, α k) ≫ (⨂ₘ k, β k)) • TypedSystem.sample P.1 (fun s => ∥ k, R s k) =
      TypedSystem.sample P.1 (fun s => ∥ k, α k • (β k • R s k)) := by
  cc_normalize

/-- Negative: under a separately supplied action `HSMul (A ⟶ B) (TypedSystem B) (TypedSystem A)`,
`cc_normalize` does not replace it by the canonical attachment and leaves the goal open. -/
example {A B : Interface} {S : Type}
    [_otherAction : HSMul (A ⟶ B) (TypedSystem B) (TypedSystem A)]
    (α : A ⟶ B) (P : Distribution.ProbDist S) (R : S → TypedSystem B)
    (h : α • TypedSystem.sample P.1 R = TypedSystem.sample P.1 (fun s => α • R s)) :
    α • TypedSystem.sample P.1 R = TypedSystem.sample P.1 (fun s => α • R s) := by
  fail_if_success solve | cc_normalize
  exact h

/-- One retained draw by the named laws: `smul_sample` moves the attachment inside
`b ← U(Bool)`, then `parallelAll_attach` acts componentwise,
`(⨂ₘ k, α k) • sample U (fun b => ∥ k, R b k) = sample U (fun b => ∥ k, α k • R b k)`. -/
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : Bool → ∀ k, TypedSystem (B k)) :
    TypedConverter.parallelAll α • TypedSystem.sample (Distribution.uniform Bool)
        (fun b => TypedSystem.parallelAll (R b)) =
      TypedSystem.sample (Distribution.uniform Bool)
        (fun b => TypedSystem.parallelAll (fun k => α k • R b k)) := by
  rw [TypedConverter.smul_sample]
  simp only [TypedConverter.parallelAll_attach]

/-- The same equation in sampling and family notation, by `cc_normalize`; the draw `b` stays
outside the whole family. -/
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : Bool → ∀ k, TypedSystem (B k)) :
    (⨂ₘ k, α k) • (sample b ←$ 𝒰[Bool]; ∥ k, R b k) =
      (sample b ←$ 𝒰[Bool]; ∥ k, α k • R b k) := by
  cc_normalize

/-- A shared draw is not independent draws. Normalization keeps `b ← U(Bool)` outside `∥` on the
left; when each `α k` fixes `fixedBit b`, the two sides are `sharedBit` and `independentBit`:

```text
sample b ← U(Bool); ∥ k, fixedBit b    ≠    ∥ k, (sample b ← U(Bool); fixedBit b)
```

They differ on `mixedReplies`, the components replying `false` then `true`: mass `0` versus
`1/4`. -/
example (α : ∀ _k : Bool, bitInterface ⟶ bitInterface)
    (hα : ∀ k b, α k • fixedBit b = fixedBit b) :
    (⨂ₘ k, α k) • (sample b ←$ 𝒰[Bool]; ∥ _k : Bool, fixedBit b) ≠
      (∥ k : Bool, sample b ←$ 𝒰[Bool]; α k • fixedBit b) := by
  -- Normalize the assumed equality: the draw is outside `∥` on the left, inside on the right.
  intro he
  cc_normalize at he
  guard_hyp he : (sample b ←$ 𝒰[Bool]; ∥ k : Bool, α k • fixedBit b) =
    (∥ k : Bool, sample b ←$ 𝒰[Bool]; α k • fixedBit b)
  -- `α k • fixedBit b = fixedBit b` gives `sharedBit = independentBit`; compare their masses
  -- `0` and `1/4` on `mixedReplies`.
  simp only [hα] at he
  change sharedBit = independentBit at he
  have hm := congrArg (fun R : TypedSystem (⨂ _k : Bool, bitInterface) => R.1 mixedReplies) he
  rw [sharedBit_mixedReplies_eq_zero, independentBit_mixedReplies_eq_quarter] at hm
  norm_num at hm

-- Diagnostic: one rewrite by the retained-sample law `TypedConverter.smul_sample`, no choice.
/--
trace: [Meta.Tactic.simp.rewrite] TypedConverter.smul_sample:1000:
      α • TypedSystem.sample (Distribution.uniform Bool) R
    ==>
      TypedSystem.sample (Distribution.uniform Bool) fun k => α • R k
[Meta.Tactic.simp.rewrite] eq_self:1000:
      (TypedSystem.sample (Distribution.uniform Bool) fun k => α • R k) =
        TypedSystem.sample (Distribution.uniform Bool) fun k => α • R k
    ==>
      True
-/
#guard_msgs (whitespace := lax) in
example {A B : Interface} (α : TypedConverter A B) (R : Bool → TypedSystem B) :
    α • TypedSystem.sample (Distribution.uniform Bool) R =
      TypedSystem.sample (Distribution.uniform Bool) (fun b => α • R b) := by
  cc_normalize?

-- Diagnostic: family locality `TypedConverter.parallelAll_attach` is its own registered rule.
/--
trace: [Meta.Tactic.simp.rewrite] TypedConverter.parallelAll_attach:1000:
      (⨂ₘ (k : K), α k) • ∥ (k : K), R k
    ==>
      ∥ (k : K), α k • R k
[Meta.Tactic.simp.rewrite] eq_self:1000:
      (∥ (k : K), α k • R k) = ∥ (k : K), α k • R k
    ==>
      True
-/
#guard_msgs (whitespace := lax) in
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : ∀ k, TypedSystem (B k)) :
    (⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k) := by
  cc_normalize?

-- Diagnostic after `cc_construct`: `attach_eq_typed_smul` turns the attachment field into the
-- typed action, `smul_sample` enters the draw, `smul_eq_typed_smul` retypes `α • R s`.
/--
trace: [Meta.Tactic.simp.rewrite] Interface.attach_eq_typed_smul:100:
      ConstructiveCryptography.ResourceTheory.attach α (TypedSystem.sample (↑P) R)
    ==>
      (have this := α;
        this) •
        TypedSystem.sample (↑P) R
[Meta.Tactic.simp.rewrite] TypedConverter.smul_sample:1000:
      α • TypedSystem.sample (↑P) R
    ==>
      TypedSystem.sample ↑P fun k => α • R k
[Meta.Tactic.simp.rewrite] Interface.smul_eq_typed_smul:100:
      α • R s
    ==>
      (have this := α;
        this) •
        R s
[Meta.Tactic.simp.rewrite] eq_self:1000:
      (TypedSystem.sample ↑P fun k => α • R k) = TypedSystem.sample ↑P fun k => α • R k
    ==>
      True
-/
#guard_msgs (whitespace := lax) in
example {A B : Interface} {S : Type} (α : A ⟶ B) (P : Distribution.ProbDist S)
    (R : S → TypedSystem B) :
    {TypedSystem.sample P.1 R} —[α]→ {TypedSystem.sample P.1 (fun s => α • R s)} := by
  cc_construct
  cc_normalize?

end SystemAlgebra.Tests.ProofErgonomics
