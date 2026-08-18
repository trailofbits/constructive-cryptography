/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Specification.Basic
import AbstractCryptography.Algebra.Attachment

/-!
# Specifications under parallel composition

JM20 Theorem 1.2 / Proposition 2.2 and MauRen11 Definition 7 (ii)–(iii).
Everything here additionally needs `Par` (MauRen11 §3, `Refinement.Basic`)
and `SMulParClass` (MauRen11 §6.2, `CryptographicAlgebra`).
-/

namespace AbstractCryptography

universe u v w

open Pointwise

variable {Sigma Φ : Type*}

section Constructs

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- Parallel composition of specifications, pointwise — JM20's `[ℛ, 𝒯]`
notation (§2.2), MauRen11 §5.1's `‖`. -/
instance [Par Φ] : Par (Specification Φ) where
  par R S := Set.image2 (· ∥ ·) R S

theorem mem_par_iff [Par Φ] {R S : Specification Φ} {x : Φ} :
    x ∈ R ∥ S ↔ ∃ r ∈ R, ∃ s ∈ S, r ∥ s = x := Set.mem_image2

theorem par_mem_par [Par Φ] {R S : Specification Φ} {r s : Φ} (hr : r ∈ R) (hs : s ∈ S) :
    r ∥ s ∈ R ∥ S := Set.mem_image2_of_mem hr hs

/-- The parallel composition of two singleton specifications is the singleton
of the parallel composite. -/
@[simp] theorem singleton_par_singleton [Par Φ] (R S : Φ) :
    ({R} : Specification Φ) ∥ ({S} : Specification Φ) = ({R ∥ S} : Specification Φ) := by
  ext x
  simp only [mem_par_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨r, rfl, s, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨R, rfl, S, rfl, rfl⟩

/-- MauRen11 §6.2's parallel converter composition, `(α|β)ⁱ(R‖S) := αⁱR ‖ βⁱS`,
holds of specifications whenever it holds of resources: both sides are the
pointwise image of the resource-level law. -/
instance [Par Φ] [Par Sigma] [SMulParClass Sigma Φ] : SMulParClass Sigma (Specification Φ) where
  smul_par α β R S := by
    ext x
    constructor
    · rintro ⟨y, ⟨r, hr, s, hs, rfl⟩, rfl⟩
      show (α ∥ β) • (r ∥ s) ∈ α • R ∥ β • S
      rw [smul_par]
      exact par_mem_par (Set.smul_mem_smul_set hr) (Set.smul_mem_smul_set hs)
    · rintro ⟨a, ⟨r, hr, rfl⟩, b, ⟨s, hs, rfl⟩, rfl⟩
      show (α • r) ∥ (β • s) ∈ (α ∥ β) • (R ∥ S)
      rw [← smul_par]
      exact Set.smul_mem_smul_set (par_mem_par hr hs)

/-- JM20 §2.2, **Theorem 1.2**: "`ℛ —π→ 𝒮 ⟹ [ℛ, 𝒯] —π→ [𝒮, 𝒯]`".

The paper carries the **same** `π` across the arrow, because in the concrete
interface model `π` attached to `[ℛ, 𝒯]` acts only on `ℛ`'s interfaces.  In
the monoid-action model the extension is written `π ∥ 1`. -/
instance [Par Φ] [Par Sigma] [SMulParClass Sigma Φ] : IsContextInsensitive (Specification Φ) Sigma where
  red_par_one {R S π} T h := by
    rintro x ⟨y, ⟨r, hr, t, ht, rfl⟩, rfl⟩
    simp only [smul_par, one_smul]
    exact par_mem_par (h (Set.smul_mem_smul_set hr)) ht
  red_one_par {R S π} T h := by
    rintro x ⟨y, ⟨t, ht, r, hr, rfl⟩, rfl⟩
    simp only [smul_par, one_smul]
    exact par_mem_par ht (h (Set.smul_mem_smul_set hr))

/-- MauRen11 Definition 7(iii), first context-insensitivity law: a construction
in the left parallel component remains valid with an unchanged right context.
The constructor is extended explicitly by `∥ 1`. -/
@[crypto_rule "ac.constructs.context" ac_spec_construction abstract_crypto]
theorem Constructs.par_left [Par Φ] [Par Sigma] [SMulParClass Sigma Φ]
    {π : Sigma} {R S : Specification Φ} (T : Specification Φ) (h : R —[π]→ S) :
    R ∥ T —[π ∥ (1 : Sigma)]→ S ∥ T :=
  red_par_one T h

/-- `Constructs.par_left` for singleton specifications. -/
theorem Constructs.par_left_resource [Par Φ] [Par Sigma] [SMulParClass Sigma Φ]
    {π : Sigma} {R S : Φ} (T : Φ)
    (h : ({R} : Specification Φ) —[π]→ ({S} : Specification Φ)) :
    ({R ∥ T} : Specification Φ) —[π ∥ (1 : Sigma)]→ ({S ∥ T} : Specification Φ) := by
  simpa only [singleton_par_singleton] using h.par_left ({T} : Specification Φ)

/-- Specifications are generally composable (MauRen11 Definition 7), hence
`red_par` and
`soundForDerivedChainStepwiseRefinement_of_isGenerallyComposable` apply. -/
instance [Par Φ] [Par Sigma] [SMulParClass Sigma Φ] : IsGenerallyComposable (Specification Φ) Sigma where

end Constructs

section Simulator

variable [Monoid Sigma] [MulAction Sigma Φ]

/-- JM20 §2.2, **Proposition 2.2**: "`ℛ —π→ σ𝒮 ⟹ [ℛ, 𝒯] —π→ σ[𝒮, 𝒯]`".

"*Proof.* The second property follows from Theorem 1 and Proposition 1 as
well: `π[ℛ, 𝒯] = [πℛ, 𝒯] ⊆ [σ𝒮, 𝒯] = σ[𝒮, 𝒯]`."

As with Theorem 1.2, the extensions the paper leaves implicit are written
out: `π ∥ 1` and `σ ∥ 1`. -/
theorem Constructs.simulator_par {π σ : Sigma} {R S : Specification Φ} (T : Specification Φ)
    [Par Φ] [Par Sigma] [SMulParClass Sigma Φ]
    (h : R —[π]→ σ • S) : R ∥ T —[π ∥ 1]→ (σ ∥ 1) • (S ∥ T) := by
  intro x hx
  obtain ⟨y, hy, t, ht, rfl⟩ := Constructs.par_left T h hx
  obtain ⟨s, hs, rfl⟩ := hy
  exact ⟨s ∥ t, par_mem_par hs ht, by simp only [smul_par, one_smul]⟩

end Simulator

end AbstractCryptography
