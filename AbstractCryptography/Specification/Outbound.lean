/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Specification.Basic

/-!
# Blocking and right-outbound specifications (MR16 §3.4)

One converter monoid `Sigma` acting on `Φ`; attachment at an interface is a
monoid homomorphism `Sigma' →* Sigma`.  Everything here is stated for an
arbitrary pair of attachment homs `eL eR` with `OrderInvariant` — MR16 §3.3's
law `(αR)β = α(Rβ)` as an equation of the *actions*, stated as a hypothesis
and never in the monoid: the instantiation's converter monoid is free, and
distinct words never commute.  MR16's two-interface setting is the case of
one hom per side; the many-party setting (MR16 §7, LiuZhang Ch. 4) supplies,
per dishonest set, the honest and dishonest attachment homs — grouped
products of an interface-indexed family, pairwise order-invariant because
disjoint index sets commute elementwise.

On this setting, MR16 §3.4's blocking relaxations:

* `⊣` is a distinguished converter `blk` attached at the right; no axioms on
  it are needed for the lemmas below.
* `RightOutbound R`: "no converter attached at the right interface can have
  an effect at the left interface, i.e., `R*⊣ = R⊣`".
* `blocked 𝓡` is `𝓡⊣`.
* `outboundCompatible 𝓡` is `𝓡⟦`, "the set of right-outbound resources `S`
  compatible with (a resource in) `𝓡` (only) at the left interface:
  `𝓡⟦ := {S | S is right-outbound and S⊣ ∈ 𝓡⊣}`".
* `Unconstructible` is §2.1's `𝓡 ↛ 𝒮`.

MR16 eq. (2) claims `𝓡 ⊆ 𝓡⟦ = (𝓡⟦)⟦`.  The equality is a theorem
(`outboundCompatible_idem`); the inclusion holds exactly when every resource
of `𝓡` is right-outbound (`subset_outboundCompatible_iff`), which is the
paper's implicit standing assumption at its use sites.
-/

namespace AbstractCryptography

open Pointwise

variable {SigmaL SigmaR Sigma Φ : Type*} [Monoid SigmaL] [Monoid SigmaR] [Monoid Sigma]
variable [MulAction Sigma Φ]

/-- MR16 §3.3's `(αR)β = α(Rβ)` for attachment homs `eL`, `eR` — LiuZhang
§3.3.2's *composition order invariance*, as an equation of the actions. -/
def OrderInvariant (Φ : Type*)
    (eL : SigmaL →* Sigma) (eR : SigmaR →* Sigma) [MulAction Sigma Φ] : Prop :=
  ∀ (α : SigmaL) (β : SigmaR) (R : Φ), eL α • eR β • R = eR β • eL α • R

variable (eR : SigmaR →* Sigma) (blk : SigmaR)

/-- MR16 §3.4: `R` is *right-outbound* "if no converter attached at the right
interface can have an effect at the left interface, i.e., if `R*⊣ = R⊣`". -/
def RightOutbound (R : Φ) : Prop :=
  ∀ β : SigmaR, eR blk • eR β • R = eR blk • R

/-- `𝓡⊣`: the right interface of every resource of `𝓡` shut by `⊣`. -/
def blocked (𝓡 : Specification Φ) : Specification Φ :=
  eR blk • 𝓡

/-- MR16 §3.4: `𝓡⟦`, "the set of right-outbound resources `S` compatible
with (a resource in) `𝓡` (only) at the left interface". -/
def outboundCompatible (𝓡 : Specification Φ) : Specification Φ :=
  {S | RightOutbound eR blk S ∧ eR blk • S ∈ blocked eR blk 𝓡}

/-- The second half of MR16 eq. (2): `(𝓡⟦)⟦ = 𝓡⟦`. -/
theorem outboundCompatible_idem (𝓡 : Specification Φ) :
    outboundCompatible eR blk (outboundCompatible eR blk 𝓡) =
      outboundCompatible eR blk 𝓡 := by
  ext S
  constructor
  · rintro ⟨hout, hmem⟩
    obtain ⟨T, ⟨-, hTmem⟩, hTS⟩ := hmem
    exact ⟨hout, hTS ▸ hTmem⟩
  · rintro ⟨hout, hmem⟩
    exact ⟨hout, Set.smul_mem_smul_set ⟨hout, hmem⟩⟩

/-- The first half of MR16 eq. (2), sharpened: `𝓡 ⊆ 𝓡⟦` holds exactly when
every resource of `𝓡` is right-outbound. -/
theorem subset_outboundCompatible_iff (𝓡 : Specification Φ) :
    𝓡 ⊆ outboundCompatible eR blk 𝓡 ↔ ∀ R ∈ 𝓡, RightOutbound eR blk R := by
  constructor
  · exact fun h R hR => (h hR).1
  · exact fun h R hR => ⟨h R hR, Set.smul_mem_smul_set hR⟩

/-- MR16 §4.1, **Lemma 4**: `𝓡 —π→ 𝒮 ⟹ 𝓡⟦ —π→ 𝒮⟦`, for a protocol
attached at the left.  The only input is order invariance. -/
theorem Constructs.outboundCompatible {eL : SigmaL →* Sigma}
    (hoi : OrderInvariant Φ eL eR) {π : SigmaL} {𝓡 𝒮 : Specification Φ}
    (h : Constructs (eL π) 𝓡 𝒮) :
    Constructs (eL π)
      (AbstractCryptography.outboundCompatible eR blk 𝓡)
      (AbstractCryptography.outboundCompatible eR blk 𝒮) := by
  rintro x hx
  obtain ⟨S, ⟨hout, hcomp⟩, rfl⟩ := hx
  obtain ⟨R, hR, hbR⟩ := hcomp
  have hbR' : eR blk • R = eR blk • S := hbR
  refine ⟨fun β => ?_, ?_⟩
  · calc eR blk • eR β • eL π • S
        = eR blk • eL π • eR β • S := by rw [hoi π β]
      _ = eL π • eR blk • eR β • S := by rw [hoi π blk]
      _ = eL π • eR blk • S := by rw [hout β]
      _ = eR blk • eL π • S := by rw [hoi π blk]
  · have key : eR blk • eL π • S = eR blk • eL π • R := by
      calc eR blk • eL π • S
          = eL π • eR blk • S := by rw [hoi π blk]
        _ = eL π • eR blk • R := by rw [hbR']
        _ = eR blk • eL π • R := by rw [hoi π blk]
    exact key ▸ Set.smul_mem_smul_set (h (Set.smul_mem_smul_set hR))

/-- MR16 §2.1: `𝓡 ↛ 𝒮` — no constructor in the admitted set `Γ` constructs
`𝒮` from `𝓡`. -/
def Unconstructible (Γ : Set Sigma) (𝓡 𝒮 : Specification Φ) : Prop :=
  ¬ ∃ π ∈ Γ, Constructs π 𝓡 𝒮

/-- MR16 §2.3: "the smaller `𝓡` or the larger `𝒮`, the stronger the
impossibility statement" — `𝓡 ↛ 𝒮 ⟹ 𝓡' ↛ 𝒮'` for `𝓡 ⊆ 𝓡'`, `𝒮' ⊆ 𝒮`. -/
theorem Unconstructible.anti {Γ : Set Sigma} {𝓡 𝓡' 𝒮 𝒮' : Specification Φ}
    (h𝓡 : 𝓡 ⊆ 𝓡') (h𝒮 : 𝒮' ⊆ 𝒮) (h : Unconstructible Γ 𝓡 𝒮) :
    Unconstructible Γ 𝓡' 𝒮' :=
  fun ⟨π, hπ, hc⟩ => h ⟨π, hπ, hc.mono h𝓡 h𝒮⟩

end AbstractCryptography
