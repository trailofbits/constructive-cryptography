/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems

/-!
# The tower at one carrier

One `Φ`, one `Σ`, every join stated as an `example`: the paper's "let `Φ` be
a set of resources" held fixed across all sections, made mechanical.  Each
example is a theorem of some abstract module landing on the one concrete
carrier through instance resolution alone — no glue, no bridge.  If a
refactor disconnects a layer, this file stops compiling.

Throughout:

* `Φ := PDS (P × X) Y` — the middle layer's resources: interface address in
  the input (Jost Def 2.2.1, LiuZhang §3.3.2).
* `Σ := FreeMonoid (P × DDC X Y X Y)` — words of converter-connection
  pairs, acting by CR18 Definition 3.13 attachment.

The commented section at the end is the honest frontier: joins whose
abstract side exists but whose carrier instance has not landed yet.
-/

namespace RandomSystemsReceipts

open RandomSystems AbstractCryptography
open Probability (Distribution)
open scoped ENNReal

universe u v z

variable {P : Type u} [DecidableEq P] {X : Type z} {Y : Type v}

/-- The one carrier. -/
local notation "Φ" => PDS (P × X) Y

/-- The one converter monoid. -/
local notation "Σc" => FreeMonoid (P × Converter.DDC X Y X Y)

/-! ## 1. The action (MauRen16 §3.3) -/

noncomputable example : MulAction Σc Φ := inferInstance

/-- `id ∈ Σ` is idle at every interface. -/
example (i : P) (S : Φ) :
    Converter.attachFamily i (Converter.idDDC (X := X) (Y := Y)) • S = S :=
  Converter.attachFamily_idDDC_smul i S

/-! ## 2. Specifications and constructions (MauRen16 §2.3, §4.1) -/

example (π : Σc) (R S : Specification Φ) : Prop := Constructs π R S

/-- Lemma 1: constructions compose. -/
example {π π' : Σc} {R S T : Specification Φ}
    (h : Constructs π R S) (h' : Constructs π' S T) :
    Constructs (π' * π) R T :=
  h.trans h'

/-! ## 3. Order invariance and grouping (MauRen16 §3.3, §7; LiuZhang fn. 1)

Order invariance is §3.3's `(αR)β = α(Rβ)`; the grouping into interface sets
is §7. -/

/-- The one axiom the abstract layer asks of the attachment family,
discharged. -/
example : PairwiseOrderInvariant Φ
    (Converter.attachFamily (P := P) (X := X) (Y := Y)) :=
  Converter.pairwiseOrderInvariant_attach

/-- Any corruption split yields an order-invariant honest/dishonest pair. -/
example {Z₁ Z₂ : Set P} (h : Disjoint Z₁ Z₂) :
    OrderInvariant Φ
      (attachedWithin (Converter.attachFamily (X := X) (Y := Y)) Z₁).subtype
      (attachedWithin (Converter.attachFamily (X := X) (Y := Y)) Z₂).subtype :=
  orderInvariant_attachedWithin _ Converter.pairwiseOrderInvariant_attach h

/-! ## 4. Blocking (MauRen16 §3.4) -/

/-- Every resource of this carrier is right-outbound at single-interface
blocking: `⊣` behind an interface silences any converter there. -/
example (i : P) (S : Φ) :
    RightOutbound
      ((attachedWithin
        (Converter.attachFamily (P := P) (X := X) (Y := Y)) {i}).subtype)
      ⟨Converter.attachFamily i Converter.blkDDC,
        Converter.blkDDC_mem_attachedWithin i⟩ S :=
  Converter.rightOutbound_attach i S

/-- Lemma 4: constructions survive the `𝓡⟦` relaxation, from order
invariance alone. -/
example {Z₁ Z₂ : Set P} (hZ : Disjoint Z₁ Z₂)
    (blk : ↥(attachedWithin (Converter.attachFamily (X := X) (Y := Y)) Z₂))
    {π : ↥(attachedWithin (Converter.attachFamily (X := X) (Y := Y)) Z₁)}
    {𝓡 𝒮 : Specification Φ}
    (h : Constructs
      ((attachedWithin (Converter.attachFamily (X := X) (Y := Y)) Z₁).subtype π)
      𝓡 𝒮) :
    Constructs
      ((attachedWithin (Converter.attachFamily (X := X) (Y := Y)) Z₁).subtype π)
      (outboundCompatible
        (attachedWithin (Converter.attachFamily (X := X) (Y := Y)) Z₂).subtype
        blk 𝓡)
      (outboundCompatible
        (attachedWithin (Converter.attachFamily (X := X) (Y := Y)) Z₂).subtype
        blk 𝒮) :=
  Constructs.outboundCompatible _ blk
    (orderInvariant_attachedWithin _ Converter.pairwiseOrderInvariant_attach hZ)
    h

/-- Impossibility statements are stateable, with their antitonicity. -/
example {Γ : Set Σc} {𝓡 𝓡' 𝒮 𝒮' : Specification Φ}
    (h𝓡 : 𝓡 ⊆ 𝓡') (h𝒮 : 𝒮' ⊆ 𝒮) (h : Unconstructible Γ 𝓡 𝒮) :
    Unconstructible Γ 𝓡' 𝒮' :=
  h.anti h𝓡 h𝒮

/-! ## 5. The distance (MauRen16 §2.3, Def 2, fn. 9)

`maxEDist` is fn. 9's `d` on the carrier, and Def 2's non-expansion is a
theorem — for `ProtocolFn`-application.  The joins below are proven at the
level of the facts; the `PseudoEMetricSpace`/`IsNonexpandingSMul` instance
packaging (and with it Lemmas 1–2 and Lemma 5 on this carrier) waits on the
terminology review and the attachment-absorption theorem.  This is the
honest frontier. -/

/-- The distance exists on the carrier, with the pseudo-metric facts. -/
noncomputable example (S T : Φ) : ℝ≥0∞ := PDS.maxEDist S T

example (S T U : Φ) :
    PDS.maxEDist S U ≤ PDS.maxEDist S T + PDS.maxEDist T U :=
  PDS.maxEDist_triangle S T U

/-- Def 2's non-expansion, derived, for deterministic converter
application. -/
example (α : {α : Converter.ProtocolFn (P × X) Y (P × X) Y // Converter.IsDDC α})
    (S T : Φ) :
    PDS.maxEDist (PDS.applyLaw (Converter.toDDC α.val) S)
        (PDS.applyLaw (Converter.toDDC α.val) T) ≤ PDS.maxEDist S T :=
  PDS.maxEDist_applyLaw_le α S T

-- FRONTIER (do not delete; these are the joins that do not fire yet):
--
-- * `PseudoEMetricSpace Φ` with `edist := maxEDist`, and
--   `IsNonexpandingSMul Σc Φ` for the CONNECTION action — needs the
--   absorption of `attachAt` into a strict test (the remaining hard
--   theorem).  With it:
--
--     example : PseudoEMetricSpace Φ := inferInstance
--     example : IsNonexpandingSMul Σc Φ := inferInstance
--
-- * Lemmas 1–2 on this carrier (`Constructs.epsilonRelaxation_trans`, which
--   is JM20 Corollary 1.1 item 1 = MR16 Lemma 1 composed with Lemma 2) and
--   Lemma 5 (`star_construct_eps`) — both fire the moment the two
--   instances above exist; their abstract sides are proven and their
--   `ActCommute` hypotheses are supplied by `actCommute_of_disjoint`.

end RandomSystemsReceipts
