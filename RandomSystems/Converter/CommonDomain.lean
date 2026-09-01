/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.CommonDomainEmbedding
import RandomSystems.Converter.RandomSystemAction

set_option autoImplicit false

/-!
# DDC attachment on common-domain random systems

The normalized specialization of Lanzenberger's common-domain carrier embeds
faithfully into the query-indexed random-system carrier. A DDC acts on that
subcarrier exactly when its query-indexed action preserves the embedded image.
Attachment is the unique preimage supplied by injectivity.

Jost separates the axiomatic system algebra from his probabilistic discrete
system presentation and does not require Lanzenberger's common-domain
relation. Liu--Maurer's conditional-probability presentation does not state a
common-domain condition on supported DDSs.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “A converter α, when applied
as an interface i of a resource, induces a function Φ → Φ : R → αⁱR.”
-/

namespace RandomSystems.CommonDomain

noncomputable section

open RandomSystems.Ambient

universe u v

variable {U A X P : Type u} {V B Y Q : Type v}

/-- A DDC whose query-indexed action preserves normalized common-domain random
systems. -/
structure DDC (U : Type u) (V : Type v) (X : Type u) (Y : Type v) where
  ddc : Ambient.DDC
    (Ambient.Interface.single U V)
    (Ambient.Interface.single X Y)
  preserves : ∀ system : ProbabilityRandomSystem X Y,
    ∃ output : ProbabilityRandomSystem U V,
      ProbabilityRandomSystem.toAmbient output =
        Ambient.RandomSystem.applyDDC ddc
          (ProbabilityRandomSystem.toAmbient system)

namespace DDC

@[ext]
theorem ext {left right : DDC U V X Y}
    (equal : left.ddc = right.ddc) : left = right := by
  cases left
  cases right
  cases equal
  rfl

/-- Forwarding as a common-domain-preserving DDC. -/
def forwarding (X : Type u) (Y : Type v) : DDC X Y X Y where
  ddc := Ambient.DDC.forwarding
    (Ambient.Interface.single X Y)
  preserves system := by
    -- The input common-domain resource itself is the output witness.
    refine ⟨system, ?_⟩
    -- Ambient forwarding attachment is the identity.
    rw [Ambient.RandomSystem.applyDDC_forwarding_eq]

/-- Serial composition of common-domain-preserving DDCs. -/
def serial (outer : DDC U V A B) (inner : DDC A B X Y) : DDC U V X Y where
  ddc := Ambient.DDC.serial outer.ddc inner.ddc
  preserves system := by
    -- Inner preservation supplies a common-domain middle resource.
    obtain ⟨middle, middleEqual⟩ := inner.preserves system
    -- Outer preservation supplies the final common-domain resource.
    obtain ⟨output, outputEqual⟩ := outer.preserves middle
    refine ⟨output, ?_⟩
    -- Ambient serial attachment composes the two actions.
    rw [outputEqual, middleEqual,
      Ambient.RandomSystem.applyDDC_serial_eq]

@[simp]
theorem forwarding_serial_eq (converter : DDC U V X Y) :
    serial (forwarding U V) converter = converter := by
  -- Equality reduces to the underlying ambient DDC.
  apply ext
  -- Apply the ambient left-identity law.
  exact Ambient.DDC.forwarding_serial_eq converter.ddc

@[simp]
theorem serial_forwarding_eq (converter : DDC U V X Y) :
    serial converter (forwarding X Y) = converter := by
  -- Equality reduces to the underlying ambient DDC.
  apply ext
  -- Apply the ambient right-identity law.
  exact Ambient.DDC.serial_forwarding_eq converter.ddc

theorem serial_assoc (outer : DDC U V A B) (middle : DDC A B X Y)
    (inner : DDC X Y P Q) :
    serial (serial outer middle) inner =
      serial outer (serial middle inner) := by
  -- Equality reduces to the underlying ambient DDC.
  apply ext
  -- Apply ambient serial associativity.
  exact Ambient.DDC.serial_assoc outer.ddc middle.ddc inner.ddc

end DDC

namespace ProbabilityRandomSystem

/-- Attachment by a common-domain-preserving DDC. -/
noncomputable def apply (converter : DDC U V X Y)
    (system : ProbabilityRandomSystem X Y) : ProbabilityRandomSystem U V :=
  Classical.choose (converter.preserves system)

@[simp]
theorem toAmbient_apply (converter : DDC U V X Y)
    (system : ProbabilityRandomSystem X Y) :
    toAmbient (apply converter system) =
      Ambient.RandomSystem.applyDDC converter.ddc (toAmbient system) :=
  Classical.choose_spec (converter.preserves system)

theorem apply_eq_iff (converter : DDC U V X Y)
    (system : ProbabilityRandomSystem X Y)
    (output : ProbabilityRandomSystem U V) :
    apply converter system = output ↔
      toAmbient output =
        Ambient.RandomSystem.applyDDC converter.ddc (toAmbient system) := by
  constructor
  -- The chosen preimage satisfies the ambient attachment equation.
  · rintro rfl
    exact toAmbient_apply converter system
  -- Injectivity identifies any other output satisfying that equation.
  · intro equal
    apply toAmbient_injective
    exact (toAmbient_apply converter system).trans equal.symm

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), says that the identity
converter “induces the identity function `Φ → Φ`.” -/
@[simp]
theorem apply_forwarding_eq (system : ProbabilityRandomSystem X Y) :
    apply (DDC.forwarding X Y) system = system := by
  -- Compare resources through the injective ambient embedding.
  apply toAmbient_injective
  -- Reduce to ambient forwarding attachment.
  rw [toAmbient_apply]
  change Ambient.RandomSystem.applyDDC
      (Ambient.DDC.forwarding (Ambient.Interface.single X Y))
      (toAmbient system) = toAmbient system
  exact Ambient.RandomSystem.applyDDC_forwarding_eq _

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), states
“`(β ◦ α)ⁱR = βⁱ(αⁱR)`.” -/
theorem apply_serial_eq (outer : DDC U V A B) (inner : DDC A B X Y)
    (system : ProbabilityRandomSystem X Y) :
    apply (DDC.serial outer inner) system =
      apply outer (apply inner system) := by
  -- Compare resources through the injective ambient embedding.
  apply toAmbient_injective
  -- Expose the three ambient attachment terms.
  rw [toAmbient_apply, toAmbient_apply, toAmbient_apply]
  change Ambient.RandomSystem.applyDDC
      (Ambient.DDC.serial outer.ddc inner.ddc)
        (toAmbient system) =
    Ambient.RandomSystem.applyDDC outer.ddc
      (Ambient.RandomSystem.applyDDC inner.ddc (toAmbient system))
  -- Apply ambient serial attachment.
  exact Ambient.RandomSystem.applyDDC_serial_eq
    outer.ddc inner.ddc (toAmbient system)

/-- Maurer--Renner 2016, Definition 2 (printed p. 11), calls a metric
non-expanding when “`d(αR, αS) ≤ d(R, S)` for all `α`.” -/
theorem edist_apply_le (converter : DDC U V X Y)
    (left right : ProbabilityRandomSystem X Y) :
    edist (apply converter left) (apply converter right) ≤
      edist left right := by
  -- Rewrite both distances through the injective ambient embedding.
  rw [edist_eq_edist_toAmbient, edist_eq_edist_toAmbient,
    toAmbient_apply, toAmbient_apply]
  -- Apply ambient DDC non-expansion.
  exact Ambient.RandomSystem.edist_applyDDC_le
    converter.ddc (toAmbient left) (toAmbient right)

end ProbabilityRandomSystem

end


end RandomSystems.CommonDomain
