/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ConstructiveCryptography.Categorical.ResourceAlgebra.Star

set_option autoImplicit false

/-!
# Blocking and right-outbound specifications

This module states Maurer--Renner's right-interface specialization using
ordinary endomorphism converters and the one categorical attachment operation.
Commutation of converters acting at disjoint interfaces is an explicit theorem
hypothesis; it is not a field of `ResourceAlgebra`.

Jost's basic construction theory does not require the outbound specialization.
It supports this optional layer through addressed interfaces and its locality
law: converters attached at disjoint interfaces commute after their connection
into the common boundary.
-/

namespace ConstructiveCryptography.Categorical.ResourceAlgebra.Specification

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A resource is right-outbound when blocking the selected right interface
absorbs every admitted converter at that interface.

Maurer--Renner 2016, Section 3.4 (printed p. 8): a resource is right-outbound
if “no converter attached at the right interface can have an effect at the
left interface, i.e., if `R*⊣ = R⊣`.” -/
def RightOutbound {A : C} (converters : EndoFamily (Opposite.op A))
    (block : CategoryTheory.End A) (resource : Resource Phi A) : Prop :=
  ∀ converter : CategoryTheory.End A, converter.op ∈ converters →
    attach (Phi := Phi) block
        (attach (Phi := Phi) converter resource) =
      attach (Phi := Phi) block resource

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Apply the blocking converter to every resource in a specification. -/
def blocked {A : C} (block : CategoryTheory.End A)
    (source : Specification Phi A) : Specification Phi A :=
  map (Phi := Phi) block source

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Right-outbound resources compatible with a specification after blocking.

Maurer--Renner 2016, Section 3.4 (printed p. 8):
“`R⟦ := {S | S is right-outbound and S⊣ ∈ R⊣}`.” -/
def outboundCompatible {A : C}
    (converters : EndoFamily (Opposite.op A))
    (block : CategoryTheory.End A) (source : Specification Phi A) :
    Specification Phi A :=
  {resource | RightOutbound (Phi := Phi) converters block resource ∧
    attach (Phi := Phi) block resource ∈ blocked (Phi := Phi) block source}

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- The right-outbound compatibility operation is idempotent. -/
theorem outboundCompatible_idem {A : C}
    (converters : EndoFamily (Opposite.op A))
    (block : CategoryTheory.End A) (source : Specification Phi A) :
    outboundCompatible (Phi := Phi) converters block
        (outboundCompatible (Phi := Phi) converters block source) =
      outboundCompatible (Phi := Phi) converters block source := by
  ext resource
  constructor
  · rintro ⟨outbound, blockedMember⟩
    -- The outer blocked witness comes from an already compatible resource.
    rcases blockedMember with
      ⟨middle, ⟨-, middleBlocked⟩, middleEquation⟩
    -- Substitute its blocked equality into the original blocked membership.
    exact ⟨outbound, middleEquation ▸ middleBlocked⟩
  · intro compatible
    -- The resource itself witnesses blocked membership in the compatible set.
    exact ⟨compatible.1,
      ⟨resource, compatible, rfl⟩⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- A specification is contained in its right-outbound compatibility set
exactly when every admitted resource is right-outbound. -/
theorem subset_outboundCompatible_iff {A : C}
    (converters : EndoFamily (Opposite.op A))
    (block : CategoryTheory.End A) (source : Specification Phi A) :
    source ⊆ outboundCompatible (Phi := Phi) converters block source ↔
      ∀ resource ∈ source,
        RightOutbound (Phi := Phi) converters block resource := by
  constructor
  · intro included resource admitted
    -- Read right-outboundness from compatibility membership.
    exact (included admitted).1
  · intro outbound resource admitted
    -- The resource itself witnesses equality of the two blocked forms.
    exact ⟨outbound resource admitted,
      ⟨resource, admitted, rfl⟩⟩

omit [MonoidalCategory C] [ResourceAlgebra C Phi] in
/-- Right-outbound compatibility is preserved by a construction whose
converter commutes with the right-interface class and the blocking converter.

Maurer--Renner 2016, Lemma 4 (printed p. 12):
“`R —π→ S  ⟹  R⟦ —π→ S⟦`.” -/
theorem Constructs.outboundCompatible {A : C}
    {converter block : CategoryTheory.End A}
    {converters : EndoFamily (Opposite.op A)}
    (commutes : ∀ rightConverter : CategoryTheory.End A,
      rightConverter.op ∈ converters →
        converter ≫ rightConverter = rightConverter ≫ converter)
    (commutesBlock : converter ≫ block = block ≫ converter)
    {source target : Specification Phi A}
    (construction : Constructs (Phi := Phi) converter source target) :
    Constructs (Phi := Phi) converter
      (outboundCompatible (Phi := Phi) converters block source)
      (outboundCompatible (Phi := Phi) converters block target) := by
  rw [constructs_iff] at construction ⊢
  have attach_commute (left right : CategoryTheory.End A)
      (equal : left ≫ right = right ≫ left) (resource : Resource Phi A) :
      attach (Phi := Phi) left (attach (Phi := Phi) right resource) =
        attach (Phi := Phi) right (attach (Phi := Phi) left resource) := by
    -- Serial attachment turns converter commutation into function commutation.
    rw [← attach_serial, ← attach_serial, equal]
  intro resource compatible
  rcases compatible with ⟨outbound, blockedMember⟩
  constructor
  · intro rightConverter rightAdmitted
    -- Commute the honest converter past the right converter and the block.
    calc
      attach (Phi := Phi) block
          (attach (Phi := Phi) rightConverter
            (attach (Phi := Phi) converter resource)) =
          attach (Phi := Phi) block
            (attach (Phi := Phi) converter
              (attach (Phi := Phi) rightConverter resource)) := by
            exact congrArg (attach (Phi := Phi) block)
              (attach_commute converter rightConverter
                (commutes rightConverter rightAdmitted) resource).symm
      _ = attach (Phi := Phi) converter
            (attach (Phi := Phi) block
              (attach (Phi := Phi) rightConverter resource)) := by
            exact (attach_commute converter block commutesBlock
              (attach (Phi := Phi) rightConverter resource)).symm
      _ = attach (Phi := Phi) converter
            (attach (Phi := Phi) block resource) := by
            rw [outbound rightConverter rightAdmitted]
      _ = attach (Phi := Phi) block
            (attach (Phi := Phi) converter resource) := by
            exact attach_commute converter block commutesBlock resource
  · -- Choose the source resource whose blocked form agrees with this one.
    rcases blockedMember with
      ⟨sourceResource, sourceAdmitted, blockedEquation⟩
    change attach (Phi := Phi) block sourceResource =
      attach (Phi := Phi) block resource at blockedEquation
    refine ⟨attach (Phi := Phi) converter sourceResource,
      construction sourceResource sourceAdmitted, ?_⟩
    -- Apply the constructing converter to the blocked equality and commute it.
    calc
      attach (Phi := Phi) block
          (attach (Phi := Phi) converter sourceResource) =
          attach (Phi := Phi) converter
            (attach (Phi := Phi) block sourceResource) := by
              exact (attach_commute converter block commutesBlock
                sourceResource).symm
      _ = attach (Phi := Phi) converter
            (attach (Phi := Phi) block resource) := by
              rw [blockedEquation]
      _ = attach (Phi := Phi) block
            (attach (Phi := Phi) converter resource) := by
              exact attach_commute converter block commutesBlock resource

end ConstructiveCryptography.Categorical.ResourceAlgebra.Specification
