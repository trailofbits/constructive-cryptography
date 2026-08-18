/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ParFace

/-!
# The cascade and output-combine laws (CR18 Definitions 3.11/3.12, lifted)

A PDS is a random variable over deterministic systems, so the two CR18 §3.4
composition operators lift by pushforward along the deterministic operator, in
exactly the shape `PDS.parLaw` already uses for parallel composition: the
independent product of the component laws, pushed along `System.cascade`
resp. `System.combine`.  The probabilistic layer adds no operation of its own.

These are **objects and support facts only**.  `cascade`/`combine` are
classified §PARTIAL-ONLY in the ledger, so no metric statement (`Adv⊥`,
`edist`) may be built on either law here; that needs the A6-style migration
first.

The support lemmas are the `PDS.faceT` idiom (`System/ParFace.lean`): the
face of a composite law is bounded by the faces of its components, because
each deterministic composite accepts only histories its components accept.
-/

namespace RandomSystems

open Probability (Distribution)

universe u v w

namespace System

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The cascade accepts only histories the left system accepts, so its
interface set sits inside the left system's. -/
theorem support_cascade_subset (S : DDS X Y) (T : DDS Y Z) :
    support (cascade S T) ⊆ support S := by
  rintro q ⟨l, hl, hq⟩
  exact ⟨l, hl.choose, hq⟩

/-- The output-combine accepts only histories both systems accept, so its
interface set sits inside both components'. -/
theorem support_combine_subset (op : Y → Y → Y) (S T : DDS X Y) :
    support (combine op S T) ⊆ support S ∩ support T := by
  rintro q ⟨l, hl, hq⟩
  exact ⟨⟨l, hl.1, hq⟩, ⟨l, hl.2, hq⟩⟩

end System

namespace PDS

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The law of `S ⊲ₚ T`: the independent product of the component laws, pushed
forward along the deterministic cascade (CR18 Definition 3.11). -/
noncomputable def cascadeLaw (S : PDS X Y) (T : PDS Y Z) : PDS X Z :=
  Distribution.fTransform
    (fun p : System.DDS X Y × System.DDS Y Z => System.cascade p.1 p.2)
    (Distribution.prod S T)

/-- The law of `S ⋆ₚ[op] T`: the independent product of the component laws,
pushed forward along the deterministic output-combine (CR18 Definition
3.12). -/
noncomputable def combineLaw (op : Y → Y → Y) (S T : PDS X Y) : PDS X Y :=
  Distribution.fTransform
    (fun p : System.DDS X Y × System.DDS X Y => System.combine op p.1 p.2)
    (Distribution.prod S T)

/-- Every behaviour of the cascade law is a cascade of component
behaviours. -/
theorem mem_support_cascadeLaw {S : PDS X Y} {T : PDS Y Z}
    {C : System.DDS X Z} (hC : C ∈ (cascadeLaw S T).support) :
    ∃ A ∈ S.support, ∃ B ∈ T.support, System.cascade A B = C := by
  obtain ⟨p, hp, rfl⟩ := Distribution.mem_support_fTransform _ _ hC
  have hmem := Distribution.support_prod_subset S T hp
  rw [Finset.mem_product] at hmem
  exact ⟨p.1, hmem.1, p.2, hmem.2, rfl⟩

/-- Every behaviour of the output-combine law is a combine of component
behaviours. -/
theorem mem_support_combineLaw {op : Y → Y → Y} {S T : PDS X Y}
    {C : System.DDS X Y} (hC : C ∈ (combineLaw op S T).support) :
    ∃ A ∈ S.support, ∃ B ∈ T.support, System.combine op A B = C := by
  obtain ⟨p, hp, rfl⟩ := Distribution.mem_support_fTransform _ _ hC
  have hmem := Distribution.support_prod_subset S T hp
  rw [Finset.mem_product] at hmem
  exact ⟨p.1, hmem.1, p.2, hmem.2, rfl⟩

/-- **The face of a cascade law** sits inside the face of its left factor:
the cascade can only ever be asked what the left system can be asked. -/
theorem faceT_cascadeLaw_subset (S : PDS X Y) (T : PDS Y Z) :
    faceT (cascadeLaw S T) ⊆ faceT S := by
  intro q hq
  obtain ⟨C, hC, hqC⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨A, hA, B, hB, rfl⟩ := mem_support_cascadeLaw hC
  exact subset_faceT hA (System.support_cascade_subset A B hqC)

/-- **The face of an output-combine law** sits inside both components'
faces: the combination is defined only where both components are. -/
theorem faceT_combineLaw_subset (op : Y → Y → Y) (S T : PDS X Y) :
    faceT (combineLaw op S T) ⊆ faceT S ∩ faceT T := by
  intro q hq
  obtain ⟨C, hC, hqC⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨A, hA, B, hB, rfl⟩ := mem_support_combineLaw hC
  obtain ⟨hqA, hqB⟩ := System.support_combine_subset op A B hqC
  exact ⟨subset_faceT hA hqA, subset_faceT hB hqB⟩

end PDS

end RandomSystems
