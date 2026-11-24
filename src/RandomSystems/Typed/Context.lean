module

public import RandomSystems.Typed.ParallelAttachment
public import RandomSystems.Typed.SystemCoherence
public import RandomSystems.Typed.ConverterCoherence
public import RandomSystems.Typed.Functional
public import RandomSystems.Converter.EmptyInterface

/-!
# Fixed contexts and parallel projections

`ofSystem R` presents `R` as a converter with no inside ports. Together with the identity and
unit converters, it builds fixed contexts: `rightContext A S • R = R ∥ S`, and likewise on
the left. `discard B` exposes no ports and never queries `B`; `eq_discard` makes it unique.

Projections use the named converters from `RandomSystems.Typed.Unitors`:

```text
A ── rightUnitorInv A ── A ⊗ unit ── id A ⊗ discard B ── A ⊗ B
B ── leftUnitorInv B  ── unit ⊗ B ── discard A ⊗ id B ── A ⊗ B
```

`projectLeft_smul_parallel` and `projectRight_smul_parallel` return the selected component.
Their `smul_sample_parallel` laws preserve one shared draw: projecting
`sample k ← P; R k ∥ S k` gives `sample k ← P; R k` or `sample k ← P; S k`.
The `comp_parallel` laws commute a converter on the retained side past the projection;
`comp_discard` absorbs the converter on the hidden side. Cancellation and naturality of the
unit converters come from `RandomSystems.Typed.ConverterCoherence`.

## References

1. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis,
   Diss. ETH No. 26723, ETH Zurich, 2020. (§2.2.2 and Proposition 2.2.3, pp. 17–18.)
-/

@[expose] public section

namespace SystemAlgebra

open Probability Interface

variable {A B : Interface}

/-- The unit interface has exactly one typed system. -/
lemma TypedSystem.empty_eq (S : TypedSystem unit) : S = TypedSystem.dummy := by
  apply Subtype.ext
  apply RandomSystem.ext
  rintro (_ | ⟨⟨⟨e, _⟩, _⟩, _⟩)
  · rw [S.1.mass_nil, TypedSystem.dummy.1.mass_nil]
  · exact e.elim

namespace TypedConverter

/-! ## A typed system as a converter with no inside interfaces -/

/-- A typed system as a typed converter with no inside interfaces: the PDC of the DDC readings
of a presentation of the system. -/
noncomputable def ofSystem (R : TypedSystem A) : TypedConverter A unit :=
  PDCBehavior.ofPDC (resourcePDC R.exists_ofPDS.choose)

lemma attach_ofSystem (R : TypedSystem A) (S : TypedSystem unit) :
    (ofSystem R • S : TypedSystem A) = R := by
  rw [TypedSystem.empty_eq S]
  have hQ := R.exists_ofPDS.choose_spec
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [smul_val, PDCBehavior.attach_presents unit.nonempty_prefix
    A.nonempty_prefix (ofSystem R) TypedSystem.dummy.1 TypedSystem.dummy.2
    (resourcePDC R.exists_ofPDS.choose) _ (fun _ => rfl) (fun _ => rfl) h,
    behaviorMass_attachPDS, Distribution.prod_single_right, Distribution.mass_fTransform]
  conv_rhs => rw [← hQ]
  change _ = R.exists_ofPDS.choose.1.mass _
  rw [resourcePDC, Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun s => ?_
  dsimp only
  erw [apply_resourceDDC _ s.2.1.1, s.2.1.trim_eq]

/-! ## Constant converters and fixed contexts -/

/-- The typed converter that attaches to any typed system and exposes no interface. -/
noncomputable def discard (B : Interface) : TypedConverter unit B :=
  ofDDC (discardSystem B.I B.X B.Y) (discardSystem_isDDCFrom B.domain)

/-- Every typed converter with the unit outside interface equals `discard B`: `unit.domain` admits
no outside query, so every nonempty converter transcript has probability zero. -/
lemma eq_discard
    -- `B` is the inside interface; `α` has the empty unit interface outside.
    {B : Interface} (α : TypedConverter unit B) : α = discard B := by
  apply PDCBehavior.ext
  intro t
  rcases List.eq_nil_or_concat t with rfl | ⟨h, ⟨x, y⟩, rfl⟩
  · -- Empty transcripts have probability one in both behaviors.
    rw [α.1.mass_nil, (discard B).1.mass_nil]
  · -- No input is admitted at the empty outside domain, so nonempty transcripts have mass zero.
    rw [List.concat_eq_append,
      α.1.mass_eq_zero_of_not_admitted (fun hd => hd.2.2.1) y,
      (discard B).1.mass_eq_zero_of_not_admitted (fun hd => hd.2.2.1) y]

/-- Discarding the output of any typed converter `β` gives `discard C`. -/
lemma comp_discard
    -- `B` is the discarded intermediate interface; `β` connects `B` to `C`.
    {B C : Interface} (β : TypedConverter B C) :
    comp (discard B) β = discard C :=
  eq_discard _

/-- A constant converter: it ignores its inside system and exposes `R`. No
efficiency claim is made for this unrestricted mathematical converter. -/
noncomputable def constant (R : TypedSystem A) (B : Interface) : TypedConverter A B :=
  comp (ofSystem R) (discard B)

lemma attach_constant (R : TypedSystem A) {B : Interface} (S : TypedSystem B) :
    (constant R B • S : TypedSystem A) = R := by
  rw [constant, comp_smul, attach_ofSystem]

/-- The right unit renaming attached to a typed system puts the dummy system beside it. -/
lemma rightUnitor_hom_attach (R : TypedSystem A) :
    rightUnitorHom A • R = TypedSystem.parallel R TypedSystem.dummy := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [rightUnitorHom, rename_mass, TypedSystem.parallel_unit_right_mass]

/-- The left unit renaming attached to a typed system puts the dummy system beside it. -/
lemma leftUnitor_hom_attach (R : TypedSystem A) :
    leftUnitorHom A • R = TypedSystem.parallel TypedSystem.dummy R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [leftUnitorHom, rename_mass, TypedSystem.parallel_unit_left_mass]

/-- The fixed right context: the identity beside `S` as a converter, followed by the right unit
renaming. -/
noncomputable def rightContext (A : Interface) {B : Interface} (S : TypedSystem B) :
    TypedConverter (tensor A B) A :=
  comp (parallel (TypedConverter.id A) (ofSystem S)) (rightUnitorHom A)

/-- The fixed left context; no symmetry of the selected substitution relation is used. -/
noncomputable def leftContext {A : Interface} (R : TypedSystem A) (B : Interface) :
    TypedConverter (tensor A B) B :=
  comp (parallel (ofSystem R) (TypedConverter.id B)) (leftUnitorHom B)

lemma attach_rightContext (R : TypedSystem A) (S : TypedSystem B) :
    (rightContext A S • R : TypedSystem (tensor A B)) = TypedSystem.parallel R S := by
  rw [rightContext, comp_smul, rightUnitor_hom_attach, parallel_attach, identity_attach,
    attach_ofSystem]

lemma attach_leftContext (R : TypedSystem A) (S : TypedSystem B) :
    (leftContext R B • S : TypedSystem (tensor A B)) = TypedSystem.parallel R S := by
  rw [leftContext, comp_smul, leftUnitor_hom_attach, parallel_attach, identity_attach,
    attach_ofSystem]

/-! ## Projections of parallel resources -/

/-- The inverse right unit renaming drops a right-hand dummy system. -/
lemma rightUnitor_inv_attach
    -- `R` is paired with the empty system on its right.
    (R : TypedSystem A) :
    rightUnitorInv A • TypedSystem.parallel R TypedSystem.dummy = R := by
  calc
    rightUnitorInv A • TypedSystem.parallel R TypedSystem.dummy
        = rightUnitorInv A • (rightUnitorHom A • R) :=
          congrArg (rightUnitorInv A • ·) (rightUnitor_hom_attach R).symm
    _ = comp (rightUnitorInv A) (rightUnitorHom A) • R := (comp_smul _ _ _).symm
    _ = R := by rw [rightUnitorInv_comp_hom, identity_attach]

/-- The inverse left unit renaming drops a left-hand dummy system. -/
lemma leftUnitor_inv_attach
    -- `R` is paired with the empty system on its left.
    (R : TypedSystem A) :
    leftUnitorInv A • TypedSystem.parallel TypedSystem.dummy R = R := by
  calc
    leftUnitorInv A • TypedSystem.parallel TypedSystem.dummy R
        = leftUnitorInv A • (leftUnitorHom A • R) :=
          congrArg (leftUnitorInv A • ·) (leftUnitor_hom_attach R).symm
    _ = comp (leftUnitorInv A) (leftUnitorHom A) • R := (comp_smul _ _ _).symm
    _ = R := by rw [leftUnitorInv_comp_hom, identity_attach]

/-- Left projection of a binary parallel interface: `projectLeft A B : A → A ⊗ B` applies the
inverse right unit renaming outside `id A ⊗ discard B`, forwarding queries on `A` and making
no queries to `B`.

```text
  A ┌───────────────┐ A ⊗ 1 ┌───────────┐ A ⊗ B
────┤ rightUnitor⁻¹ ├───────┤ id A ⊗ ∅  ├───────
    └───────────────┘       └───────────┘
``` -/
noncomputable def projectLeft
    -- `A` is retained; the other parallel interface is hidden.
    (A B : Interface) : TypedConverter A (tensor A B) :=
  comp (rightUnitorInv A) (parallel (TypedConverter.id A) (discard B))

/-- Right projection of a binary parallel interface: `projectRight A B : B → A ⊗ B` applies the
inverse left unit renaming outside `discard A ⊗ id B`, making no queries to `A` and forwarding
queries on `B`.

```text
  B ┌──────────────┐ 1 ⊗ B ┌───────────┐ A ⊗ B
────┤ leftUnitor⁻¹ ├───────┤ ∅ ⊗ id B  ├───────
    └──────────────┘       └───────────┘
``` -/
noncomputable def projectRight
    -- `B` is retained; the other parallel interface is hidden.
    (A B : Interface) : TypedConverter B (tensor A B) :=
  comp (leftUnitorInv B) (parallel (discard A) (TypedConverter.id B))

/-- Projecting the left component of `R ∥ S` returns `R`. -/
lemma projectLeft_smul_parallel
    -- `R` on `A` is retained; `S` on `B` is discarded without being queried.
    (R : TypedSystem A) (S : TypedSystem B) :
    projectLeft A B • TypedSystem.parallel R S = R := by
  -- Attach `id A ⊗ discard B` locally, collapse the unit component to `dummy`, and drop it.
  rw [projectLeft, comp_smul, parallel_attach, identity_attach,
    TypedSystem.empty_eq (discard B • S), rightUnitor_inv_attach]

/-- Projecting the right component of `R ∥ S` returns `S`. -/
lemma projectRight_smul_parallel
    -- `R` on `A` is discarded without being queried; `S` on `B` is retained.
    (R : TypedSystem A) (S : TypedSystem B) :
    projectRight A B • TypedSystem.parallel R S = S := by
  -- Attach `discard A ⊗ id B` locally, collapse the unit component to `dummy`, and drop it.
  rw [projectRight, comp_smul, parallel_attach, identity_attach,
    TypedSystem.empty_eq (discard A • R), leftUnitor_inv_attach]

/-- Projecting the left component of `sample k ← P; R k ∥ S k` preserves the single retained
draw `k ← P` and returns the marginal system `sample k ← P; R k`. -/
lemma projectLeft_smul_sample_parallel
    -- `K` carries the shared initial sample; `P` is the normalized law drawn once.
    {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    -- `R k` is retained and `S k` is discarded for that same draw `k`.
    (R : K → TypedSystem A) (S : K → TypedSystem B) :
    projectLeft A B • TypedSystem.sample P (fun k => TypedSystem.parallel (R k) (S k)) =
      TypedSystem.sample P R := by
  -- Attachment commutes with the initial draw, then `projectLeft` drops `S k` pointwise in `k`.
  rw [smul_sample]
  simp only [projectLeft_smul_parallel]

/-- Projecting the right component of `sample k ← P; R k ∥ S k` preserves the single retained
draw `k ← P` and returns the marginal system `sample k ← P; S k`. -/
lemma projectRight_smul_sample_parallel
    -- `K` carries the shared initial sample; `P` is the normalized law drawn once.
    {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    -- `R k` is discarded and `S k` is retained for that same draw `k`.
    (R : K → TypedSystem A) (S : K → TypedSystem B) :
    projectRight A B • TypedSystem.sample P (fun k => TypedSystem.parallel (R k) (S k)) =
      TypedSystem.sample P S := by
  -- Attachment commutes with the initial draw, then `projectRight` drops `R k` pointwise in `k`.
  rw [smul_sample]
  simp only [projectRight_smul_parallel]

/-- Left projection is natural with respect to parallel converters: `α` moves outside `projectLeft`,
and `discard B` absorbs any converter `β` on the hidden component. -/
lemma projectLeft_comp_parallel
    -- `A`, `A'` are the outside and inside interfaces of `α`;
    -- `B`, `B'` are the outside and inside interfaces of `β`.
    {A A' B B' : Interface}
    (α : TypedConverter A A') (β : TypedConverter B B') :
    comp (projectLeft A B) (parallel α β) = comp α (projectLeft A' B') := by
  -- Interchange combines the retained converter with discard; inverse naturality moves it out.
  calc
    comp (projectLeft A B) (parallel α β)
        = comp (rightUnitorInv A)
          (comp (parallel (TypedConverter.id A) (discard B)) (parallel α β)) :=
          PDCBehavior.comp_assoc _ _ _
    _ = comp (rightUnitorInv A) (parallel (comp (TypedConverter.id A) α) (comp (discard B) β)) :=
          congrArg (comp (rightUnitorInv A)) (PDCBehavior.comp_tensor _ _ _ _)
    _ = comp (rightUnitorInv A) (parallel α (discard B')) := by
          rw [show comp (TypedConverter.id A) α = α from PDCBehavior.id_comp α A.nonempty_prefix,
            comp_discard β]
    _ = comp (rightUnitorInv A) (parallel (comp α (TypedConverter.id A'))
          (comp (TypedConverter.id unit) (discard B'))) := by
          rw [show comp α (TypedConverter.id A') = α from PDCBehavior.comp_id α A'.nonempty_prefix,
            show comp (TypedConverter.id unit) (discard B') = discard B' from
              PDCBehavior.id_comp (discard B') unit.nonempty_prefix]
    _ = comp (rightUnitorInv A) (comp (parallel α (TypedConverter.id unit))
          (parallel (TypedConverter.id A') (discard B'))) :=
          congrArg (comp (rightUnitorInv A)) (PDCBehavior.comp_tensor _ _ _ _).symm
    _ = comp (comp (rightUnitorInv A) (parallel α (TypedConverter.id unit)))
          (parallel (TypedConverter.id A') (discard B')) :=
          (PDCBehavior.comp_assoc _ _ _).symm
    _ = comp (comp α (rightUnitorInv A')) (parallel (TypedConverter.id A') (discard B')) := by
          rw [comp_rightUnitor_inv α]
    _ = comp α (projectLeft A' B') :=
          PDCBehavior.comp_assoc _ _ _

/-- Left projection commutes with a converter `α` on the retained component:
`projectLeft A B ≫ (α ⊗ id B) = α ≫ projectLeft A' B`. -/
lemma projectLeft_comp_parallel_id
    -- `A`, `A'` are the outside and inside interfaces of `α`; `B` is the hidden component.
    {A A' B : Interface} (α : TypedConverter A A') :
    comp (projectLeft A B) (parallel α (TypedConverter.id B)) = comp α (projectLeft A' B) :=
  projectLeft_comp_parallel α (TypedConverter.id B)

/-- Right projection is natural with respect to parallel converters: `β` moves outside
`projectRight`, and `discard A` absorbs any converter `α` on the hidden component. -/
lemma projectRight_comp_parallel
    -- `A`, `A'` are the outside and inside interfaces of `α`;
    -- `B`, `B'` are the outside and inside interfaces of `β`.
    {A A' B B' : Interface}
    (α : TypedConverter A A') (β : TypedConverter B B') :
    comp (projectRight A B) (parallel α β) = comp β (projectRight A' B') := by
  -- Interchange combines discard with the retained converter; inverse naturality moves it out.
  calc
    comp (projectRight A B) (parallel α β)
        = comp (leftUnitorInv B)
          (comp (parallel (discard A) (TypedConverter.id B)) (parallel α β)) :=
          PDCBehavior.comp_assoc _ _ _
    _ = comp (leftUnitorInv B) (parallel (comp (discard A) α) (comp (TypedConverter.id B) β)) :=
          congrArg (comp (leftUnitorInv B)) (PDCBehavior.comp_tensor _ _ _ _)
    _ = comp (leftUnitorInv B) (parallel (discard A') β) := by
          rw [comp_discard α,
            show comp (TypedConverter.id B) β = β from PDCBehavior.id_comp β B.nonempty_prefix]
    _ = comp (leftUnitorInv B) (parallel (comp (TypedConverter.id unit) (discard A'))
          (comp β (TypedConverter.id B'))) := by
          rw [show comp (TypedConverter.id unit) (discard A') = discard A' from
              PDCBehavior.id_comp (discard A') unit.nonempty_prefix,
            show comp β (TypedConverter.id B') = β from PDCBehavior.comp_id β B'.nonempty_prefix]
    _ = comp (leftUnitorInv B) (comp (parallel (TypedConverter.id unit) β)
          (parallel (discard A') (TypedConverter.id B'))) :=
          congrArg (comp (leftUnitorInv B)) (PDCBehavior.comp_tensor _ _ _ _).symm
    _ = comp (comp (leftUnitorInv B) (parallel (TypedConverter.id unit) β))
          (parallel (discard A') (TypedConverter.id B')) :=
          (PDCBehavior.comp_assoc _ _ _).symm
    _ = comp (comp β (leftUnitorInv B')) (parallel (discard A') (TypedConverter.id B')) := by
          rw [comp_leftUnitor_inv β]
    _ = comp β (projectRight A' B') :=
          PDCBehavior.comp_assoc _ _ _

/-- Right projection commutes with a converter `β` on the retained component:
`projectRight A B ≫ (id A ⊗ β) = β ≫ projectRight A B'`. -/
lemma projectRight_comp_parallel_id
    -- `A` is the hidden component; `B`, `B'` are the outside and inside interfaces of `β`.
    {A B B' : Interface} (β : TypedConverter B B') :
    comp (projectRight A B) (parallel (TypedConverter.id A) β) = comp β (projectRight A B') :=
  projectRight_comp_parallel (TypedConverter.id A) β

/-- Attaching `α ⊗ β` before `projectLeft A B` equals attaching `α` after `projectLeft A' B'`,
for any (possibly correlated) typed system `T` on `tensor A' B'`. -/
lemma projectLeft_smul_parallel_smul
    -- `A`, `A'` are the retained interfaces and `B`, `B'` the hidden interfaces.
    {A A' B B' : Interface}
    -- `α` acts on the retained side, `β` on the hidden side, and `T` is any joint system.
    (α : TypedConverter A A') (β : TypedConverter B B')
    (T : TypedSystem (tensor A' B')) :
    projectLeft A B • (parallel α β • T) = α • (projectLeft A' B' • T) := by
  rw [← comp_smul, projectLeft_comp_parallel, comp_smul]

/-- Attaching `α ⊗ β` before `projectRight A B` equals attaching `β` after `projectRight A' B'`,
for any (possibly correlated) typed system `T` on `tensor A' B'`. -/
lemma projectRight_smul_parallel_smul
    -- `A`, `A'` are the hidden interfaces and `B`, `B'` the retained interfaces.
    {A A' B B' : Interface}
    -- `α` acts on the hidden side, `β` on the retained side, and `T` is any joint system.
    (α : TypedConverter A A') (β : TypedConverter B B')
    (T : TypedSystem (tensor A' B')) :
    projectRight A B • (parallel α β • T) = β • (projectRight A' B' • T) := by
  rw [← comp_smul, projectRight_comp_parallel, comp_smul]

end TypedConverter

end SystemAlgebra
