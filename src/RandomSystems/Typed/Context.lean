module

public import RandomSystems.Typed.ParallelAttachment
public import RandomSystems.Typed.SystemCoherence
public import RandomSystems.Typed.ConverterCoherence
public import RandomSystems.Typed.Functional
public import RandomSystems.Converter.EmptyInterface

/-!
# Fixed contexts and parallel projections

A typed system `R` on `A` is a typed converter from `A` to the unit interface (`ofSystem`):
the PDC of the DDC readings (`resourcePDC`) of the deterministic systems presenting `R`.
Attaching it to the unit system gives `R`. In parallel with the identity it gives the fixed
contexts: attaching `rightContext A S` to `R` is `R ∥ S`, and so is attaching
`leftContext R B` to `S`.

Dually, `discard B` exposes the empty unit interface and never queries `B`; every converter with
the unit outside interface equals `discard B` (`eq_discard`). Composing the inverse unit
renamings with `id ⊗ discard` and `discard ⊗ id` defines the ordered projections
`projectLeft A B : A → A ⊗ B` and `projectRight A B : B → A ⊗ B`:

```text
  A ┌───────────────┐ A ⊗ 1 ┌───────────┐ A ⊗ B
────┤ rightUnitor⁻¹ ├───────┤ id A ⊗ ∅  ├───────    (projectLeft A B)
    └───────────────┘       └───────────┘

  B ┌──────────────┐ 1 ⊗ B ┌───────────┐ A ⊗ B
────┤ leftUnitor⁻¹ ├───────┤ ∅ ⊗ id B  ├───────    (projectRight A B)
    └──────────────┘       └───────────┘
```

Attaching `projectLeft A B` or `projectRight A B` to `R ∥ S` returns `R` or `S`
(`projectLeft_smul_parallel`, `projectRight_smul_parallel`). On a shared initial draw
`sample k ← P; R k ∥ S k`, `smul_sample` preserves that single draw and returns the marginal
system `sample k ← P; R k` or `sample k ← P; S k` (`projectLeft_smul_sample_parallel`,
`projectRight_smul_sample_parallel`). Both projections are natural with respect to parallel
converters (`projectLeft_comp_parallel`, `projectRight_comp_parallel`) and in particular commute
with a converter on the retained component (`projectLeft_comp_parallel_id`,
`projectRight_comp_parallel_id`).

## Main definitions

* `TypedConverter.ofSystem R`: `R` as a typed converter with no inside interfaces
* `TypedConverter.discard B`: the converter exposing the unit interface and ignoring `B`
* `TypedConverter.constant R B`: the converter that ignores its inside system and exposes `R`
* `TypedConverter.rightContext A S`, `TypedConverter.leftContext R B`: the fixed contexts
* `TypedConverter.projectLeft A B`, `TypedConverter.projectRight A B`: the ordered projections

## Main results

* `TypedConverter.attach_ofSystem`, `TypedConverter.attach_constant`: attaching them gives `R`
* `TypedConverter.eq_discard`, `TypedConverter.comp_discard`: uniqueness of the discarding
  converter at the unit outside interface
* `TypedConverter.attach_rightContext`, `TypedConverter.attach_leftContext`: attaching a
  context is parallel composition
* `TypedConverter.projectLeft_smul_parallel`, `TypedConverter.projectRight_smul_parallel`:
  projecting a parallel system returns the selected component
* `TypedConverter.projectLeft_smul_sample_parallel`,
  `TypedConverter.projectRight_smul_sample_parallel`: projecting a sampled parallel system
  preserves the retained draw and returns its marginal
* `TypedConverter.projectLeft_comp_parallel`, `TypedConverter.projectRight_comp_parallel`,
  `TypedConverter.projectLeft_comp_parallel_id`, `TypedConverter.projectRight_comp_parallel_id`:
  naturality of both projections

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
    (rename (A := tensor A unit) (B := A) (Equiv.sumEmpty A.I Empty) (rightUnitAlphabet A.X)
        (rightUnitAlphabet A.Y) (rightUnitAlphabet_fst A.X) (rightUnitAlphabet_fst A.Y)
        (parallelDomain_unit_right A) • R : TypedSystem (tensor A unit)) =
      TypedSystem.parallel R TypedSystem.dummy := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [rename_mass, TypedSystem.parallel_unit_right_mass]

/-- The left unit renaming attached to a typed system puts the dummy system beside it. -/
lemma leftUnitor_hom_attach (R : TypedSystem A) :
    (rename (A := tensor unit A) (B := A) (Equiv.emptySum Empty A.I) (leftUnitAlphabet A.X)
        (leftUnitAlphabet A.Y) (leftUnitAlphabet_fst A.X) (leftUnitAlphabet_fst A.Y)
        (parallelDomain_unit_left A) • R : TypedSystem (tensor unit A)) =
      TypedSystem.parallel TypedSystem.dummy R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [rename_mass, TypedSystem.parallel_unit_left_mass]

/-- The fixed right context: the identity beside `S` as a converter, followed by the right unit
renaming. -/
noncomputable def rightContext (A : Interface) {B : Interface} (S : TypedSystem B) :
    TypedConverter (tensor A B) A :=
  comp (parallel (TypedConverter.id A) (ofSystem S))
    (rename (Equiv.sumEmpty A.I Empty) (rightUnitAlphabet A.X) (rightUnitAlphabet A.Y)
      (rightUnitAlphabet_fst A.X) (rightUnitAlphabet_fst A.Y) (parallelDomain_unit_right A))

/-- The fixed left context; no symmetry of the selected substitution relation is used. -/
noncomputable def leftContext {A : Interface} (R : TypedSystem A) (B : Interface) :
    TypedConverter (tensor A B) B :=
  comp (parallel (ofSystem R) (TypedConverter.id B))
    (rename (Equiv.emptySum Empty B.I) (leftUnitAlphabet B.X) (leftUnitAlphabet B.Y)
      (leftUnitAlphabet_fst B.X) (leftUnitAlphabet_fst B.Y) (parallelDomain_unit_left B))

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
    -- `R` is a typed system on `A`, paired on the right with `TypedSystem.dummy`.
    (R : TypedSystem A) :
    (rename (A := A) (B := tensor A unit) (Equiv.sumEmpty A.I Empty).symm
        (rightUnitAlphabet A.X).symm (rightUnitAlphabet A.Y).symm
        (alphabet_symm_label _ _ (rightUnitAlphabet_fst A.X))
        (alphabet_symm_label _ _ (rightUnitAlphabet_fst A.Y))
        (fun h => by
          have he := (parallelDomain_unit_right A (h.map (rightUnitAlphabet A.X).symm)).symm
          simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he) •
      TypedSystem.parallel R TypedSystem.dummy : TypedSystem A) = R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [rename_mass, TypedSystem.parallel_unit_right_mass]
  simp only [← Equiv.prodCongr_symm, List.map_map, Equiv.self_comp_symm, List.map_id]

/-- The inverse left unit renaming drops a left-hand dummy system. -/
lemma leftUnitor_inv_attach
    -- `R` is a typed system on `A`, paired on the left with `TypedSystem.dummy`.
    (R : TypedSystem A) :
    (rename (A := A) (B := tensor unit A) (Equiv.emptySum Empty A.I).symm
        (leftUnitAlphabet A.X).symm (leftUnitAlphabet A.Y).symm
        (alphabet_symm_label _ _ (leftUnitAlphabet_fst A.X))
        (alphabet_symm_label _ _ (leftUnitAlphabet_fst A.Y))
        (fun h => by
          have he := (parallelDomain_unit_left A (h.map (leftUnitAlphabet A.X).symm)).symm
          simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he) •
      TypedSystem.parallel TypedSystem.dummy R : TypedSystem A) = R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [rename_mass, TypedSystem.parallel_unit_left_mass]
  simp only [← Equiv.prodCongr_symm, List.map_map, Equiv.self_comp_symm, List.map_id]

/-- Naturality of the inverse right unit renaming with respect to any typed converter `α`. -/
lemma comp_rightUnitor_inv
    -- `A`, `A'` are the outside and inside interfaces of `α`.
    {A A' : Interface} (α : TypedConverter A A') :
    comp (rename (A := A) (B := tensor A unit) (Equiv.sumEmpty A.I Empty).symm
        (rightUnitAlphabet A.X).symm (rightUnitAlphabet A.Y).symm
        (alphabet_symm_label _ _ (rightUnitAlphabet_fst A.X))
        (alphabet_symm_label _ _ (rightUnitAlphabet_fst A.Y))
        (fun h => by
          have he := (parallelDomain_unit_right A (h.map (rightUnitAlphabet A.X).symm)).symm
          simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he))
      (parallel α (TypedConverter.id unit)) =
    comp α (rename (A := A') (B := tensor A' unit) (Equiv.sumEmpty A'.I Empty).symm
      (rightUnitAlphabet A'.X).symm (rightUnitAlphabet A'.Y).symm
      (alphabet_symm_label _ _ (rightUnitAlphabet_fst A'.X))
      (alphabet_symm_label _ _ (rightUnitAlphabet_fst A'.Y))
      (fun h => by
        have he := (parallelDomain_unit_right A' (h.map (rightUnitAlphabet A'.X).symm)).symm
        simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)) := by
  let rHom (C : Interface) : TypedConverter (tensor C unit) C :=
    rename (Equiv.sumEmpty C.I Empty) (rightUnitAlphabet C.X) (rightUnitAlphabet C.Y)
      (rightUnitAlphabet_fst C.X) (rightUnitAlphabet_fst C.Y) (parallelDomain_unit_right C)
  let rInv (C : Interface) : TypedConverter C (tensor C unit) :=
    rename (Equiv.sumEmpty C.I Empty).symm (rightUnitAlphabet C.X).symm
      (rightUnitAlphabet C.Y).symm
      (alphabet_symm_label _ _ (rightUnitAlphabet_fst C.X))
      (alphabet_symm_label _ _ (rightUnitAlphabet_fst C.Y))
      (fun h => by
        have he := (parallelDomain_unit_right C (h.map (rightUnitAlphabet C.X).symm)).symm
        simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)
  -- The inverse right unit renaming cancels `rHom` on both sides.
  have hinvA : comp (rInv A) (rHom A) = TypedConverter.id A := by
    rw [rename_comp]
    simpa only [Equiv.symm_trans_self] using rename_refl A
  have hhomA' : comp (rHom A') (rInv A') = TypedConverter.id (tensor A' unit) := by
    rw [rename_comp]
    simpa only [Equiv.self_trans_symm] using rename_refl (tensor A' unit)
  -- Conjugate `comp_rightUnitor α` by `rInv A` on the left and `rInv A'` on the right.
  calc
    comp (rInv A) (parallel α (TypedConverter.id unit))
        = comp (rInv A) (comp (parallel α (TypedConverter.id unit))
            (TypedConverter.id (tensor A' unit))) :=
          congrArg (comp (rInv A)) (PDCBehavior.comp_id _ (tensor A' unit).nonempty_prefix).symm
    _ = comp (rInv A) (comp (parallel α (TypedConverter.id unit))
          (comp (rHom A') (rInv A'))) := by
          rw [hhomA']
    _ = comp (rInv A) (comp (comp (parallel α (TypedConverter.id unit)) (rHom A'))
          (rInv A')) :=
          congrArg (comp (rInv A)) (PDCBehavior.comp_assoc _ _ _).symm
    _ = comp (rInv A) (comp (comp (rHom A) α) (rInv A')) := by
          rw [comp_rightUnitor α]
    _ = comp (comp (rInv A) (rHom A)) (comp α (rInv A')) := by
          simp only [comp, PDCBehavior.comp_assoc]
    _ = comp (TypedConverter.id A) (comp α (rInv A')) := by
          rw [hinvA]
    _ = comp α (rInv A') :=
          PDCBehavior.id_comp _ A.nonempty_prefix

/-- Naturality of the inverse left unit renaming with respect to any typed converter `β`. -/
lemma comp_leftUnitor_inv
    -- `B`, `B'` are the outside and inside interfaces of `β`.
    {B B' : Interface} (β : TypedConverter B B') :
    comp (rename (A := B) (B := tensor unit B) (Equiv.emptySum Empty B.I).symm
        (leftUnitAlphabet B.X).symm (leftUnitAlphabet B.Y).symm
        (alphabet_symm_label _ _ (leftUnitAlphabet_fst B.X))
        (alphabet_symm_label _ _ (leftUnitAlphabet_fst B.Y))
        (fun h => by
          have he := (parallelDomain_unit_left B (h.map (leftUnitAlphabet B.X).symm)).symm
          simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he))
      (parallel (TypedConverter.id unit) β) =
    comp β (rename (A := B') (B := tensor unit B') (Equiv.emptySum Empty B'.I).symm
      (leftUnitAlphabet B'.X).symm (leftUnitAlphabet B'.Y).symm
      (alphabet_symm_label _ _ (leftUnitAlphabet_fst B'.X))
      (alphabet_symm_label _ _ (leftUnitAlphabet_fst B'.Y))
      (fun h => by
        have he := (parallelDomain_unit_left B' (h.map (leftUnitAlphabet B'.X).symm)).symm
        simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)) := by
  let lHom (C : Interface) : TypedConverter (tensor unit C) C :=
    rename (Equiv.emptySum Empty C.I) (leftUnitAlphabet C.X) (leftUnitAlphabet C.Y)
      (leftUnitAlphabet_fst C.X) (leftUnitAlphabet_fst C.Y) (parallelDomain_unit_left C)
  let lInv (C : Interface) : TypedConverter C (tensor unit C) :=
    rename (Equiv.emptySum Empty C.I).symm (leftUnitAlphabet C.X).symm
      (leftUnitAlphabet C.Y).symm
      (alphabet_symm_label _ _ (leftUnitAlphabet_fst C.X))
      (alphabet_symm_label _ _ (leftUnitAlphabet_fst C.Y))
      (fun h => by
        have he := (parallelDomain_unit_left C (h.map (leftUnitAlphabet C.X).symm)).symm
        simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)
  -- The inverse left unit renaming cancels `lHom` on both sides.
  have hinvB : comp (lInv B) (lHom B) = TypedConverter.id B := by
    rw [rename_comp]
    simpa only [Equiv.symm_trans_self] using rename_refl B
  have hhomB' : comp (lHom B') (lInv B') = TypedConverter.id (tensor unit B') := by
    rw [rename_comp]
    simpa only [Equiv.self_trans_symm] using rename_refl (tensor unit B')
  -- Conjugate `comp_leftUnitor β` by `lInv B` on the left and `lInv B'` on the right.
  calc
    comp (lInv B) (parallel (TypedConverter.id unit) β)
        = comp (lInv B) (comp (parallel (TypedConverter.id unit) β)
            (TypedConverter.id (tensor unit B'))) :=
          congrArg (comp (lInv B)) (PDCBehavior.comp_id _ (tensor unit B').nonempty_prefix).symm
    _ = comp (lInv B) (comp (parallel (TypedConverter.id unit) β)
          (comp (lHom B') (lInv B'))) := by
          rw [hhomB']
    _ = comp (lInv B) (comp (comp (parallel (TypedConverter.id unit) β) (lHom B'))
          (lInv B')) :=
          congrArg (comp (lInv B)) (PDCBehavior.comp_assoc _ _ _).symm
    _ = comp (lInv B) (comp (comp (lHom B) β) (lInv B')) := by
          rw [comp_leftUnitor β]
    _ = comp (comp (lInv B) (lHom B)) (comp β (lInv B')) := by
          simp only [comp, PDCBehavior.comp_assoc]
    _ = comp (TypedConverter.id B) (comp β (lInv B')) := by
          rw [hinvB]
    _ = comp β (lInv B') :=
          PDCBehavior.id_comp _ B.nonempty_prefix

/-- Left projection of a binary parallel interface: `projectLeft A B : A → A ⊗ B` applies the
inverse right unit renaming outside `id A ⊗ discard B`, forwarding queries on `A` and making
no queries to `B`.

```text
  A ┌───────────────┐ A ⊗ 1 ┌───────────┐ A ⊗ B
────┤ rightUnitor⁻¹ ├───────┤ id A ⊗ ∅  ├───────
    └───────────────┘       └───────────┘
``` -/
noncomputable def projectLeft
    -- `A` is the retained outside interface; `B` is the hidden parallel component.
    (A B : Interface) : TypedConverter A (tensor A B) :=
  comp
    (rename (Equiv.sumEmpty A.I Empty).symm (rightUnitAlphabet A.X).symm
      (rightUnitAlphabet A.Y).symm
      (alphabet_symm_label _ _ (rightUnitAlphabet_fst A.X))
      (alphabet_symm_label _ _ (rightUnitAlphabet_fst A.Y))
      (fun h => by
        have he := (parallelDomain_unit_right A (h.map (rightUnitAlphabet A.X).symm)).symm
        simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he))
    (parallel (TypedConverter.id A) (discard B))

/-- Right projection of a binary parallel interface: `projectRight A B : B → A ⊗ B` applies the
inverse left unit renaming outside `discard A ⊗ id B`, making no queries to `A` and forwarding
queries on `B`.

```text
  B ┌──────────────┐ 1 ⊗ B ┌───────────┐ A ⊗ B
────┤ leftUnitor⁻¹ ├───────┤ ∅ ⊗ id B  ├───────
    └──────────────┘       └───────────┘
``` -/
noncomputable def projectRight
    -- `A` is the hidden parallel component; `B` is the retained outside interface.
    (A B : Interface) : TypedConverter B (tensor A B) :=
  comp
    (rename (Equiv.emptySum Empty B.I).symm (leftUnitAlphabet B.X).symm
      (leftUnitAlphabet B.Y).symm
      (alphabet_symm_label _ _ (leftUnitAlphabet_fst B.X))
      (alphabet_symm_label _ _ (leftUnitAlphabet_fst B.Y))
      (fun h => by
        have he := (parallelDomain_unit_left B (h.map (leftUnitAlphabet B.X).symm)).symm
        simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he))
    (parallel (discard A) (TypedConverter.id B))

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
  let rInv (C : Interface) : TypedConverter C (tensor C unit) :=
    rename (Equiv.sumEmpty C.I Empty).symm (rightUnitAlphabet C.X).symm
      (rightUnitAlphabet C.Y).symm
      (alphabet_symm_label _ _ (rightUnitAlphabet_fst C.X))
      (alphabet_symm_label _ _ (rightUnitAlphabet_fst C.Y))
      (fun h => by
        have he := (parallelDomain_unit_right C (h.map (rightUnitAlphabet C.X).symm)).symm
        simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)
  -- Combine `(id A ⊗ discard B) ≫ (α ⊗ β) = α ⊗ discard B'`, then commute `α` past `rInv`.
  calc
    comp (projectLeft A B) (parallel α β)
        = comp (rInv A) (comp (parallel (TypedConverter.id A) (discard B)) (parallel α β)) :=
          PDCBehavior.comp_assoc _ _ _
    _ = comp (rInv A) (parallel (comp (TypedConverter.id A) α) (comp (discard B) β)) :=
          congrArg (comp (rInv A)) (PDCBehavior.comp_tensor _ _ _ _)
    _ = comp (rInv A) (parallel α (discard B')) := by
          rw [show comp (TypedConverter.id A) α = α from PDCBehavior.id_comp α A.nonempty_prefix,
            comp_discard β]
    _ = comp (rInv A) (parallel (comp α (TypedConverter.id A'))
          (comp (TypedConverter.id unit) (discard B'))) := by
          rw [show comp α (TypedConverter.id A') = α from PDCBehavior.comp_id α A'.nonempty_prefix,
            show comp (TypedConverter.id unit) (discard B') = discard B' from
              PDCBehavior.id_comp (discard B') unit.nonempty_prefix]
    _ = comp (rInv A) (comp (parallel α (TypedConverter.id unit))
          (parallel (TypedConverter.id A') (discard B'))) :=
          congrArg (comp (rInv A)) (PDCBehavior.comp_tensor _ _ _ _).symm
    _ = comp (comp (rInv A) (parallel α (TypedConverter.id unit)))
          (parallel (TypedConverter.id A') (discard B')) :=
          (PDCBehavior.comp_assoc _ _ _).symm
    _ = comp (comp α (rInv A')) (parallel (TypedConverter.id A') (discard B')) := by
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
  let lInv (C : Interface) : TypedConverter C (tensor unit C) :=
    rename (Equiv.emptySum Empty C.I).symm (leftUnitAlphabet C.X).symm
      (leftUnitAlphabet C.Y).symm
      (alphabet_symm_label _ _ (leftUnitAlphabet_fst C.X))
      (alphabet_symm_label _ _ (leftUnitAlphabet_fst C.Y))
      (fun h => by
        have he := (parallelDomain_unit_left C (h.map (leftUnitAlphabet C.X).symm)).symm
        simpa only [List.map_map, Equiv.self_comp_symm, List.map_id] using he)
  -- Combine `(discard A ⊗ id B) ≫ (α ⊗ β) = discard A' ⊗ β`, then commute `β` past `lInv`.
  calc
    comp (projectRight A B) (parallel α β)
        = comp (lInv B) (comp (parallel (discard A) (TypedConverter.id B)) (parallel α β)) :=
          PDCBehavior.comp_assoc _ _ _
    _ = comp (lInv B) (parallel (comp (discard A) α) (comp (TypedConverter.id B) β)) :=
          congrArg (comp (lInv B)) (PDCBehavior.comp_tensor _ _ _ _)
    _ = comp (lInv B) (parallel (discard A') β) := by
          rw [comp_discard α,
            show comp (TypedConverter.id B) β = β from PDCBehavior.id_comp β B.nonempty_prefix]
    _ = comp (lInv B) (parallel (comp (TypedConverter.id unit) (discard A'))
          (comp β (TypedConverter.id B'))) := by
          rw [show comp (TypedConverter.id unit) (discard A') = discard A' from
              PDCBehavior.id_comp (discard A') unit.nonempty_prefix,
            show comp β (TypedConverter.id B') = β from PDCBehavior.comp_id β B'.nonempty_prefix]
    _ = comp (lInv B) (comp (parallel (TypedConverter.id unit) β)
          (parallel (discard A') (TypedConverter.id B'))) :=
          congrArg (comp (lInv B)) (PDCBehavior.comp_tensor _ _ _ _).symm
    _ = comp (comp (lInv B) (parallel (TypedConverter.id unit) β))
          (parallel (discard A') (TypedConverter.id B')) :=
          (PDCBehavior.comp_assoc _ _ _).symm
    _ = comp (comp β (lInv B')) (parallel (discard A') (TypedConverter.id B')) := by
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
