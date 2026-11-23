module

public import RandomSystems.Typed.Distinguisher
public import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction
public import RandomSystems.Distance.RevealedHCoefficient
public import RandomSystems.Typed.Context
public import RandomSystems.Typed.ParallelAttachment
public import RandomSystems.Typed.SamplingDistance
public import RandomSystems.Typed.SystemCoherence
public import RandomSystems.Typed.Distance
public import ConstructiveCryptography.Instances.Monoidal
public import ConstructiveCryptography.CryptographicAlgebra.Distinguisher
public import RandomSystems.Distance.Distinguisher
public import ConstructiveCryptography.Substitution.Reduction
public import ConstructiveCryptography.Notation.Basic

/-!
# Interfaces as a cryptographic algebra

Interfaces are an instance of `ResourceTheory`: its carrier `Φ A` is `TypedSystem A`, its field
`attach` is `TypedConverter.attach`, the attachment of PDC behaviors, and its axioms
`attach_identity` and `attach_serial` are discharged by `TypedConverter.identity_attach` and
`TypedConverter.comp_smul`. They are an instance of `CryptographicAlgebra`: the lax monoidal
structure of the functor of typed systems has the product `TypedSystem.parallel` and the unit
`TypedSystem.dummy`; naturality is discharged by `TypedConverter.parallel_attach`, and
associativity and unitality by `parallel_assoc`, `parallel_dummy_left` and `parallel_dummy_right`,
which read `TypedConverter.rename_mass` with `TypedSystem.parallel_assoc_mass`,
`TypedSystem.parallel_unit_left_mass` and `TypedSystem.parallel_unit_right_mass` through the
regrouping isomorphisms. They are an instance of `CompatibleDistinguisherClass`: the
distinguishers on `A` are the output-1 probabilities of **all** stopping distinguishers
compatible with `A`'s domain (`TypedDistinguisher A`, i.e. `Domain.DistinguisherBehavior`).
The axiom `closed_attach` is discharged by `Domain.DistinguisherBehavior.absorb`, and
`closed_parallel_left` and `closed_parallel_right` by `Domain.Distinguisher.exists_absorbRight`
and the swap (`TypedSystem.parallel_swap_mass`). Its metric is the canonical transcript distance
(`TypedSystem.transcriptPseudoEMetricSpace`), so `cc_distance_eq` holds by definition. The bridge
`transcriptDistance_eq_advantageDistance` identifies it with the advantage distance of these
distinguishers. Non-expansion under attachment and parallel composition is not a systems
theorem: the abstract `CompatibleDistinguisherClass.ofClosure` (Maurer 2011, Lemma 1) derives it
from the closure lemmas, and the bridge transfers it to the transcript distance.

The decision layer is instantiated separately. `TypedDistinguisher A` evaluates by its output-1
probability (`distinguisherEvaluations`), and typed absorption `(dα)(R) = d(αR)` is the CC
action (`distinguisherAction`). These instances select no admitted class, and no
`AdmissibleDistinguishers` instance is installed: a security statement chooses its tests
locally, with no efficiency or universal closure claim, and each reduction supplies
`AdmissibleDistinguishers.ClosedUnder α` for its own converter `α`. For every admitted set,
`distinguisherAdvantageDominated` bounds the decision advantage by the transcript distance, the
domination law needed by statistical steps of a substitution chain.

## Main definitions

* `Interface.resourcesLaxMonoidal`: parallel composition and the dummy system
* `Interface.distinguishers A`: the behaviors of the probabilistic distinguishers compatible with
  `A`'s domain
* `Interface.resourceTheory`, `Interface.cryptographicAlgebra`,
  `Interface.compatibleDistinguisherClass`: the instances
* `Interface.distinguisherEvaluations`, `Interface.distinguisherAction`: decision evaluation and
  absorption of `TypedDistinguisher`
* `Interface.distinguisherAdvantageDominated admitted`: the decision advantage of every admitted
  set is dominated by the transcript distance

## Main results

* `Interface.parallel_assoc`, `Interface.parallel_dummy_left`, `Interface.parallel_dummy_right`:
  the lax monoidal laws through the regrouping isomorphisms
* `Interface.associator_hom_attach`, `Interface.leftUnitor_hom_attach`,
  `Interface.rightUnitor_hom_attach`: the forward associator and unitor attachment laws,
  instantiated from the `CryptographicAlgebra` class laws
* `Interface.whiskerLeft_smul`, `Interface.whiskerRight_smul`, `Interface.whisker_smul_comm`:
  whiskering attachment and interchange laws on typed systems, from the class laws
* `Interface.parallel_swap`: parallel composition is commutative through the swap
* `Interface.distinguishers_attach`, `Interface.distinguishers_parallel_left`,
  `Interface.distinguishers_parallel_right`: closure
* `Interface.cc_parallel_eq`, `Interface.cc_dummy_eq`: the abstract operations are the
  concrete ones
* `Interface.transcriptDistance_eq_advantageDistance`: the transcript distance is the advantage
  distance of `Interface.distinguishers A`
* `Interface.cc_distance_eq`: the distance is the transcript distance of the random systems, by
  definition
* `Interface.distance_sample_le_expect`: the distance of two retained samples is at most their
  expected component error
* `Interface.distance_le_of_hCoefficient`: an H-coefficient argument bounds the distance
* `Interface.projectLeft_eq`, `Interface.projectRight_eq`, `Interface.projectLeft_smul_parallel`,
  `Interface.projectRight_smul_parallel`, `Interface.projectLeft_smul_sample_parallel`,
  `Interface.projectRight_smul_sample_parallel`, `Interface.projectLeft_comp_tensor`,
  `Interface.projectLeft_comp_whiskerRight`, `Interface.projectRight_comp_tensor`,
  `Interface.projectRight_comp_whiskerLeft`, `Interface.projectLeft_smul_tensor_smul`,
  `Interface.projectRight_smul_tensor_smul`: instance-level laws of `TypedConverter.projectLeft` and
  `TypedConverter.projectRight`
-/

@[expose] public section

namespace SystemAlgebra.Interface

open CategoryTheory CategoryTheory.MonoidalCategory

/-- Interfaces are an instance of `ResourceTheory`: its carrier on `A` is `TypedSystem A`, and
attachment is the attachment of PDC behaviors. -/
noncomputable instance resourceTheory :
    ConstructiveCryptography.ResourceTheory Interface TypedSystem where
  attach := TypedConverter.attach
  attach_identity := TypedConverter.identity_attach
  attach_serial := TypedConverter.comp_smul

/-- The attachment field of `resourceTheory` is the direct typed action:
`ResourceTheory.attach α R = α • R` with `α : TypedConverter A B`, by definition. A
representation bridge for this selected instance, not a law of an arbitrary resource theory or
of another action on typed systems. -/
lemma attach_eq_typed_smul {A B : Interface} (α : A ⟶ B) (R : TypedSystem B) :
    ConstructiveCryptography.ResourceTheory.attach α R =
      (show TypedConverter A B from α) • R := rfl

lemma parallel_assoc {A B C : Interface} (R : TypedSystem A) (S : TypedSystem B)
    (T : TypedSystem C) :
    ((associator A B C).inv • TypedSystem.parallel (TypedSystem.parallel R S) T :
      TypedSystem (tensor A (tensor B C))) =
      TypedSystem.parallel R (TypedSystem.parallel S T) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  simp only [associator, isoOf]
  rw [TypedConverter.rename_mass, TypedSystem.parallel_assoc_mass]
  simp only [← Equiv.prodCongr_symm, List.map_map, Equiv.self_comp_symm, List.map_id]

lemma parallel_dummy_left {A : Interface} (R : TypedSystem A) :
    ((leftUnitor A).inv • TypedSystem.parallel TypedSystem.dummy R : TypedSystem A) = R :=
  TypedConverter.leftUnitor_inv_attach R

lemma parallel_dummy_right {A : Interface} (R : TypedSystem A) :
    ((rightUnitor A).inv • TypedSystem.parallel R TypedSystem.dummy : TypedSystem A) = R :=
  TypedConverter.rightUnitor_inv_attach R

lemma parallel_swap {A B : Interface} (R : TypedSystem A) (S : TypedSystem B) :
    ((swap A B).hom • TypedSystem.parallel S R : TypedSystem (tensor A B)) =
      TypedSystem.parallel R S := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  simp only [swap, isoOf]
  rw [TypedConverter.rename_mass, TypedSystem.parallel_swap_mass]

noncomputable instance resourcesLaxMonoidal :
    (ConstructiveCryptography.ResourceTheory.functor Interface TypedSystem).LaxMonoidal where
  ε := TypeCat.ofHom fun _ => TypedSystem.dummy
  μ A B := TypeCat.ofHom fun (p : TypedSystem A.unop × TypedSystem B.unop) =>
    TypedSystem.parallel p.1 p.2
  μ_natural_left f A' := by
    ext p
    have h := (TypedConverter.parallel_attach f.unop (𝟙 A'.unop) p.1 p.2).symm
    rw [identity_attach (A := A'.unop) p.2] at h
    exact h
  μ_natural_right A' f := by
    ext p
    have h := (TypedConverter.parallel_attach (𝟙 A'.unop) f.unop p.1 p.2).symm
    rw [identity_attach (A := A'.unop) p.1] at h
    exact h
  associativity A B C := by
    ext p
    exact parallel_assoc p.1.1 p.1.2 p.2
  left_unitality A := by
    ext p
    exact (parallel_dummy_left p.2).symm
  right_unitality A := by
    ext p
    exact (parallel_dummy_right p.1).symm

/-- Interfaces, typed converters and typed systems are a cryptographic algebra. -/
noncomputable instance cryptographicAlgebra :
    ConstructiveCryptography.CryptographicAlgebra Interface TypedSystem where
  laxMonoidal := resourcesLaxMonoidal

/-- Forward associator regroups three parallel typed systems, from the class law. -/
lemma associator_hom_attach {A B C : Interface} (R : TypedSystem A) (S : TypedSystem B)
    (T : TypedSystem C) :
    ((associator A B C).hom • TypedSystem.parallel R (TypedSystem.parallel S T) :
      TypedSystem (tensor (tensor A B) C)) =
      TypedSystem.parallel (TypedSystem.parallel R S) T :=
  ConstructiveCryptography.CryptographicAlgebra.associator_hom_attach R S T

/-- Forward left unitor adjoins `TypedSystem.dummy` on the left, from the class law. -/
lemma leftUnitor_hom_attach {A : Interface} (R : TypedSystem A) :
    ((leftUnitor A).hom • R : TypedSystem (tensor unit A)) =
      TypedSystem.parallel TypedSystem.dummy R :=
  ConstructiveCryptography.CryptographicAlgebra.leftUnitor_hom_attach R

/-- Forward right unitor adjoins `TypedSystem.dummy` on the right, from the class law. -/
lemma rightUnitor_hom_attach {A : Interface} (R : TypedSystem A) :
    ((rightUnitor A).hom • R : TypedSystem (tensor A unit)) =
      TypedSystem.parallel R TypedSystem.dummy :=
  ConstructiveCryptography.CryptographicAlgebra.rightUnitor_hom_attach R

/-- Left-whiskering `A ◁ β` acts on the right typed system, from the class law. -/
lemma whiskerLeft_smul {A B B' : Interface} (β : B' ⟶ B)
    (R : TypedSystem A) (S : TypedSystem B) :
    ((A ◁ β) • TypedSystem.parallel R S : TypedSystem (tensor A B')) =
      TypedSystem.parallel R (β • S) :=
  ConstructiveCryptography.CryptographicAlgebra.attach_whiskerLeft β R S

/-- Right-whiskering `α ▷ B` acts on the left typed system, from the class law. -/
lemma whiskerRight_smul {A A' B : Interface} (α : A' ⟶ A)
    (R : TypedSystem A) (S : TypedSystem B) :
    ((α ▷ B) • TypedSystem.parallel R S : TypedSystem (tensor A' B)) =
      TypedSystem.parallel (α • R) S :=
  ConstructiveCryptography.CryptographicAlgebra.attach_whiskerRight α R S

/-- Right-whiskering and left-whiskering attachments commute on typed systems. -/
lemma whisker_smul_comm {A A' B B' : Interface} (α : A' ⟶ A) (β : B' ⟶ B)
    (R : TypedSystem (tensor A B)) :
    ((α ▷ B') • ((A ◁ β) • R) : TypedSystem (tensor A' B')) =
      (A' ◁ β) • ((α ▷ B) • R) :=
  ConstructiveCryptography.CryptographicAlgebra.whisker_attach_comm α β R

/-- Typed distinguishers evaluate by their output-1 behavior: `probability d R = d.1 R`, the
probability that `d` connected to `R` outputs `1`. -/
noncomputable instance distinguisherEvaluations :
    ConstructiveCryptography.Distinguishers Interface TypedSystem TypedDistinguisher where
  probability d R := d.1 R

/-- Typed absorption is the abstract action: `absorb d α = dα`, with its probability, identity
and serial laws discharged by the `TypedDistinguisher` lemmas. No admitted class is involved. -/
noncomputable instance distinguisherAction :
    ConstructiveCryptography.DistinguisherAction Interface TypedSystem TypedDistinguisher where
  absorb := TypedDistinguisher.absorb
  probability_absorb := TypedDistinguisher.probability_absorb
  absorb_id := TypedDistinguisher.absorb_id
  absorb_comp := TypedDistinguisher.absorb_comp

/-- The distinguishers on `A`: the behaviors of the probabilistic distinguishers compatible with
`A`'s domain, their probabilities of outputting `1`. -/
def distinguishers (A : Interface) : Set (TypedSystem A → ℝ) :=
  Set.range fun (d : TypedDistinguisher A) =>
    ConstructiveCryptography.Distinguishers.probability (Phi := TypedSystem) d

/-- Absorbing a converter into a distinguisher gives a distinguisher. -/
lemma distinguishers_attach {A B : Interface} (α : A ⟶ B) {d : TypedSystem A → ℝ}
    (hd : d ∈ distinguishers A) : (fun R : TypedSystem B => d (α • R)) ∈ distinguishers B := by
  obtain ⟨D, rfl⟩ := hd
  exact ⟨TypedDistinguisher.absorb D α, rfl⟩

/-- Running a fixed typed system beside the distinguished one gives a distinguisher. -/
lemma distinguishers_parallel_left {A B : Interface} (T : TypedSystem B)
    {d : TypedSystem (tensor A B) → ℝ} (hd : d ∈ distinguishers (tensor A B)) :
    (fun R : TypedSystem A => d (TypedSystem.parallel R T)) ∈ distinguishers A := by
  obtain ⟨D, rfl⟩ := hd
  obtain ⟨P, hP⟩ := D.2
  obtain ⟨U, rfl⟩ := T.exists_ofPDS
  obtain ⟨Q, hQ⟩ := Domain.Distinguisher.exists_absorbRight (X₁ := A.X) (Y₁ := A.Y)
    (X₂ := B.X) (Y₂ := B.Y) (hE := A.length_le) (hF := B.length_le)
    A.nonempty_prefix B.nonempty_prefix P U
  refine ⟨⟨fun R => D.1 (TypedSystem.parallel R (TypedSystem.ofPDS U)), Q, fun R => ?_⟩, rfl⟩
  obtain ⟨Pr, rfl⟩ := TypedSystem.exists_ofPDS R
  refine (hP (TypedSystem.parallel (TypedSystem.ofPDS Pr) (TypedSystem.ofPDS U))).trans ?_
  rw [TypedSystem.parallel_ofPDS]
  exact (hQ Pr _ _ (fun _ => rfl) (fun _ => rfl)).symm

/-- Running a fixed typed system `T` to the left gives a distinguisher `S ↦ d(T ∥ S)`, by the
left case through the swap. -/
lemma distinguishers_parallel_right {A B : Interface} (T : TypedSystem A)
    {d : TypedSystem (tensor A B) → ℝ} (hd : d ∈ distinguishers (tensor A B)) :
    (fun S : TypedSystem B => d (TypedSystem.parallel T S)) ∈ distinguishers B := by
  have h := distinguishers_parallel_left T (distinguishers_attach (swap A B).hom hd)
  simpa only [parallel_swap] using h

/-- The systems-level transcript distance is the advantage distance of all compatible
distinguisher behaviors: `Δ(R, S) = ⨆ d, |d R - d S| = advantageDistance (distinguishers A) R S`.
The systems characterization of the selected metric, and its `edist_eq` field. -/
lemma transcriptDistance_eq_advantageDistance {A : Interface} (R S : TypedSystem A) :
    R.1.transcriptDistance S.1 =
      ConstructiveCryptography.advantageDistance (distinguishers A) R S := by
  -- `Δ(R, S) = ⨆ d, Adv_d(R, S)` over compatible stopping distinguisher behaviors.
  rw [RandomSystem.transcriptDistance_eq_iSup_behavior R S]
  -- The advantage distance is the same supremum, indexed through `Set.range`.
  simp only [ConstructiveCryptography.advantageDistance, distinguishers, iSup_range,
    Domain.DistinguisherBehavior.advantage,
    ConstructiveCryptography.Distinguishers.probability]

/-- The selected metric `fibreMetric` is the transcript distance
`TypedSystem.transcriptPseudoEMetricSpace`, and the distinguishers are `distinguishers A`.
Maurer 2011, Lemma 1, printed p. 46: “the pseudo-metric ΔD is compatible with the cryptographic
algebra”. Each non-expansion bound passes through the bridge (`═`,
`transcriptDistance_eq_advantageDistance`) to the bound of `ofClosure` on the advantage
distance `d_𝒟` of `distinguishers`:

```text
Δ(αR, αS)     ═ d_𝒟(αR, αS)     ≤ d_𝒟(R, S)              ═ Δ(R, S)
Δ(R∥S, R'∥S') ═ d_𝒟(R∥S, R'∥S') ≤ d_𝒟(R, R') + d_𝒟(S, S') ═ Δ(R, R') + Δ(S, S')
```
-/
noncomputable instance compatibleDistinguisherClass :
    ConstructiveCryptography.CompatibleDistinguisherClass Interface TypedSystem :=
  -- The closed class of Lemma 1 supplies the closure fields and non-expansion proofs; its
  -- advantage metric is replaced by the transcript metric below.
  let closed := ConstructiveCryptography.CompatibleDistinguisherClass.ofClosure distinguishers
    (fun α _ hd => distinguishers_attach α hd)
    (fun T _ hd => distinguishers_parallel_left T hd)
    (fun T _ hd => distinguishers_parallel_right T hd)
  { closed with
    fibreMetric := TypedSystem.transcriptPseudoEMetricSpace
    edist_smul_le := by
      intro A B α R S
      -- `edist` of the selected metric unfolds to transcript distance.
      change (α • R).1.transcriptDistance (α • S).1 ≤ R.1.transcriptDistance S.1
      -- Both sides become advantage distances; absorbing `α` is Lemma 1's attachment bound.
      rw [transcriptDistance_eq_advantageDistance, transcriptDistance_eq_advantageDistance]
      exact closed.edist_smul_le α R S
    edist_parallel_le := by
      intro A B R R' S S'
      change (TypedSystem.parallel R S).1.transcriptDistance (TypedSystem.parallel R' S').1 ≤
        R.1.transcriptDistance R'.1 + S.1.transcriptDistance S'.1
      -- All three distances become advantage distances; Lemma 1 gives the parallel bound.
      rw [transcriptDistance_eq_advantageDistance, transcriptDistance_eq_advantageDistance,
        transcriptDistance_eq_advantageDistance]
      exact closed.edist_parallel_le R R' S S'
    edist_eq := transcriptDistance_eq_advantageDistance }

lemma cc_parallel_eq {A B : Interface} (R : TypedSystem A) (S : TypedSystem B) :
    ConstructiveCryptography.CryptographicAlgebra.parallel R S =
      TypedSystem.parallel R S := rfl

lemma cc_dummy_eq :
    ConstructiveCryptography.CryptographicAlgebra.dummy = TypedSystem.dummy := rfl

/-- The distance of two typed systems is the transcript distance of their random systems, by
definition: the selected `fibreMetric` is `TypedSystem.transcriptPseudoEMetricSpace`. -/
lemma cc_distance_eq {A : Interface} (R S : TypedSystem A) :
    ConstructiveCryptography.CryptographicAlgebra.distance R S =
      R.1.transcriptDistance S.1 := by
  rfl

section Sampling

open Probability
open scoped SystemAlgebra NNReal

/-- If the components have errors `ε k`, retaining a draw from `P` gives
`Δ (sample P R) (sample P S) ≤ E_P[ε]`. -/
lemma distance_sample_le_expect {A : Interface} {K : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (ε : K → ℝ≥0)
    (bound : ∀ k, Δ (R k) (S k) ≤ (ε k : ENNReal)) :
    Δ (TypedSystem.sample P R) (TypedSystem.sample P S) ≤
      (Real.toNNReal (P.expect (fun k => (ε k : ℝ))) : ENNReal) :=
  TypedSystem.transcriptDistance_sample_le_expect P R S ε bound

/-- A common component bound `ε` also bounds the distance between both retained samples. -/
lemma distance_sample_le {A : Interface} {K : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (R S : K → TypedSystem A) (ε : ℝ≥0)
    (bound : ∀ k, Δ (R k) (S k) ≤ (ε : ENNReal)) :
    Δ (TypedSystem.sample P R) (TypedSystem.sample P S) ≤ (ε : ENNReal) :=
  TypedSystem.transcriptDistance_sample_le P R S ε bound

end Sampling

/-- **An H-coefficient argument bounds the CC distance** of typed systems on `A`:
`distance R S ≤ error`, since that distance is the transcript distance of `R.1` and `S.1`. -/
lemma distance_le_of_hCoefficient {A : Interface} {R S : TypedSystem A} {error : NNReal}
    (w : RandomSystem.HCoefficient R.1 S.1 error) :
    ConstructiveCryptography.CryptographicAlgebra.distance R S ≤ error := by
  -- `distance R S = R.1.transcriptDistance S.1` (`cc_distance_eq`); a typed system replies
  -- at the queried interface (`S.2`).
  rw [cc_distance_eq]
  exact w.transcriptDistance_le_nnreal S.2

/-- Decision advantage is dominated by the transcript distance: every typed decision behavior
`d` has `|d R - d S| ≤ Δ(R, S)`, so the domination law holds for whatever set is admitted. The
metric is the selected transcript metric; nothing is changed or chosen here. -/
noncomputable instance distinguisherAdvantageDominated
    -- `admitted A` is the selected set of typed distinguishers on interface `A`.
    (admitted : ∀ A : Interface, Set (TypedDistinguisher A)) :
    ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.DominatedByDistance
      (ConstructiveCryptography.Distinguishers.distinguisherAdvantage
        (Phi := TypedSystem) admitted) where
  advantage_le_distance d _ R S := by
    rw [cc_distance_eq]
    exact d.advantage_le_transcriptDistance R S

/-- In the monoidal category of interfaces, `projectLeft A B` is
`(ρ_ A).inv ≫ (𝟙 A ⊗ₘ discard B)`. -/
lemma projectLeft_eq
    -- `A` is the retained outside interface; `B` is the hidden parallel component.
    (A B : Interface) :
    (TypedConverter.projectLeft A B : A ⟶ A ⊗ B) =
      (ρ_ A).inv ≫ (𝟙 A ⊗ₘ TypedConverter.discard B) := rfl

/-- In the monoidal category of interfaces, `projectRight A B` is
`(λ_ B).inv ≫ (discard A ⊗ₘ 𝟙 B)`. -/
lemma projectRight_eq
    -- `A` is the hidden parallel component; `B` is the retained outside interface.
    (A B : Interface) :
    (TypedConverter.projectRight A B : B ⟶ A ⊗ B) =
      (λ_ B).inv ≫ (TypedConverter.discard A ⊗ₘ 𝟙 B) := rfl

/-- Projecting the left component of a parallel resource returns `R`. -/
lemma projectLeft_smul_parallel
    -- `R` on `A` is retained; `S` on `B` is discarded.
    {A B : Interface} (R : TypedSystem A) (S : TypedSystem B) :
    TypedConverter.projectLeft A B •
      ConstructiveCryptography.CryptographicAlgebra.parallel R S = R :=
  TypedConverter.projectLeft_smul_parallel R S

/-- Projecting the right component of a parallel resource returns `S`. -/
lemma projectRight_smul_parallel
    -- `R` on `A` is discarded; `S` on `B` is retained.
    {A B : Interface} (R : TypedSystem A) (S : TypedSystem B) :
    TypedConverter.projectRight A B •
      ConstructiveCryptography.CryptographicAlgebra.parallel R S = S :=
  TypedConverter.projectRight_smul_parallel R S

/-- Projecting the left component of a sampled parallel resource preserves the retained draw
`k ← P` and returns `TypedSystem.sample P R`. -/
lemma projectLeft_smul_sample_parallel
    -- `A`, `B` are the ordered component interfaces; `K` carries the shared initial draw.
    {A B : Interface} {K : Type}
    -- `P` is the normalized law drawn once before interaction.
    (P : Probability.Distribution K) [Probability.Distribution.IsProbability P]
    -- `R k` is retained and `S k` is discarded for that draw `k`.
    (R : K → TypedSystem A) (S : K → TypedSystem B) :
    TypedConverter.projectLeft A B • TypedSystem.sample P (fun k =>
      ConstructiveCryptography.CryptographicAlgebra.parallel (R k) (S k)) =
      TypedSystem.sample P R :=
  TypedConverter.projectLeft_smul_sample_parallel P R S

/-- Projecting the right component of a sampled parallel resource preserves the retained draw
`k ← P` and returns `TypedSystem.sample P S`. -/
lemma projectRight_smul_sample_parallel
    -- `A`, `B` are the ordered component interfaces; `K` carries the shared initial draw.
    {A B : Interface} {K : Type}
    -- `P` is the normalized law drawn once before interaction.
    (P : Probability.Distribution K) [Probability.Distribution.IsProbability P]
    -- `R k` is discarded and `S k` is retained for that draw `k`.
    (R : K → TypedSystem A) (S : K → TypedSystem B) :
    TypedConverter.projectRight A B • TypedSystem.sample P (fun k =>
      ConstructiveCryptography.CryptographicAlgebra.parallel (R k) (S k)) =
      TypedSystem.sample P S :=
  TypedConverter.projectRight_smul_sample_parallel P R S

/-- Naturality of `projectLeft` under tensor of arrows:
`projectLeft A B ≫ (α ⊗ₘ β) = α ≫ projectLeft A' B'`. -/
lemma projectLeft_comp_tensor
    -- `A`, `A'` are the retained interfaces of `α`; `B`, `B'` are the hidden interfaces of `β`.
    {A A' B B' : Interface} (α : A ⟶ A') (β : B ⟶ B') :
    (TypedConverter.projectLeft A B : A ⟶ A ⊗ B) ≫ (α ⊗ₘ β) =
      α ≫ (TypedConverter.projectLeft A' B' : A' ⟶ A' ⊗ B') :=
  TypedConverter.projectLeft_comp_parallel α β

/-- Left projection commutes with a converter `α` on the retained component:
`projectLeft A B ≫ (α ⊗ₘ 𝟙 B) = α ≫ projectLeft A' B`. -/
lemma projectLeft_comp_whiskerRight
    -- `A`, `A'` are the outside and inside interfaces of `α`; `B` is the hidden component.
    {A A' B : Interface} (α : A ⟶ A') :
    (TypedConverter.projectLeft A B : A ⟶ A ⊗ B) ≫ (α ⊗ₘ 𝟙 B) =
      α ≫ (TypedConverter.projectLeft A' B : A' ⟶ A' ⊗ B) :=
  TypedConverter.projectLeft_comp_parallel_id α

/-- Naturality of `projectRight` under tensor of arrows:
`projectRight A B ≫ (α ⊗ₘ β) = β ≫ projectRight A' B'`. -/
lemma projectRight_comp_tensor
    -- `A`, `A'` are the hidden interfaces of `α`; `B`, `B'` are the retained interfaces of `β`.
    {A A' B B' : Interface} (α : A ⟶ A') (β : B ⟶ B') :
    (TypedConverter.projectRight A B : B ⟶ A ⊗ B) ≫ (α ⊗ₘ β) =
      β ≫ (TypedConverter.projectRight A' B' : B' ⟶ A' ⊗ B') :=
  TypedConverter.projectRight_comp_parallel α β

/-- Right projection commutes with a converter `β` on the retained component:
`projectRight A B ≫ (𝟙 A ⊗ₘ β) = β ≫ projectRight A B'`. -/
lemma projectRight_comp_whiskerLeft
    -- `A` is the hidden component; `B`, `B'` are the outside and inside interfaces of `β`.
    {A B B' : Interface} (β : B ⟶ B') :
    (TypedConverter.projectRight A B : B ⟶ A ⊗ B) ≫ (𝟙 A ⊗ₘ β) =
      β ≫ (TypedConverter.projectRight A B' : B' ⟶ A ⊗ B') :=
  TypedConverter.projectRight_comp_parallel_id β

/-- Attaching `α ⊗ₘ β` before `projectLeft A B` equals attaching `α` after `projectLeft A' B'`,
for any (possibly correlated) typed system `T` on `A' ⊗ B'`. -/
lemma projectLeft_smul_tensor_smul
    -- `A`, `A'` are the retained interfaces and `B`, `B'` the hidden interfaces.
    {A A' B B' : Interface}
    -- `α` acts on the retained side, `β` on the hidden side, and `T` is any joint system.
    (α : A ⟶ A') (β : B ⟶ B') (T : TypedSystem (A' ⊗ B')) :
    TypedConverter.projectLeft A B • ((α ⊗ₘ β) • T) =
      α • (TypedConverter.projectLeft A' B' • T) :=
  TypedConverter.projectLeft_smul_parallel_smul α β T

/-- Attaching `α ⊗ₘ β` before `projectRight A B` equals attaching `β` after `projectRight A' B'`,
for any (possibly correlated) typed system `T` on `A' ⊗ B'`. -/
lemma projectRight_smul_tensor_smul
    -- `A`, `A'` are the hidden interfaces and `B`, `B'` the retained interfaces.
    {A A' B B' : Interface}
    -- `α` acts on the hidden side, `β` on the retained side, and `T` is any joint system.
    (α : A ⟶ A') (β : B ⟶ B') (T : TypedSystem (A' ⊗ B')) :
    TypedConverter.projectRight A B • ((α ⊗ₘ β) • T) =
      β • (TypedConverter.projectRight A' B' • T) :=
  TypedConverter.projectRight_smul_parallel_smul α β T

end SystemAlgebra.Interface
