import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Typed.ParallelAttachment
import RandomSystems.Typed.SystemCoherence
import ConstructiveCryptography.InterfaceMonoidal
import ConstructiveCryptography.CryptographicAlgebra.Distinguisher
import RandomSystems.Distance.Distinguisher
import ConstructiveCryptography.Substitution.Reduction

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
distinguishers on `A` are the behaviors of the probabilistic distinguishers compatible with `A`'s
domain (`Domain.DistinguisherBehavior`), their probabilities of outputting `1` on typed systems.
The axiom `closed_attach` is discharged by `Domain.DistinguisherBehavior.absorb`, and
`closed_parallel_left` and `closed_parallel_right` by `Domain.Distinguisher.exists_absorbRight`
and the swap (`TypedSystem.parallel_swap_mass`), so Maurer's Lemma 1
(`CompatibleDistinguisherClass.ofClosure`) makes its advantage distance a compatible
pseudo-metric. This distance of two typed systems is the transcript distance of their random
systems (`RandomSystem.transcriptDistance_eq_iSup_behavior`). For every class of admitted
distinguishers they carry a `DistinguisherAdvantage`: its field `advantage` is
`Domain.DistinguisherBehavior.advantage`, and its laws are `advantage_self`, `advantage_symm` and
`advantage_triangle` of the random systems. In a security proof a converter absorbed into a
distinguisher (`Domain.DistinguisherBehavior.absorb`) is the reduction (CR18).

## Main definitions

* `Interface.resourcesLaxMonoidal`: parallel composition and the dummy system
* `Interface.distinguishers A`: the behaviors of the probabilistic distinguishers compatible with
  `A`'s domain
* `Interface.resourceTheory`, `Interface.cryptographicAlgebra`,
  `Interface.compatibleDistinguisherClass`: the instances
* `Interface.distinguisherAdvantage admissible`: the distinguishing advantage of the
  substitution calculus, with its field `advantage` the systems-level
  `Domain.DistinguisherBehavior.advantage`
* `Interface.AdmissibleDistinguishers`: the class of the admitted distinguishers, closed under
  absorbing converters

## Main results

* `Interface.parallel_assoc`, `Interface.parallel_dummy_left`, `Interface.parallel_dummy_right`:
  the lax monoidal laws through the regrouping isomorphisms
* `Interface.parallel_swap`: parallel composition is commutative through the swap
* `Interface.distinguishers_attach`, `Interface.distinguishers_parallel_left`,
  `Interface.distinguishers_parallel_right`: closure
* `Interface.cc_parallel_eq`, `Interface.cc_dummy_eq`: the abstract operations are the
  concrete ones
* `Interface.cc_distance_eq`: the distance is the transcript distance of the random systems
* `Interface.distinguisherAdvantage_le_distance`: an advantage is at most the distance
* `Interface.distinguisherAdvantage_attach`, `Interface.substitutesWithin_attach`: an advantage
  between attachments is the advantage with the converter absorbed, and a concrete substitution
  transports through a converter; `Interface.AdmissibleDistinguishers.substitutesWithin_attach`
  for the admitted distinguishers, and
  `Interface.AdmissibleDistinguishers.substitutesWithin_context` in a composite context
-/

namespace SystemAlgebra.Interface

open CategoryTheory CategoryTheory.MonoidalCategory

/-- Interfaces are an instance of `ResourceTheory`: its carrier on `A` is `TypedSystem A`, and
attachment is the attachment of PDC behaviors. -/
noncomputable instance resourceTheory :
    ConstructiveCryptography.ResourceTheory Interface TypedSystem where
  attach := TypedConverter.attach
  attach_identity := TypedConverter.identity_attach
  attach_serial := TypedConverter.comp_smul

/-- The selected CC instance's attachment field is the direct typed action.
This is a representation equality for `resourceTheory`, not a law about an arbitrary
resource theory or a choice of another action on typed systems. -/
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
    ((leftUnitor A).inv • TypedSystem.parallel TypedSystem.dummy R : TypedSystem A) = R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  simp only [leftUnitor, isoOf]
  rw [TypedConverter.rename_mass, TypedSystem.parallel_unit_left_mass]
  simp only [← Equiv.prodCongr_symm, List.map_map, Equiv.self_comp_symm, List.map_id]

lemma parallel_dummy_right {A : Interface} (R : TypedSystem A) :
    ((rightUnitor A).inv • TypedSystem.parallel R TypedSystem.dummy : TypedSystem A) = R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  simp only [rightUnitor, isoOf]
  rw [TypedConverter.rename_mass, TypedSystem.parallel_unit_right_mass]
  simp only [← Equiv.prodCongr_symm, List.map_map, Equiv.self_comp_symm, List.map_id]

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

/-- The distinguishers on `A`: the behaviors of the probabilistic distinguishers compatible with
`A`'s domain, their probabilities of outputting `1`. -/
def distinguishers (A : Interface) : Set (TypedSystem A → ℝ) :=
  Set.range fun (d : A.inputDomain.DistinguisherBehavior) (R : TypedSystem A) => d.1 R

/-- Absorbing a converter into a distinguisher gives a distinguisher. -/
lemma distinguishers_attach {A B : Interface} (α : A ⟶ B) {d : TypedSystem A → ℝ}
    (hd : d ∈ distinguishers A) : (fun R : TypedSystem B => d (α • R)) ∈ distinguishers B := by
  obtain ⟨D, rfl⟩ := hd
  exact ⟨D.absorb B.nonempty_prefix A.nonempty_prefix α, rfl⟩

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

lemma distinguishers_parallel_right {A B : Interface} (T : TypedSystem A)
    {d : TypedSystem (tensor A B) → ℝ} (hd : d ∈ distinguishers (tensor A B)) :
    (fun S : TypedSystem B => d (TypedSystem.parallel T S)) ∈ distinguishers B := by
  have h := distinguishers_parallel_left T (distinguishers_attach (swap A B).hom hd)
  simpa only [parallel_swap] using h

/-- The distinguishers are a compatible distinguisher class; by Maurer's Lemma 1 their
advantage distance is a compatible pseudo-metric. -/
noncomputable instance compatibleDistinguisherClass :
    ConstructiveCryptography.CompatibleDistinguisherClass Interface TypedSystem :=
  ConstructiveCryptography.CompatibleDistinguisherClass.ofClosure distinguishers
    (fun α _ hd => distinguishers_attach α hd)
    (fun T _ hd => distinguishers_parallel_left T hd)
    (fun T _ hd => distinguishers_parallel_right T hd)

lemma cc_parallel_eq {A B : Interface} (R : TypedSystem A) (S : TypedSystem B) :
    ConstructiveCryptography.CryptographicAlgebra.parallel R S =
      TypedSystem.parallel R S := rfl

lemma cc_dummy_eq :
    ConstructiveCryptography.CryptographicAlgebra.dummy = TypedSystem.dummy := rfl

/-- The distance of two typed systems is the transcript distance of their random systems. -/
lemma cc_distance_eq {A : Interface} (R S : TypedSystem A) :
    ConstructiveCryptography.CryptographicAlgebra.distance R S =
      R.1.transcriptDistance S.1 := by
  rw [RandomSystem.transcriptDistance_eq_iSup_behavior R S]
  change ConstructiveCryptography.advantageDistance (distinguishers A) R S = _
  simp only [ConstructiveCryptography.advantageDistance, distinguishers, iSup_range,
    Domain.DistinguisherBehavior.advantage]

/-- A revealed-transcript H-coefficient argument bounds the existing interface distance. -/
lemma distance_le_of_hCoefficient {A : Interface} {R S : TypedSystem A} {error : NNReal}
    (w : RandomSystem.HCoefficient R.1 S.1 error) :
    ConstructiveCryptography.CryptographicAlgebra.distance R S ≤ error := by
  -- The interface instance uses precisely the cumulative systems' transcript distance.
  rw [cc_distance_eq]
  exact w.transcriptDistance_le_nnreal S.2

/-- Interfaces carry a distinguishing advantage for every class `admissible` of admitted
distinguishers: the distinguishers on `A` are the behaviors of the probabilistic distinguishers
compatible with `A`'s domain, and the advantage between two typed systems is their advantage
between the random systems. -/
noncomputable def distinguisherAdvantage
    (admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior) :
    ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage Interface TypedSystem
      fun A => A.inputDomain.DistinguisherBehavior where
  admissible := admissible
  advantage _ D R S := D.advantage R S
  advantage_self _ D R := D.advantage_self R
  advantage_symm _ D R S := D.advantage_symm R S
  advantage_triangle _ D R S T := D.advantage_triangle R S T

/-- The advantage of a distinguisher between two attachments is the advantage of the
distinguisher with the converter absorbed. -/
lemma distinguisherAdvantage_attach
    (admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior) {A B : Interface}
    (α : A ⟶ B) (D : A.inputDomain.DistinguisherBehavior) (R S : TypedSystem B) :
    (distinguisherAdvantage admissible).advantage A D (α • R) (α • S) =
      (distinguisherAdvantage admissible).advantage B
        (D.absorb B.nonempty_prefix A.nonempty_prefix α) R S :=
  rfl

/-- **A concrete substitution through a converter**: its loss is the loss at the distinguisher
with the converter absorbed (Banfi 2023, §2.3.3, printed p. 16: `ε'(D) := ε(D ∘ ρ)`), when the
admitted distinguishers are closed under absorbing converters. -/
lemma substitutesWithin_attach
    (admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior)
    (closed : ∀ {A B : Interface} (α : A ⟶ B) (D : A.inputDomain.DistinguisherBehavior),
      D ∈ admissible A → D.absorb B.nonempty_prefix A.nonempty_prefix α ∈ admissible B)
    {A B : Interface} (α : A ⟶ B) {error : B.inputDomain.DistinguisherBehavior → ENNReal}
    {R S : TypedSystem B} (h : (distinguisherAdvantage admissible).SubstitutesWithin error R S) :
    (distinguisherAdvantage admissible).SubstitutesWithin
      (fun D => error (D.absorb B.nonempty_prefix A.nonempty_prefix α)) (α • R) (α • S) :=
  ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.attach _ α
    (fun D => D.absorb B.nonempty_prefix A.nonempty_prefix α) (fun D hD => closed α D hD)
    (distinguisherAdvantage_attach admissible α) h

/-- **The admitted distinguishers**: a class of distinguishers at every interface, closed under
absorbing converters. Security statements are substitutions for their distinguishing
advantage, written `R ≃[ε] S`. -/
class AdmissibleDistinguishers where
  /-- The admitted distinguishers at each interface. -/
  admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior
  /-- An admitted distinguisher with a converter absorbed is admitted. -/
  closed : ∀ {A B : Interface} (α : A ⟶ B) (D : A.inputDomain.DistinguisherBehavior),
    D ∈ admissible A → D.absorb B.nonempty_prefix A.nonempty_prefix α ∈ admissible B

/-- **A substitution through a converter**, for the admitted distinguishers: its loss is the loss
at the distinguisher with the converter absorbed. -/
lemma AdmissibleDistinguishers.substitutesWithin_attach [AdmissibleDistinguishers]
    {A B : Interface} (α : A ⟶ B) {error : B.inputDomain.DistinguisherBehavior → ENNReal}
    {R S : TypedSystem B}
    (h : (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin error R S) :
    (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin
      (fun D => error (D.absorb B.nonempty_prefix A.nonempty_prefix α)) (α • R) (α • S) :=
  Interface.substitutesWithin_attach _ AdmissibleDistinguishers.closed α h

/-- **A substitution in a context** (Banfi 2023, §2.3.3, printed p. 16: `ε(D ∘ ρ)`): substituting
`S` for `R` inside the context `ρ` loses the error at the distinguisher with `ρ` absorbed. The
context may be a serial composition; its attachments `X` and `Y` are written converter by
converter. -/
lemma AdmissibleDistinguishers.substitutesWithin_context [AdmissibleDistinguishers]
    {A B : Interface} (ρ : A ⟶ B) {error : B.inputDomain.DistinguisherBehavior → ENNReal}
    {R S : TypedSystem B}
    (h : (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin error R S)
    {X Y : TypedSystem A}
    (hX : ρ • R = X := by first | rfl | (simp only [SystemAlgebra.Interface.comp_smul] <;> rfl))
    (hY : ρ • S = Y := by first | rfl | (simp only [SystemAlgebra.Interface.comp_smul] <;> rfl)) :
    (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin
      (fun D => error (D.absorb B.nonempty_prefix A.nonempty_prefix ρ)) X Y := by
  subst hX hY
  exact AdmissibleDistinguishers.substitutesWithin_attach ρ h

/-- The advantage of a distinguisher is at most the distance. -/
lemma distinguisherAdvantage_le_distance
    (admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior) {A : Interface}
    (D : A.inputDomain.DistinguisherBehavior) (R S : TypedSystem A) :
    (distinguisherAdvantage admissible).advantage A D R S ≤
      ConstructiveCryptography.CryptographicAlgebra.distance R S := by
  rw [cc_distance_eq]
  exact D.advantage_le_transcriptDistance R S

end SystemAlgebra.Interface
