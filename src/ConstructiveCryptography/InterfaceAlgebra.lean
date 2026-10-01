import ConstructiveCryptography.ResourceParallelAttachment
import ConstructiveCryptography.ResourceCoherence
import ConstructiveCryptography.InterfaceMonoidal
import ConstructiveCryptography.CryptographicAlgebra.Distinguisher
import RandomSystems.Distance.Distinguisher
import ConstructiveCryptography.Substitution.Reduction

/-!
# Interfaces as a cryptographic algebra

Interfaces are an instance of `ResourceTheory`: the resources on `A` are `Interface.Resource A`,
and attachment is `Interface.attach`, the attachment of PDC behaviors; its axioms are
`Interface.identity_attach` and `Interface.comp_smul`. They are an instance of
`CryptographicAlgebra`: the lax monoidal structure of the resource functor is parallel
composition of resources with the dummy resource. They are an instance of
`CompatibleDistinguisherClass`:
the distinguishers on `A` are the behaviors of the probabilistic distinguishers compatible with
`A`'s domain (`Domain.DistinguisherBehavior`), their probabilities of outputting `1` on
resources. The class is closed under absorbing a converter
(`Domain.DistinguisherBehavior.absorb`) and under running a fixed resource beside
(`Domain.Distinguisher.exists_absorbRight`), so Maurer's Lemma 1
(`CompatibleDistinguisherClass.ofClosure`) makes its advantage distance a compatible
pseudo-metric. This distance of two resources is the transcript distance of their random systems
(`RandomSystem.transcriptDistance_eq_iSup_behavior`). For every class of admitted distinguishers
they carry a `DistinguisherAdvantage`: its field `advantage` is
`Domain.DistinguisherBehavior.advantage`, and its laws are `advantage_self`, `advantage_symm` and
`advantage_triangle` of the random systems. In a security proof a converter absorbed into a
distinguisher is the reduction (CR18); absorbing a serial composition absorbs its converters in
turn.

## Main definitions

* `Interface.resourcesLaxMonoidal`: parallel composition and the dummy resource
* `Interface.distinguishers A`: the behaviors of the probabilistic distinguishers compatible with
  `A`'s domain
* `Interface.resourceTheory`, `Interface.cryptographicAlgebra`,
  `Interface.compatibleDistinguisherClass`: the instances
* `Interface.distinguisherAdvantage admissible`: the distinguishing advantage of the
  substitution calculus, with its field `advantage` the systems-level
  `Domain.DistinguisherBehavior.advantage`
* `Interface.absorb α D`: the distinguisher `D` with the converter `α` absorbed, the systems-level
  `Domain.DistinguisherBehavior.absorb`
* `Interface.AdmissibleDistinguishers`: the class of the admitted distinguishers, closed under
  absorbing converters

## Main results

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
* `Interface.absorb_comp`: absorbing a serial composition absorbs its converters in turn
-/

namespace SystemAlgebra.Interface

open CategoryTheory CategoryTheory.MonoidalCategory

/-- Interfaces carry a resource theory: the resources on `A` are `Resource A`, and
attachment is the attachment of PDC behaviors. -/
noncomputable instance resourceTheory :
    ConstructiveCryptography.ResourceTheory Interface Resource where
  attach := attach
  attach_identity := identity_attach
  attach_serial := comp_smul

noncomputable instance resourcesLaxMonoidal :
    (ConstructiveCryptography.ResourceTheory.functor Interface Resource).LaxMonoidal where
  ε := TypeCat.ofHom fun _ => dummy
  μ A B := TypeCat.ofHom fun (p : Resource A.unop × Resource B.unop) => parallel p.1 p.2
  μ_natural_left f A' := by
    ext p
    have h := (parallel_attach f.unop (𝟙 A'.unop) p.1 p.2).symm
    rw [identity_attach (A := A'.unop) p.2] at h
    exact h
  μ_natural_right A' f := by
    ext p
    have h := (parallel_attach (𝟙 A'.unop) f.unop p.1 p.2).symm
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

/-- Interfaces, converters and resources are a cryptographic algebra. -/
noncomputable instance cryptographicAlgebra :
    ConstructiveCryptography.CryptographicAlgebra Interface Resource where
  laxMonoidal := resourcesLaxMonoidal

/-- The distinguishers on `A`: the behaviors of the probabilistic distinguishers compatible with
`A`'s domain, their probabilities of outputting `1`. -/
def distinguishers (A : Interface) : Set (Resource A → ℝ) :=
  Set.range fun (d : A.inputDomain.DistinguisherBehavior) (R : Resource A) => d.1 R

/-- **A distinguisher with a converter absorbed**: the distinguisher `D ∘ α` on `B`, deciding as
`D` does with `α : A ⟶ B` attached, the systems-level `Domain.DistinguisherBehavior.absorb`. In a
security proof `α` is the reduction. -/
noncomputable def absorb {A B : Interface} (α : A ⟶ B) (D : A.inputDomain.DistinguisherBehavior) :
    B.inputDomain.DistinguisherBehavior :=
  D.absorb B.nonempty_prefix A.nonempty_prefix α

/-- **Absorbing a serial composition** absorbs its converters in turn:
`D ∘ (α ≫ β) = (D ∘ α) ∘ β`. -/
theorem absorb_comp {A B C : Interface} (α : A ⟶ B) (β : B ⟶ C)
    (D : A.inputDomain.DistinguisherBehavior) : absorb (α ≫ β) D = absorb β (absorb α D) :=
  D.absorb_comp C.nonempty_prefix A.nonempty_prefix B.nonempty_prefix α β

/-- Absorbing a converter into a distinguisher gives a distinguisher. -/
theorem distinguishers_attach {A B : Interface} (α : A ⟶ B) {d : Resource A → ℝ}
    (hd : d ∈ distinguishers A) : (fun R : Resource B => d (α • R)) ∈ distinguishers B := by
  obtain ⟨D, rfl⟩ := hd
  exact ⟨absorb α D, rfl⟩

/-- Running a fixed resource beside the distinguished one gives a distinguisher. -/
theorem distinguishers_parallel_left {A B : Interface} (T : Resource B)
    {d : Resource (tensor A B) → ℝ} (hd : d ∈ distinguishers (tensor A B)) :
    (fun R : Resource A => d (parallel R T)) ∈ distinguishers A := by
  obtain ⟨D, rfl⟩ := hd
  obtain ⟨P, hP⟩ := D.2
  obtain ⟨U, rfl⟩ := T.exists_ofPDS
  obtain ⟨Q, hQ⟩ := Domain.Distinguisher.exists_absorbRight (X₁ := A.X) (Y₁ := A.Y)
    (X₂ := B.X) (Y₂ := B.Y) (hE := A.length_le) (hF := B.length_le)
    A.nonempty_prefix B.nonempty_prefix P U
  refine ⟨⟨fun R => D.1 (parallel R (Resource.ofPDS U)), Q, fun R => ?_⟩, rfl⟩
  obtain ⟨Pr, rfl⟩ := Resource.exists_ofPDS R
  refine (hP (parallel (Resource.ofPDS Pr) (Resource.ofPDS U))).trans ?_
  rw [parallel_ofPDS]
  exact (hQ Pr _ _ (fun _ => rfl) (fun _ => rfl)).symm

theorem distinguishers_parallel_right {A B : Interface} (T : Resource A)
    {d : Resource (tensor A B) → ℝ} (hd : d ∈ distinguishers (tensor A B)) :
    (fun S : Resource B => d (parallel T S)) ∈ distinguishers B := by
  have h := distinguishers_parallel_left T (distinguishers_attach (swap A B).hom hd)
  simpa only [parallel_swap] using h

/-- The distinguishers are a compatible distinguisher class; by Maurer's Lemma 1 their
advantage distance is a compatible pseudo-metric. -/
noncomputable instance compatibleDistinguisherClass :
    ConstructiveCryptography.CompatibleDistinguisherClass Interface Resource :=
  ConstructiveCryptography.CompatibleDistinguisherClass.ofClosure distinguishers
    (fun α _ hd => distinguishers_attach α hd)
    (fun T _ hd => distinguishers_parallel_left T hd)
    (fun T _ hd => distinguishers_parallel_right T hd)

theorem cc_parallel_eq {A B : Interface} (R : Resource A) (S : Resource B) :
    ConstructiveCryptography.CryptographicAlgebra.parallel R S =
      parallel R S := rfl

theorem cc_dummy_eq :
    ConstructiveCryptography.CryptographicAlgebra.dummy = dummy := rfl

/-- The distance of two resources is the transcript distance of their random systems. -/
theorem cc_distance_eq {A : Interface} (R S : Resource A) :
    ConstructiveCryptography.CryptographicAlgebra.distance R S =
      R.1.transcriptDistance S.1 := by
  rw [RandomSystem.transcriptDistance_eq_iSup_behavior R S]
  change ConstructiveCryptography.advantageDistance (distinguishers A) R S = _
  simp only [ConstructiveCryptography.advantageDistance, distinguishers, iSup_range,
    Domain.DistinguisherBehavior.advantage]

/-- Interfaces carry a distinguishing advantage for every class `admissible` of admitted
distinguishers: the distinguishers on `A` are the behaviors of the probabilistic distinguishers
compatible with `A`'s domain, and the advantage between two resources is their advantage between
the random systems. -/
noncomputable def distinguisherAdvantage
    (admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior) :
    ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage Interface Resource
      fun A => A.inputDomain.DistinguisherBehavior where
  admissible := admissible
  advantage _ D R S := D.advantage R S
  advantage_self _ D R := D.advantage_self R
  advantage_symm _ D R S := D.advantage_symm R S
  advantage_triangle _ D R S T := D.advantage_triangle R S T

/-- The advantage of a distinguisher between two attachments is the advantage of the
distinguisher with the converter absorbed. -/
theorem distinguisherAdvantage_attach
    (admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior) {A B : Interface}
    (α : A ⟶ B) (D : A.inputDomain.DistinguisherBehavior) (R S : Resource B) :
    (distinguisherAdvantage admissible).advantage A D (α • R) (α • S) =
      (distinguisherAdvantage admissible).advantage B (absorb α D) R S :=
  rfl

/-- **A concrete substitution through a converter**: its loss is the loss at the distinguisher
with the converter absorbed (Banfi 2023, §2.3.3, printed p. 16: `ε'(D) := ε(D ∘ ρ)`), when the
admitted distinguishers are closed under absorbing converters. -/
theorem substitutesWithin_attach
    (admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior)
    (closed : ∀ {A B : Interface} (α : A ⟶ B) (D : A.inputDomain.DistinguisherBehavior),
      D ∈ admissible A → absorb α D ∈ admissible B)
    {A B : Interface} (α : A ⟶ B) {error : B.inputDomain.DistinguisherBehavior → ENNReal}
    {R S : Resource B} (h : (distinguisherAdvantage admissible).SubstitutesWithin error R S) :
    (distinguisherAdvantage admissible).SubstitutesWithin (fun D => error (absorb α D))
      (α • R) (α • S) :=
  ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.attach _ α
    (absorb α) (fun D hD => closed α D hD) (distinguisherAdvantage_attach admissible α) h

/-- **The admitted distinguishers**: a class of distinguishers at every interface, closed under
absorbing converters. Security statements are substitutions for their distinguishing
advantage, written `R ≃[ε] S`. -/
class AdmissibleDistinguishers where
  /-- The admitted distinguishers at each interface. -/
  admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior
  /-- An admitted distinguisher with a converter absorbed is admitted. -/
  closed : ∀ {A B : Interface} (α : A ⟶ B) (D : A.inputDomain.DistinguisherBehavior),
    D ∈ admissible A → absorb α D ∈ admissible B

/-- **A substitution through a converter**, for the admitted distinguishers: its loss is the loss
at the distinguisher with the converter absorbed. -/
theorem AdmissibleDistinguishers.substitutesWithin_attach [AdmissibleDistinguishers]
    {A B : Interface} (α : A ⟶ B) {error : B.inputDomain.DistinguisherBehavior → ENNReal}
    {R S : Resource B}
    (h : (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin error R S) :
    (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin
      (fun D => error (absorb α D)) (α • R) (α • S) :=
  Interface.substitutesWithin_attach _ AdmissibleDistinguishers.closed α h

/-- **A substitution in a context** (Banfi 2023, §2.3.3, printed p. 16: `ε(D ∘ ρ)`): substituting
`S` for `R` inside the context `ρ` loses the error at the distinguisher with `ρ` absorbed. The
context may be a serial composition; its attachments `X` and `Y` are written converter by
converter. -/
theorem AdmissibleDistinguishers.substitutesWithin_context [AdmissibleDistinguishers]
    {A B : Interface} (ρ : A ⟶ B) {error : B.inputDomain.DistinguisherBehavior → ENNReal}
    {R S : Resource B}
    (h : (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin error R S)
    {X Y : Resource A}
    (hX : ρ • R = X := by first | rfl | (simp only [SystemAlgebra.Interface.comp_smul] <;> rfl))
    (hY : ρ • S = Y := by first | rfl | (simp only [SystemAlgebra.Interface.comp_smul] <;> rfl)) :
    (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin
      (error ∘ absorb ρ) X Y := by
  subst hX hY
  exact AdmissibleDistinguishers.substitutesWithin_attach ρ h

/-- The advantage of a distinguisher is at most the distance. -/
theorem distinguisherAdvantage_le_distance
    (admissible : ∀ A : Interface, Set A.inputDomain.DistinguisherBehavior) {A : Interface}
    (D : A.inputDomain.DistinguisherBehavior) (R S : Resource A) :
    (distinguisherAdvantage admissible).advantage A D R S ≤
      ConstructiveCryptography.CryptographicAlgebra.distance R S := by
  rw [cc_distance_eq]
  exact D.advantage_le_transcriptDistance R S

end SystemAlgebra.Interface
