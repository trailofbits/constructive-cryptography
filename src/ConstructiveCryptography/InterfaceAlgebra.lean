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
the distinguishers on `A` are the probabilistic distinguishers compatible with `A`'s domain
(`Domain.Distinguisher`), evaluated on resources by their probability of outputting `1`.
The class is closed under absorbing a converter (`Domain.Distinguisher.exists_absorbAll`)
and under running a fixed resource beside (`Domain.Distinguisher.exists_absorbRight`), so
Maurer's Lemma 1 (`CompatibleDistinguisherClass.ofClosure`) makes its advantage distance a
compatible pseudo-metric. This distance of two resources is the transcript distance of
their random systems (`RandomSystem.transcriptDistance_eq_iSup`). For every class of admitted
distinguishers they carry a `DistinguisherAdvantage`: its field `advantage` is
`Domain.Distinguisher.advantage`, and its laws are `advantage_self`, `advantage_symm` and
`advantage_triangle` of the random systems.

## Main definitions

* `Interface.resourcesLaxMonoidal`: parallel composition and the dummy resource
* `Interface.distinguishers A`: the probabilities of outputting `1` of the probabilistic
  distinguishers compatible with `A`'s domain
* `Interface.resourceTheory`, `Interface.cryptographicAlgebra`,
  `Interface.compatibleDistinguisherClass`: the instances
* `Interface.distinguisherAdvantage admissible`: the distinguishing advantage of the
  substitution calculus, with its field `advantage` the systems-level
  `Domain.Distinguisher.advantage`
* `Interface.reduction α P`: a distinguisher through a converter, the systems-level
  `Domain.Distinguisher.absorb`
* `Interface.AdmissibleDistinguishers`: the class of the admitted distinguishers, closed under
  reduction

## Main results

* `Interface.distinguishers_attach`, `Interface.distinguishers_parallel_left`,
  `Interface.distinguishers_parallel_right`: closure
* `Interface.cc_parallel_eq`, `Interface.cc_dummy_eq`: the abstract operations are the
  concrete ones
* `Interface.cc_distance_eq`: the distance is the transcript distance of the random systems
* `Interface.distinguisherAdvantage_le_distance`: an advantage is at most the distance
* `Interface.distinguisherAdvantage_attach`, `Interface.substitutesWithin_attach`: an advantage
  between attachments is the advantage of the reduction, and a concrete substitution transports
  through a converter; `Interface.AdmissibleDistinguishers.substitutesWithin_attach` for the
  admitted distinguishers
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

/-- The distinguishers on `A`: the probabilities of outputting `1` of the probabilistic
distinguishers compatible with `A`'s domain. -/
def distinguishers (A : Interface) : Set (Resource A → ℝ) :=
  Set.range fun (P : A.inputDomain.Distinguisher) (R : Resource A) => P.probability R.1

/-- Absorbing a converter into a distinguisher gives a distinguisher. -/
theorem distinguishers_attach {A B : Interface} (α : A ⟶ B) {d : Resource A → ℝ}
    (hd : d ∈ distinguishers A) : (fun R : Resource B => d (α • R)) ∈ distinguishers B := by
  obtain ⟨P, rfl⟩ := hd
  obtain ⟨Q, hQ⟩ :=
    Domain.Distinguisher.exists_absorbAll B.nonempty_prefix A.nonempty_prefix α P
  exact ⟨Q, funext fun R => hQ R.1 R.2⟩

/-- Running a fixed resource beside the distinguished one gives a distinguisher. -/
theorem distinguishers_parallel_left {A B : Interface} (T : Resource B)
    {d : Resource (tensor A B) → ℝ} (hd : d ∈ distinguishers (tensor A B)) :
    (fun R : Resource A => d (parallel R T)) ∈ distinguishers A := by
  obtain ⟨P, rfl⟩ := hd
  obtain ⟨U, rfl⟩ := T.exists_ofPDS
  obtain ⟨Q, hQ⟩ := Domain.Distinguisher.exists_absorbRight (X₁ := A.X) (Y₁ := A.Y)
    (X₂ := B.X) (Y₂ := B.Y) (hE := A.length_le) (hF := B.length_le)
    A.nonempty_prefix B.nonempty_prefix P U
  refine ⟨Q, funext fun R => ?_⟩
  obtain ⟨Pr, rfl⟩ := R.exists_ofPDS
  dsimp only
  rw [parallel_ofPDS]
  exact hQ Pr _ _ (fun _ => rfl) (fun _ => rfl)

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
  rw [RandomSystem.transcriptDistance_eq_iSup R.2 S.2]
  change ConstructiveCryptography.advantageDistance (distinguishers A) R S = _
  simp only [ConstructiveCryptography.advantageDistance, distinguishers, iSup_range,
    Domain.Distinguisher.advantage]

/-- Interfaces carry a distinguishing advantage for every class `admissible` of admitted
distinguishers: the distinguishers on `A` are the probabilistic distinguishers compatible with
`A`'s domain, and the advantage between two resources is their advantage between the random
systems. -/
noncomputable def distinguisherAdvantage (admissible : ∀ A : Interface, Set A.inputDomain.Distinguisher) :
    ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage Interface Resource
      fun A => A.inputDomain.Distinguisher where
  admissible := admissible
  advantage _ P R S := P.advantage R.1 S.1
  advantage_self _ P R := P.advantage_self R.1
  advantage_symm _ P R S := P.advantage_symm R.1 S.1
  advantage_triangle _ P R S T := P.advantage_triangle R.1 S.1 T.1

/-- The reduction of a distinguisher on `A` through a converter `α : A ⟶ B`: the systems-level
distinguisher with `α` absorbed. -/
noncomputable def reduction {A B : Interface} (α : A ⟶ B) (P : A.inputDomain.Distinguisher) :
    B.inputDomain.Distinguisher :=
  P.absorb B.nonempty_prefix A.nonempty_prefix α

/-- The advantage of a distinguisher between two attachments is the advantage of its reduction. -/
theorem distinguisherAdvantage_attach
    (admissible : ∀ A : Interface, Set A.inputDomain.Distinguisher) {A B : Interface}
    (α : A ⟶ B) (P : A.inputDomain.Distinguisher) (R S : Resource B) :
    (distinguisherAdvantage admissible).advantage A P (α • R) (α • S) =
      (distinguisherAdvantage admissible).advantage B (reduction α P) R S := by
  simp only [distinguisherAdvantage, Domain.Distinguisher.advantage, reduction,
    Domain.Distinguisher.probability_absorb _ _ α P _ R.2,
    Domain.Distinguisher.probability_absorb _ _ α P _ S.2]
  rfl

/-- **A concrete substitution through a converter**: its loss is the loss at the reduced
distinguisher (Banfi 2023, §2.3.3, printed p. 16: `ε'(D) := ε(D ∘ ρ)`), when the admitted
distinguishers are closed under reduction. -/
theorem substitutesWithin_attach
    (admissible : ∀ A : Interface, Set A.inputDomain.Distinguisher)
    (closed : ∀ {A B : Interface} (α : A ⟶ B) (P : A.inputDomain.Distinguisher),
      P ∈ admissible A → reduction α P ∈ admissible B)
    {A B : Interface} (α : A ⟶ B) {error : B.inputDomain.Distinguisher → ENNReal}
    {R S : Resource B} (h : (distinguisherAdvantage admissible).SubstitutesWithin error R S) :
    (distinguisherAdvantage admissible).SubstitutesWithin (fun P => error (reduction α P))
      (α • R) (α • S) :=
  ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.attach _ α
    (reduction α) (fun P hP => closed α P hP) (distinguisherAdvantage_attach admissible α) h

/-- **The admitted distinguishers**: a class of distinguishers at every interface, closed under
reduction through converters. Security statements are substitutions for their distinguishing
advantage, written `R ≃[ε] S`. -/
class AdmissibleDistinguishers where
  /-- The admitted distinguishers at each interface. -/
  admissible : ∀ A : Interface, Set A.inputDomain.Distinguisher
  /-- The reduction of an admitted distinguisher through a converter is admitted. -/
  closed : ∀ {A B : Interface} (α : A ⟶ B) (P : A.inputDomain.Distinguisher),
    P ∈ admissible A → reduction α P ∈ admissible B

/-- **A substitution through a converter**, for the admitted distinguishers: its loss is the loss
at the reduced distinguisher. -/
theorem AdmissibleDistinguishers.substitutesWithin_attach [AdmissibleDistinguishers]
    {A B : Interface} (α : A ⟶ B) {error : B.inputDomain.Distinguisher → ENNReal}
    {R S : Resource B}
    (h : (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin error R S) :
    (distinguisherAdvantage AdmissibleDistinguishers.admissible).SubstitutesWithin
      (fun P => error (reduction α P)) (α • R) (α • S) :=
  Interface.substitutesWithin_attach _ AdmissibleDistinguishers.closed α h

/-- The advantage of a distinguisher is at most the distance. -/
theorem distinguisherAdvantage_le_distance
    (admissible : ∀ A : Interface, Set A.inputDomain.Distinguisher) {A : Interface}
    (P : A.inputDomain.Distinguisher) (R S : Resource A) :
    (distinguisherAdvantage admissible).advantage A P R S ≤
      ConstructiveCryptography.CryptographicAlgebra.distance R S := by
  rw [cc_distance_eq]
  exact P.advantage_le_transcriptDistance R.2 S.2

end SystemAlgebra.Interface
