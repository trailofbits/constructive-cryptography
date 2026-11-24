module

public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Substitution.StructuredHybrid
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Tests for structured distinguishers and uniform-index telescoping hybrids

Exercises:
1. Concrete `StructuredDistinguisher` API: `transcriptLaw_bind`, `IsNonAdaptive.uniformChoice`,
   `sampleFixedQuery_isNonAdaptive`, `toTyped_absorb`, `structuredDistinguisherAdvantage`, and
   `DominatedByDistance` in `cc_calc mixed`.
2. 0-inclusive finite hybrid chains (`SubstitutesWithin.chain`) on `DistinguisherAdvantage`.
3. Signed-gap averaging and uniform-index telescoping hybrids both abstractly on
   `Distinguishers`/`AdmissibleDistinguishers` and concretely via
   `StructuredDistinguisher.uniformChoice`.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.StructuredHybrid

open CategoryTheory ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra Probability
open scoped SystemAlgebra

/-- A single-port Boolean query interface allowing at most one query. -/
abbrev boolInterface : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

/-- Nonadaptive one-query test asking `()` and returning the system's Boolean reply. -/
noncomputable def queryTest : StructuredDistinguisher boolInterface :=
  StructuredDistinguisher.fixedQuery boolInterface [⟨(), ()⟩]
    (Or.inr ⟨List.cons_ne_nil _ _, le_refl 1⟩)
    (fun replies => match replies with
      | [⟨(), b⟩] => b
      | _ => false)

/-- `queryTest` is nonadaptive, and uniform-index sampling preserves nonadaptivity. -/
lemma uniformChoice_nonadaptive :
    (StructuredDistinguisher.uniformChoice (L := 3) (by omega)
      (fun _ => queryTest)).IsNonAdaptive :=
  StructuredDistinguisher.IsNonAdaptive.uniformChoice (by omega) _
    (fun _ => StructuredDistinguisher.fixedQuery_isNonAdaptive _ _ _ _)

/-- Sampled fixed-query tests remain nonadaptive on a single-label interface. -/
lemma sampleFixedQuery_nonadaptive :
    (StructuredDistinguisher.sampleFixedQuery boolInterface 𝒰[Bool]
      (fun _ => [⟨(), ()⟩])
      (fun _ => Or.inr ⟨List.cons_ne_nil _ _, le_refl 1⟩)
      (fun b replies => match replies with
        | [⟨(), r⟩] => xor b r
        | _ => false)).IsNonAdaptive :=
  StructuredDistinguisher.sampleFixedQuery_isNonAdaptive _ _ _ _ _

/-- Concrete `StructuredDistinguisher.absorb` matches `TypedDistinguisher.absorb`. -/
lemma absorb_compatible {A B : Interface} (D : StructuredDistinguisher A)
    (α : TypedConverter A B) :
    (D.absorb α).toTyped = D.toTyped.absorb α :=
  D.toTyped_absorb α

/-- `transcriptLaw_bind` preserves transcript laws under finite mixtures. -/
lemma transcriptLaw_uniform_eq (R : TypedSystem boolInterface) :
    Domain.Distinguisher.transcriptLaw (𝒰[Bool].bind (fun _ => queryTest)) R =
      𝒰[Bool].bind (fun _ => Domain.Distinguisher.transcriptLaw queryTest R) :=
  StructuredDistinguisher.transcriptLaw_bind _ _ R

/-- `structuredDistinguisherAdvantage` works with `cc_normalize`,
`structuredSubstitutesWithin_attach`, and `cc_calc mixed` via `DominatedByDistance`. -/
lemma structured_mixed_calc
    (admitted : ∀ A : Interface, Set (StructuredDistinguisher A))
    {A B D : Interface} (α : A ⟶ B) (β : B ⟶ D) {R S T : TypedSystem D}
    {loss : StructuredDistinguisher D → ENNReal} {ε : ENNReal}
    (hclosed : ∀ P ∈ admitted A, P.absorb (α ≫ β) ∈ admitted D)
    (hcomp : (Interface.structuredDistinguisherAdvantage admitted).SubstitutesWithin loss R S)
    (hstat : Δ S T ≤ ε) :
    (Interface.structuredDistinguisherAdvantage admitted).SubstitutesWithin
      (fun P => loss (P.absorb (α ≫ β)) + ε) (α • (β • R)) ((α ≫ β) • T) := by
  have hattach := Interface.structuredSubstitutesWithin_attach admitted (α ≫ β) hclosed hcomp
  cc_calc mixed
    α • (β • R) = (α ≫ β) • R := by cc_normalize
    _ ≃[fun P => loss (P.absorb (α ≫ β))] (α ≫ β) • S := hattach
    _ ≈[ε] (α ≫ β) • T := hstat

/-- `Interface.structuredAdvantage_le_distance` bounds advantage directly by `Δ`. -/
lemma structured_advantage_le_distance {A : Interface} (D : StructuredDistinguisher A)
    (R S : TypedSystem A) :
    D.advantage R S ≤ Δ R S :=
  Interface.structuredAdvantage_le_distance D R S

/-- 0-step `SubstitutesWithin.chain` holds trivially with zero error. -/
lemma chain_zero_check {C : Type} {Systems D : C → Type}
    (model : DistinguisherAdvantage C Systems D) {A : C} (H : Fin 1 → Systems A) :
    model.SubstitutesWithin (fun d => ∑ _ : Fin 0, (fun _ => (0 : ENNReal)) d)
      (H 0) (H (Fin.last 0)) :=
  DistinguisherAdvantage.SubstitutesWithin.chain model H (fun _ _ => 0) (fun i => Fin.elim0 i)

/-- Abstract uniform-index telescoping on `AdmissibleDistinguishers`. -/
lemma abstract_uniform_telescoping_check
    {I : Type} {Phi D : I → Type} [Distinguishers I Phi D] [AdmissibleDistinguishers I D]
    {A B : I} (H : Fin 4 → Phi A) (X₀ X₁ : Phi B)
    (stepDistinguisher : D A → Fin 3 → D B) (ρ : D A → D B)
    (hρ : ∀ d ∈ AdmissibleDistinguishers.admissible A, ρ d ∈ AdmissibleDistinguishers.admissible B)
    (hX₀ : ∀ d ∈ AdmissibleDistinguishers.admissible A,
      Distinguishers.probability (ρ d) X₀ =
        (1 / (3 : ℝ)) * ∑ i : Fin 3, Distinguishers.probability (stepDistinguisher d i) X₀)
    (hX₁ : ∀ d ∈ AdmissibleDistinguishers.admissible A,
      Distinguishers.probability (ρ d) X₁ =
        (1 / (3 : ℝ)) * ∑ i : Fin 3, Distinguishers.probability (stepDistinguisher d i) X₁)
    (hstep : ∀ d ∈ AdmissibleDistinguishers.admissible A, ∀ i : Fin 3,
      Distinguishers.signedGap d (H i.castSucc) (H i.succ) =
        Distinguishers.signedGap (stepDistinguisher d i) X₀ X₁)
    {ε : D B → ENNReal} (hX : X₀ ≃[ε] X₁) :
    H 0 ≃[fun d => (3 : ENNReal) * ε (ρ d)] H (Fin.last 3) :=
  AdmissibleDistinguishers.substitutesWithin_uniform_telescoping (by omega) H X₀ X₁
    stepDistinguisher ρ hρ hX₀ hX₁ hstep hX

/-- Structured uniform-index telescoping hybrid on a 3-step sequence of typed systems. -/
lemma structured_uniform_telescoping_check
    (admitted : ∀ A : Interface, Set (StructuredDistinguisher A))
    {A B : Interface} (H : Fin 4 → TypedSystem A) (X₀ X₁ : TypedSystem B)
    (stepDistinguisher : StructuredDistinguisher A → Fin 3 → StructuredDistinguisher B)
    (hclosed : ∀ D ∈ admitted A,
      StructuredDistinguisher.uniformChoice (by omega) (stepDistinguisher D) ∈ admitted B)
    (hstep : ∀ D ∈ admitted A, ∀ i : Fin 3,
      D.signedGap (H i.castSucc) (H i.succ) = (stepDistinguisher D i).signedGap X₀ X₁)
    {ε : StructuredDistinguisher B → ENNReal}
    (hX : (Interface.structuredDistinguisherAdvantage admitted).SubstitutesWithin ε X₀ X₁) :
    (Interface.structuredDistinguisherAdvantage admitted).SubstitutesWithin
      (fun D => (3 : ENNReal) *
        ε (StructuredDistinguisher.uniformChoice (by omega) (stepDistinguisher D)))
      (H 0) (H (Fin.last 3)) :=
  Interface.structuredSubstitutesWithin_uniform_telescoping admitted (by omega) H X₀ X₁
    stepDistinguisher hclosed hstep hX

/-- Bidirectional bridge between `TypedDistinguisher` and `StructuredDistinguisher`. -/
lemma typed_structured_roundtrip
    {A : Interface} {R S : TypedSystem A} {ε : ENNReal}
    (h : (Distinguishers.distinguisherAdvantage (Phi := TypedSystem)
      (fun _ => Set.univ)).SubstitutesWithin (fun _ => ε) R S) :
    (Interface.structuredDistinguisherAdvantage (fun _ => Set.univ)).SubstitutesWithin
      (fun _ => ε) R S :=
  Interface.structuredSubstitutesWithin_of_typed (fun _ => Set.univ) (fun _ => Set.univ)
    (fun _ _ => Set.mem_univ _) h

#print axioms StructuredDistinguisher.toTyped_absorb
#print axioms StructuredDistinguisher.transcriptLaw_bind
#print axioms StructuredDistinguisher.signedGap_telescoping_uniformChoice
#print axioms StructuredDistinguisher.advantage_telescoping_uniformChoice_le
#print axioms StructuredDistinguisher.IsNonAdaptive.uniformChoice
#print axioms StructuredDistinguisher.fixedQuery_isNonAdaptive
#print axioms StructuredDistinguisher.sampleFixedQuery_isNonAdaptive
#print axioms CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin.chain
#print axioms Distinguishers.signedGap_telescoping
#print axioms Distinguishers.signedGap_uniform_telescoping
#print axioms AdmissibleDistinguishers.substitutesWithin_uniform_telescoping
#print axioms Interface.structuredAdvantage_le_distance
#print axioms Interface.structuredSubstitutesWithin_attach
#print axioms Interface.structuredSubstitutesWithin_of_typed
#print axioms Interface.typedSubstitutesWithin_of_structured
#print axioms Interface.structuredSubstitutesWithin_uniform_telescoping

end Tests.StructuredHybrid
