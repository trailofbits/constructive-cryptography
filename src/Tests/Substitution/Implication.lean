import ConstructiveCryptography.Substitution.Relaxation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Implication-witness tests

Witnesses built from single uses, reversal, concatenation and transformation: their endpoints,
their use counts (repeated uses are counted, not collapsed), and their validity.
-/

namespace Tests.Substitution.Implication

open CategoryTheory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SubstitutionRelation

universe u v w x

variable {C : Type u} [Category.{v} C]
variable {Phi : C → Type w} [ResourceTheory C Phi]
variable {ι : Type x} {boundary : ι → C}
variable {systems : ∀ i, Bool → Phi (boundary i)}

-- Every named premise belongs to the generated relation, by its identity
-- transformation; no semantic validity of the premise is assumed here.
example (assumption : ι) :
    (generatedRelation boundary systems).substitutes (boundary assumption)
      (systems assumption false) (systems assumption true) := by
  refine ⟨0, Implication.single (systems := systems) assumption false (𝟙 _), ?_, ?_⟩
  · exact attach_identity _
  · exact attach_identity _

-- Heterogeneous assumptions, a reversed second use, and an additional outer
-- context exercise the actual dependent chain rather than a same-fibre shortcut.
theorem transformed_chain_counts [DecidableEq ι] {A B : C}
    (firstAssumption secondAssumption : ι)
    (firstTransform : B ⟶ boundary firstAssumption)
    (secondTransform : B ⟶ boundary secondAssumption)
    (context : A ⟶ B)
    (join : attach firstTransform (systems firstAssumption true) =
      attach secondTransform (systems secondAssumption true)) :
    ∃ implication : Implication boundary systems A 1,
      implication.targetLeft = attach context
        (attach firstTransform (systems firstAssumption false)) ∧
      implication.targetRight = attach context
        (attach secondTransform (systems secondAssumption false)) ∧
      ∀ assumption, implication.usageCount assumption =
        (if firstAssumption = assumption then 1 else 0) +
        (if secondAssumption = assumption then 1 else 0) := by
  let first := Implication.single (systems := systems) firstAssumption false firstTransform
  let second := (Implication.single (systems := systems) secondAssumption false
    secondTransform).reverse
  have joined : first.targetRight = second.targetLeft := join
  let combined := (first.append second joined).map context
  refine ⟨combined, rfl, rfl, ?_⟩
  intro assumption
  -- The supplied context and reversal preserve counts; concatenation adds them.
  rw [Implication.usageCount_map, Implication.usageCount_append first second joined]
  simp only [first, second, Implication.usageCount_reverse, Implication.usageCount_single]

-- Repeated uses of the same assumption must not collapse into a set of premises.
example [DecidableEq ι] {A : C} (assumption : ι)
    (transformation : A ⟶ boundary assumption) :
    let single := Implication.single (systems := systems) assumption false transformation
    (single.append single.reverse rfl).usageCount assumption = 2 := by
  intro single
  have one : single.usageCount assumption = 1 :=
    (Implication.usageCount_single assumption assumption false transformation).trans (if_pos rfl)
  calc
    _ = single.usageCount assumption + single.reverse.usageCount assumption :=
      single.usageCount_append single.reverse rfl assumption
    _ = 1 + 1 := congrArg₂ Nat.add one ((single.usageCount_reverse assumption).trans one)
    _ = 2 := rfl

-- Reversal is not allowed to change the premise multiplicities.
example [DecidableEq ι] {A : C} {uses : Nat}
    (implication : Implication boundary systems A uses) (assumption : ι) :
    implication.reverse.usageCount assumption = implication.usageCount assumption :=
  implication.usageCount_reverse assumption

-- A missing exact join does not become an implicit search obligation.
example {A : C} {n m : Nat}
    (first : Implication boundary systems A n) (second : Implication boundary systems A m)
    (join : first.targetRight = second.targetLeft) :
    Nonempty (Implication boundary systems A ((n + 1) + m)) := by
  fail_if_success exact ⟨first.append second rfl⟩
  exact ⟨first.append second join⟩

-- No fictitious zero-use chain is inserted to force reflexivity: with no
-- named assumptions, there is no nonempty implication even from R to itself.
example {A : C} (resource : Phi A) :
    ¬ derivable (fun i : PEmpty => nomatch i)
      (fun i : PEmpty => nomatch i) resource resource := by
  rintro ⟨uses, implication, _, _⟩
  exact (implication.index 0).elim

-- The generated relation is interpreted by any valid supplied substitution
-- semantics, without additional relation axioms or an invented game model.
example (relation : SubstitutionRelation C)
    (premise : ∀ i, relation.substitutes (boundary i) (systems i false) (systems i true))
    {A : C} {left right : Phi A}
    (derived : derivable boundary systems left right) :
    relation.substitutes A left right :=
  derivable_substitutes relation premise derived

-- An explicit implication now enters the existing CC specification calculus.
-- The diagonal hypothesis remains visible, as required by Jost's relaxation.
theorem construction_of_implication {A B : C} {uses : Nat}
    (protocol : A ⟶ B) (simulator : A ⟶ A)
    (real : Phi B) (ideal : Phi A)
    (implication : Implication boundary systems A uses)
    (leftEq : implication.targetLeft = attach protocol real)
    (rightEq : implication.targetRight = attach simulator ideal)
    (reflexive : ∀ target, Std.Refl ((generatedRelation boundary systems).substitutes target)) :
    Specification.Constructs protocol {real}
      (Specification.substitutionRelaxation (generatedRelation boundary systems) reflexive
        {attach simulator ideal}) := by
  apply (Specification.constructs_singleton_substitutionRelaxation_iff
    (generatedRelation boundary systems) reflexive).mpr
  -- The complete chain and its exact endpoints witness assumption implication.
  exact ⟨uses, implication, leftEq, rightEq⟩

section RawWitness


variable {A B : C}

-- Raw-record regression: explicit positions, a reversed second assumption,
-- one use of each premise, and the same substitution/distance endpoints.
-- The reader-facing calculation is in Tests.ConstructiveCryptography.Substitution.
example
    [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    (relation : SubstitutionRelation C)
    (firstLeft firstRight secondLeft secondRight : Phi B)
    (targetLeft targetRight : Phi A)
    (firstTransformation secondTransformation : A ⟶ B)
    (firstPremise : relation.substitutes B firstLeft firstRight)
    (secondPremise : relation.substitutes B secondLeft secondRight)
    (firstError secondError : ENNReal)
    (firstClose : distance firstLeft firstRight ≤ firstError)
    (secondClose : distance secondLeft secondRight ≤ secondError)
    (startEq : targetLeft = attach firstTransformation firstLeft)
    (joinEq : attach firstTransformation firstRight =
      attach secondTransformation secondRight)
    (endEq : targetRight =
      attach secondTransformation secondLeft) :
    relation.substitutes A targetLeft targetRight ∧
      distance targetLeft targetRight ≤
        firstError + secondError := by
  let systems : Bool → Bool → Phi B := fun assumption side =>
    match assumption, side with
    | false, false => firstLeft
    | false, true => firstRight
    | true, false => secondLeft
    | true, true => secondRight
  let index : Fin 2 → Bool := ![false, true]
  let direction : Fin 2 → Bool := ![false, true]
  let transformation : Fin 2 → (A ⟶ B) :=
    ![firstTransformation, secondTransformation]
  let implication : SubstitutionRelation.Implication
      (fun _ : Bool => B) systems A 1 := {
    targetLeft := targetLeft
    targetRight := targetRight
    index := index
    direction := direction
    transformation := transformation
    start_eq := by
      simpa [index, direction, transformation, systems] using startEq
    link_eq := fun use => by
      have useEq : use = 0 := Subsingleton.elim _ _
      subst use
      simpa [index, direction, transformation, systems] using joinEq
    end_eq := by
      simpa [index, direction, transformation, systems] using endEq }
  have univFinTwo : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
    ext use
    fin_cases use <;> simp
  have firstCount : implication.usageCount false = 1 := by
    change (Finset.univ.filter fun use : Fin 2 => index use = false).card = 1
    rw [univFinTwo]
    have filterEq : (({0, 1} : Finset (Fin 2)).filter
        fun use => index use = false) = {0} := by
      ext use
      fin_cases use <;> simp [index]
    rw [filterEq]
    simp
  have secondCount : implication.usageCount true = 1 := by
    change (Finset.univ.filter fun use : Fin 2 => index use = true).card = 1
    rw [univFinTwo]
    have filterEq : (({0, 1} : Finset (Fin 2)).filter
        fun use => index use = true) = {1} := by
      ext use
      fin_cases use <;> simp [index]
    rw [filterEq]
    simp
  -- One preserved premise cannot skip the printed join and endpoint equations.
  fail_if_success exact relation.preserved firstTransformation firstPremise
  have targetSubstitution := implication.substitutes relation (fun assumption => by
    cases assumption
    · exact firstPremise
    · exact secondPremise)
  have targetDistance := implication.distance_le ![firstError, secondError]
    (fun use => by
      fin_cases use
      · simpa [implication, index, systems] using firstClose
      · simpa [implication, index, systems] using secondClose)
  constructor
  · exact targetSubstitution
  · simpa [Fin.sum_univ_two] using targetDistance

end RawWitness

#print axioms generatedRelation
#print axioms derivable_substitutes
#print axioms Implication.usageCount_append
#print axioms Implication.usageCount_reverse
#print axioms transformed_chain_counts
#print axioms construction_of_implication

end Tests.Substitution.Implication
