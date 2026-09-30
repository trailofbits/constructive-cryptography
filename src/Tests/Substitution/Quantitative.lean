import ConstructiveCryptography.Substitution.Quantitative
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# A mixed quantitative chain

Three steps, two uses of one assumption and one statistical step, sum to the stated loss.
-/

namespace Tests.Substitution.Quantitative

open CategoryTheory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SubstitutionRelation
open scoped BigOperators

universe u v w x y

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
variable {Distinguisher : C → Type y}

-- A three-step source chain uses the named assumption twice and a statistical
-- bound once. The middle reverse step is not counted as an assumption use.
theorem mixed_three_steps [MonoidalCategory C] [CompatiblePseudoMetric C Phi] {A : C}
    (model : DistinguisherAdvantage C Phi Distinguisher)
    (left right : Phi A) (loss : Distinguisher A → ENNReal) (error : ENNReal)
    (domination : ∀ distinguisher ∈ model.admissible A,
      ∀ first second, model.advantage A distinguisher first second ≤
        distance first second)
    (assumption : model.SubstitutesWithin loss left right)
    (approximate : distance right left ≤ error) :
    ∃ witness : Implication (fun _ : Unit => A)
        (fun _ bit => if bit then right else left) A 2,
      witness.selectedUsageCount (fun position => if position.val = 1 then false else true) () = 2 ∧
      model.SubstitutesWithin (fun distinguisher => loss distinguisher + error + loss distinguisher)
        witness.targetLeft witness.targetRight := by
  let single := Implication.single (systems := fun (_ : Unit) bit => if bit then right else left)
    () false (𝟙 A)
  let witness := (single.append single.reverse rfl).append single rfl
  let selected : Fin 3 → Bool := fun position => if position.val = 1 then false else true
  refine ⟨witness, ?_, ?_⟩
  · -- Only the first and last positions are assumption uses.
    fail_if_success exact (show (3 : Nat) = 3 from rfl)
    change (Finset.univ.filter (fun position : Fin 3 =>
      selected position = true ∧ witness.index position = ())).card = 2
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ,
      Fin.sum_univ_zero, selected, witness, single, Implication.append,
      Implication.reverse, Implication.single, Fin.addCases, Fin.castAdd,
      Fin.natAdd, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
      Nat.add_zero, Nat.zero_add, ↓reduceIte,
      Bool.false_eq_true, and_true, Nat.reduceEqDiff]
  · have bounds : ∀ position : Fin 3, selected position = true →
        model.SubstitutesWithin loss
          (attach (witness.transformation position)
            ((fun (_ : Unit) bit => if bit then right else left)
              (witness.index position) (witness.direction position)))
          (attach (witness.transformation position)
            ((fun (_ : Unit) bit => if bit then right else left)
              (witness.index position) (!(witness.direction position)))) := by
      intro position chosen
      fin_cases position
      · change model.SubstitutesWithin loss
          (attach (𝟙 A) left) (attach (𝟙 A) right)
        rw [attach_identity, attach_identity]
        exact assumption
      · change false = true at chosen
        cases chosen
      · change model.SubstitutesWithin loss
          (attach (𝟙 A) left) (attach (𝟙 A) right)
        rw [attach_identity, attach_identity]
        exact assumption
    have statistical : ∀ position : Fin 3, selected position = false →
        distance
          (attach (witness.transformation position)
            ((fun (_ : Unit) bit => if bit then right else left)
              (witness.index position) (witness.direction position)))
          (attach (witness.transformation position)
            ((fun (_ : Unit) bit => if bit then right else left)
              (witness.index position) (!(witness.direction position)))) ≤ error := by
      intro position chosen
      fin_cases position
      · change true = false at chosen
        cases chosen
      · change distance (attach (𝟙 A) right)
          (attach (𝟙 A) left) ≤ error
        rw [attach_identity, attach_identity]
        exact approximate
      · change true = false at chosen
        cases chosen
    have total : model.SubstitutesWithin
        (fun distinguisher => ∑ position : Fin 3,
          if selected position then loss distinguisher else error)
        witness.targetLeft witness.targetRight := by
      exact Implication.substitutesWithin_of_mixed model witness selected
        (fun _ => loss) (fun _ => error) domination bounds statistical
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, selected, Fin.val_zero,
      Fin.val_succ, Nat.reduceAdd, Nat.reduceEqDiff, Bool.false_eq_true,
      ↓reduceIte, add_zero, add_assoc] using total


end Tests.Substitution.Quantitative
