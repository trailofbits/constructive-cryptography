module

public import ConstructiveCryptography.Tactics.Substitution
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# A mixed quantitative chain

Three steps, two uses of one assumption and one statistical step, sum to the stated loss.
-/

@[expose] public section

set_option autoImplicit false

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
lemma mixed_three_steps [MonoidalCategory C] [CompatiblePseudoMetric C Phi] {A : C}
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

/-- The first step retains the Boolean observer tag and doubles the inside bound.
The next step adds statistical error `δ` on the outside resources. -/
example [MonoidalCategory C] [CompatiblePseudoMetric C Phi] {A : C} {Y : Type}
    (outside : DistinguisherAdvantage C Phi (fun _ => Bool))
    (inside : DistinguisherAdvantage Unit (fun _ => Y) (fun _ => Bool × Unit))
    {R S T : Phi A} {U V : Y} {ε : Bool × Unit → ENNReal}
    (closed : ∀ b ∈ outside.admissible A, (b, ()) ∈ inside.admissible ())
    (twice : ∀ b ∈ outside.admissible A,
      outside.advantage A b R S ≤ 2 * inside.advantage () (b, ()) U V)
    (bound : inside.SubstitutesWithin (A := ()) ε U V)
    (domination : ∀ b ∈ outside.admissible A, ∀ r s, outside.advantage A b r s ≤ distance r s)
    {δ : ENNReal} (close : distance S T ≤ δ) :
    outside.SubstitutesWithin (fun b => 2 * ε (b, ()) + δ) R T := by
  have reduced := DistinguisherAdvantage.SubstitutesWithin.of_reduction outside inside
    (fun b => (b, ())) (2 * ·) (fun _ _ h => mul_le_mul_right h 2)
    (fun {_} hb => closed _ hb) twice bound
  cc_calc mixed outside using domination
    R ≃[fun b => 2 * ε (b, ())] S := reduced
    _ ≈[δ] T := close

/-- The outside test observes `2` on `true` and `0` on `false`; only test `true` is admitted. -/
noncomputable def outsideModel :
    DistinguisherAdvantage Unit (fun _ => Bool) (fun _ => Bool) := by
  letI : Distinguishers Unit (fun _ => Bool) (fun _ => Bool) :=
    ⟨fun {_} _ r => if r then 2 else 0⟩
  exact Distinguishers.distinguisherAdvantage (fun _ => {true})

/-- The inside tests observe `1` on `true` and `0` on `false`; only `(false, ())` is admitted. -/
noncomputable def insideModel :
    DistinguisherAdvantage Unit (fun _ => Bool) (fun _ => Bool × Unit) := by
  letI : Distinguishers Unit (fun _ => Bool) (fun _ => Bool × Unit) :=
    ⟨fun {_} _ r => if r then 1 else 0⟩
  exact Distinguishers.distinguisherAdvantage (fun _ => {(false, ())})

/-- `tagBudget (b, ())` is zero on the excluded tag and one on the admitted inside tag. -/
def tagBudget (d : Bool × Unit) : ENNReal := if d.1 then 0 else 1

/-- The reduction changes the tag and doubles the inside loss, without a resource category. -/
example : outsideModel.SubstitutesWithin (A := ())
    (fun b => 2 * tagBudget (!b, ())) false true := by
  apply DistinguisherAdvantage.SubstitutesWithin.of_reduction outsideModel insideModel
    (B := ()) (U := false) (V := true)
    (fun b => (!b, ())) (2 * ·) (fun _ _ h => mul_le_mul_right h 2)
  · rintro b (rfl : b = true)
    exact Set.mem_singleton _
  · intro b _
    norm_num [outsideModel, insideModel, Distinguishers.distinguisherAdvantage,
      Distinguishers.advantage, Distinguishers.probability]
  · rintro d (rfl : d = (false, ()))
    norm_num [insideModel, DistinguisherAdvantage.SubstitutesWithin,
      Distinguishers.distinguisherAdvantage, Distinguishers.advantage,
      Distinguishers.probability, tagBudget]

/-- Keeping the tag satisfies the numerical reduction for every outside observer. -/
example (b : Bool) : outsideModel.advantage () b false true ≤
    2 * insideModel.advantage () (b, ()) false true := by
  norm_num [outsideModel, insideModel, Distinguishers.distinguisherAdvantage,
    Distinguishers.advantage, Distinguishers.probability]

/-- That unchanged tag does not belong to the admitted inside class. -/
example : ¬ Set.MapsTo (fun b => (b, ()))
    (outsideModel.admissible ()) (insideModel.admissible ()) := by
  intro closed
  have impossible := closed (show true ∈ outsideModel.admissible () from Set.mem_singleton _)
  simp only [insideModel, Distinguishers.distinguisherAdvantage, Set.mem_singleton_iff,
    Prod.mk.injEq, Bool.true_eq_false, false_and] at impossible

/-- Using that unadmitted test would incorrectly bound outside advantage `2` by `0`. -/
example : ¬ outsideModel.SubstitutesWithin (A := ())
    (fun b => 2 * tagBudget (b, ())) false true := by
  intro bound
  have impossible := bound true (Set.mem_singleton _)
  norm_num [outsideModel, Distinguishers.distinguisherAdvantage, Distinguishers.advantage,
    Distinguishers.probability, tagBudget] at impossible

#print axioms DistinguisherAdvantage.SubstitutesWithin.of_reduction

end Tests.Substitution.Quantitative
