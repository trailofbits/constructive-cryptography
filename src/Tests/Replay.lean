import Probability.Replay

/-! # Adaptive replay and public table constraints -/

namespace Probability.Tests.Replay

open Counting

/-- Query the distinguished coordinate, then use its reply to choose a second coordinate. -/
def evaluate (table : Option Bool → Bool) : Option Unit → Bool
  | none => table none
  | some () => table (some (table none))

def site (value : Option Unit → Bool) : Option Unit → Option Bool
  | none => none
  | some () => some (value none)

/-- A complete output tuple pins exactly the coordinates this adaptive evaluation queried. -/
lemma pinned (table : Option Bool → Bool) (value : Option Unit → Bool) :
    evaluate table = value ↔ ∀ i, table (site value i) = value i := by
  constructor
  · intro h i
    have hfirst : table none = value none := congrFun h none
    cases i with
    | none => exact hfirst
    | some u =>
      cases u
      simpa [evaluate, site, hfirst] using congrFun h (some ())
  · intro h
    have hfirst : table none = value none := h none
    funext i
    cases i with
    | none => exact hfirst
    | some u =>
      cases u
      simpa [evaluate, site, hfirst] using h (some ())

/-- On first reply true, the public false coordinate is separate from both adaptive sites. -/
lemma distinct (value : Option Unit → Bool) (h : value none = true) :
    Function.Injective (Sum.elim (site value) (fun _ : Unit => some false)) := by
  simp [Function.Injective, Sum.forall, Option.forall, site, h]

/-- Two adaptive replies and one public value constrain three independent Boolean entries. -/
example : (Distribution.uniform (Option Bool → Bool)).mass
      (fun f => evaluate f = (fun _ => true) ∧ f (some false) = false) = 1 / 8 := by
  have h := uniform_mass_replay_public_eq site evaluate pinned (fun _ : Unit => some false)
    (fun _ => false) (fun _ => true) (distinct _ rfl)
  norm_num at h ⊢
  exact h

/-- The good-event factorization allows an additional event on the adaptive replies. -/
example (Event : (Option Unit → Bool) → Prop) :
    (Distribution.uniform (Option Bool → Bool)).mass
        (fun f => evaluate f none = true ∧ Event (evaluate f) ∧ f (some false) = false) =
      (Distribution.uniform (Option Unit → Bool)).mass
        (fun value => value none = true ∧ Event value) * (1 / 2) := by
  have h := uniform_replay_public_good_factor site evaluate pinned
    (fun _ : Unit => some false) (fun _ => false) (fun value => value none = true) Event distinct
  norm_num at h ⊢
  exact h

/-- On the bad branch, the second query hits the public coordinate, so independence fails. -/
example : ¬ Function.Injective
    (Sum.elim (site (fun _ => false)) (fun _ : Unit => some false)) := by
  intro h
  have he := h (a₁ := Sum.inl (some ())) (a₂ := Sum.inr ()) rfl
  cases he

#print axioms Probability.Counting.uniform_replay_public_good_factor

end Probability.Tests.Replay
