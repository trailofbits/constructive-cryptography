import Probability.Counting

/-!
# Repeated-query table laws

Two identical queries constrain one uniform table coordinate. Conflicting replies to the same
query have zero mass. Mixed repeated/distinct queries count each distinct coordinate once;
Nat-indexed families preserve two query classes across different table domains. A lifted-type
example checks that the transcript law is polymorphic in both alphabet universes.
-/

namespace Probability.Counting.Tests

/-- Repeating a consistent query pays for one coordinate, not two independent draws. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (false, true)] : List (Bool × Bool)), f z.1 = z.2) =
      (1 / 2 : ℝ) := by
  -- Boolean negation agrees with both recorded replies at the repeated input.
  have hg : ∀ z ∈ ([(false, true), (false, true)] : List (Bool × Bool)),
      (fun x : Bool => !x) z.1 = z.2 := by
    intro z hz
    have hz' : z = (false, true) := by simpa using hz
    subst z
    rfl
  -- The transcript fixes one coordinate, so its mass is 1/2.
  simpa using uniform_mass_transcript_eq
    ([(false, true), (false, true)] : List (Bool × Bool)) (fun x => !x) hg

/-- A uniform function cannot give contradictory answers to one input. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (false, false)] : List (Bool × Bool)), f z.1 = z.2) =
      0 := by
  -- No table assigns both Boolean values to the same input, so the event is empty.
  apply Distribution.mass_eq_zero_of_forall_not
  intro f hf
  simp at hf

/-- The transcript `[(false,true), (true,false), (false,true)]` fixes two coordinates.
Its mass is `(1/2)^2`; repeating the first query contributes no additional factor. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (true, false), (false, true)] : List (Bool × Bool)),
      f z.1 = z.2) = (1 / (2 : ℝ)) ^ 2 := by
  -- Boolean negation agrees with all three exchanges, including the repeated one.
  have hg : ∀ z ∈ ([(false, true), (true, false), (false, true)] : List (Bool × Bool)),
      (fun x : Bool => !x) z.1 = z.2 := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> rfl
  -- The distinct inputs are exactly the two Booleans.
  simpa using uniform_mass_transcript_eq
    ([(false, true), (true, false), (false, true)] : List (Bool × Bool)) (fun x => !x) hg

/-- Repeating one input has the same output law for tables of different domain sizes. -/
example :
    Distribution.fTransform (fun f : Bool → Bool => fun _ : Fin 2 => f false)
        (Distribution.uniform (Bool → Bool)) =
      Distribution.fTransform (fun f : Fin 3 → Bool => fun _ : Fin 2 => f 0)
        (Distribution.uniform (Fin 3 → Bool)) := by
  -- Both query maps are constant, so every pair of indices belongs to the same class.
  apply fTransform_eval_uniform_eq_of_same_fibers
  intro i j
  simp

/-- `left(n) = (n % 2 == 0)` and `right(n) = some (left(n))` have the same two query classes.
The common output law alternates `U,V,U,V,...` for independent uniform Boolean values U and V.
The index type is Nat; no finite enumeration of it is available. -/
example :
    Distribution.fTransform (fun f : Bool → Bool => fun n : Nat => f (n % 2 == 0))
        (Distribution.uniform (Bool → Bool)) =
      Distribution.fTransform (fun f : Option Bool → Bool => fun n : Nat =>
        f (some (n % 2 == 0))) (Distribution.uniform (Option Bool → Bool)) := by
  -- The injective map some preserves and reflects equality of queried coordinates.
  apply fTransform_eval_uniform_eq_of_same_fibers
  intro i j
  simp only [Option.some.injEq]

/-- Lifting the input and output alphabets to different universes preserves
`Pr[F matches h] = (1 / |Y|)^|distinct inputs of h|`. -/
example (h : List (ULift.{1} Bool × ULift.{2} Bool))
    (g : ULift.{1} Bool → ULift.{2} Bool) (hg : ∀ z ∈ h, g z.1 = z.2) :
    (Distribution.uniform (ULift.{1} Bool → ULift.{2} Bool)).mass
        (fun f => ∀ z ∈ h, f z.1 = z.2) =
      (1 / (Fintype.card (ULift.{2} Bool) : ℝ)) ^ (h.map Prod.fst).toFinset.card := by
  -- The same coordinate-counting law applies without lowering either alphabet's universe.
  exact uniform_mass_transcript_eq h g hg

#print axioms Probability.Counting.uniform_mass_transcript_eq
#print axioms Probability.Counting.fTransform_eval_uniform_eq_of_same_fibers

end Probability.Counting.Tests
