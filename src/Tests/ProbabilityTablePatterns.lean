import Probability.Counting

/-!
# Repeated-query table laws

Examples of `uniform_mass_transcript_eq`, `Pr[F matches h] = (1/|Y|)^d` for a transcript `h`
answered by a function, with `d` the number of distinct inputs of `h`, and of
`fTransform_eval_uniform_eq_of_same_fibers`,
`Law(i ↦ F (left i)) = Law(i ↦ G (right i))` for query maps with the same equality pattern.

```text
h = [(false, true), (false, true)]                  mass 1/2        one coordinate, repeated
h = [(false, true), (false, false)]                 mass 0          contradictory replies
h = [(false, true), (true, false), (false, true)]   mass (1/2)^2    two coordinates, one repeat
i ↦ F false  vs  i ↦ G 0,  G : Fin 3 → Bool         equal laws      different table domains
n ↦ F (n even)  vs  n ↦ G (some (n even)),  n : ℕ   equal laws      infinite index type
ULift.{1} Bool → ULift.{2} Bool                     (1/|Y|)^d       other universes
```
-/

namespace Probability.Counting.Tests

/-- `h = [(false, true), (false, true)]` has one distinct input, so for `F` uniform on
`Bool → Bool`, `Pr[F false = true] = (1/2)^1`, not `(1/2)^2`. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (false, true)] : List (Bool × Bool)), f z.1 = z.2) =
      (1 / 2 : ℝ) := by
  -- `h` is answered by negation `g x = !x`: both entries are `(false, true)` and `!false = true`.
  have hg : ∀ z ∈ ([(false, true), (false, true)] : List (Bool × Bool)),
      (fun x : Bool => !x) z.1 = z.2 := by
    intro z hz
    have hz' : z = (false, true) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hz
    subst z
    rfl
  -- The transcript law with `|S| = |{false}| = 1` and `|Y| = |Bool| = 2` gives `(1/2)^1 = 1/2`.
  convert uniform_mass_transcript_eq
    ([(false, true), (false, true)] : List (Bool × Bool)) (fun x => !x) hg using 1
  norm_num

/-- `h = [(false, true), (false, false)]` gives two replies to one input:
`Pr[F false = true ∧ F false = false] = 0`. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (false, false)] : List (Bool × Bool)), f z.1 = z.2) =
      0 := by
  -- An event satisfied by no table has mass 0.
  apply Distribution.mass_eq_zero_of_forall_not
  -- For any table `F`, `F false = true` and `F false = false` give `true = false`.
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Bool.eq_true_and_eq_false_self] at hf

/-- `h = [(false, true), (true, false), (false, true)]` has distinct inputs `{false, true}`:
`Pr[F false = true ∧ F true = false] = (1/2)^2`; the repeated `(false, true)` adds no factor. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (true, false), (false, true)] : List (Bool × Bool)),
      f z.1 = z.2) = (1 / (2 : ℝ)) ^ 2 := by
  -- `h` is answered by negation: `!false = true` and `!true = false`, entry by entry.
  have hg : ∀ z ∈ ([(false, true), (true, false), (false, true)] : List (Bool × Bool)),
      (fun x : Bool => !x) z.1 = z.2 := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> rfl
  -- The transcript law with `|S| = |{false, true}| = 2` and `|Y| = |Bool| = 2` gives `(1/2)^2`.
  convert uniform_mass_transcript_eq
    ([(false, true), (true, false), (false, true)] : List (Bool × Bool)) (fun x => !x) hg
    using 1
  norm_num

/-- `left i = false` in `Bool` and `right i = 0` in `Fin 3`, for `i : Fin 2`: for `F` uniform on
`Bool → Bool` and `G` uniform on `Fin 3 → Bool`,
`Law(F false, F false) = Law(G 0, G 0)`, both `(U, U)` with `U` uniform on `Bool`. -/
example :
    Distribution.fTransform (fun f : Bool → Bool => fun _ : Fin 2 => f false)
        (Distribution.uniform (Bool → Bool)) =
      Distribution.fTransform (fun f : Fin 3 → Bool => fun _ : Fin 2 => f 0)
        (Distribution.uniform (Fin 3 → Bool)) := by
  -- Both query maps are constant, so `left i = left j` and `right i = right j` both hold.
  apply fTransform_eval_uniform_eq_of_same_fibers
  intro i j
  exact iff_of_true rfl rfl

/-- `left n = (n % 2 == 0)` in `Bool` and `right n = some (left n)` in `Option Bool`, for
`n : ℕ`. Both have the classes even and odd, so both outputs have the law of
`(U, V, U, V, …)` with `U`, `V` independent uniform on `Bool`; the index type is infinite. -/
example :
    Distribution.fTransform (fun f : Bool → Bool => fun n : Nat => f (n % 2 == 0))
        (Distribution.uniform (Bool → Bool)) =
      Distribution.fTransform (fun f : Option Bool → Bool => fun n : Nat =>
        f (some (n % 2 == 0))) (Distribution.uniform (Option Bool → Bool)) := by
  -- `some a = some b ↔ a = b`, so the pattern condition `left i = left j ↔ right i = right j`
  -- becomes `left i = left j ↔ left i = left j`.
  apply fTransform_eval_uniform_eq_of_same_fibers
  intro i j
  simp only [Option.some.injEq]

/-- With `X = ULift.{1} Bool` and `Y = ULift.{2} Bool`, a transcript `h` answered by `g` has
`Pr[F matches h] = (1/|Y|)^d`, `d` the number of distinct inputs of `h`. -/
example (h : List (ULift.{1} Bool × ULift.{2} Bool))
    (g : ULift.{1} Bool → ULift.{2} Bool) (hg : ∀ z ∈ h, g z.1 = z.2) :
    (Distribution.uniform (ULift.{1} Bool → ULift.{2} Bool)).mass
        (fun f => ∀ z ∈ h, f z.1 = z.2) =
      (1 / (Fintype.card (ULift.{2} Bool) : ℝ)) ^ (h.map Prod.fst).toFinset.card := by
  -- The transcript law holds at any universes of `X` and `Y`.
  exact uniform_mass_transcript_eq h g hg

/-- No unordered pair exists when only one coordinate is visible. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ¬ Set.InjOn f ({false} : Finset Bool)) ≤ 0 := by
  simpa using uniform_mass_not_injOn_le_choose (X := Bool) (Y := Bool) ({false} : Finset Bool)

/-- Two visible coordinates incur exactly one pair opportunity in the union bound. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ¬ Set.InjOn f (Finset.univ : Finset Bool)) ≤ (1 / 2 : ℝ) := by
  simpa using uniform_mass_not_injOn_le_choose (X := Bool) (Y := Bool) Finset.univ

/-- The second coordinate stays uniform after revealing the first. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => f false = true ∧ f true = false) =
      (Distribution.uniform (Bool → Bool)).mass (fun f => f false = true) / 2 := by
  apply uniform_mass_fresh_eval_eq
  intro f g he
  simp only [he false (by simp)]

#print axioms Probability.Counting.uniform_mass_transcript_eq
#print axioms Probability.Counting.fTransform_eval_uniform_eq_of_same_fibers
#print axioms Probability.Counting.uniform_mass_fresh_eval_eq
#print axioms Probability.Counting.uniform_mass_not_injOn_le_choose
#print axioms Probability.Distribution.mass_exists_pair_le_choose

end Probability.Counting.Tests
