module

public import Probability.Kernel

/-!
# Coincidence laws for independent tables

Independent tables with one entry law assign the same output law to any two tuples that repeat at
the same indices, even across different table domains and for infinite tuple or outcome types.
The factored form `ProbDist.map_piDep_comp_comp` also handles varying coordinate laws when the
tuple factors through an injective map.
-/

@[expose] public section

namespace Tests.IndependentTableCoincidence

open Probability.Distribution

/-- `(true, false, true)` in `Bool` and `(0, 2, 0)` in `Fin 3` have the same law under any
single entry law `μ`, even though index `0` and index `2` repeat. -/
example {Y : Type*} (μ : ProbDist Y) :
    (ProbDist.piDep fun _ : Bool => μ).map
        (fun f (i : Fin 3) => f (match i with | 0 => true | 1 => false | 2 => true)) =
      (ProbDist.piDep fun _ : Fin 3 => μ).map
        (fun f (i : Fin 3) => f (match i with | 0 => 0 | 1 => 2 | 2 => 0)) := by
  apply ProbDist.map_piDep_comp_eq_of_eq_iff
  intro i j
  match i, j with
  | 0, 0 | 0, 2 | 1, 1 | 2, 0 | 2, 2 => exact iff_of_true rfl rfl
  | 0, 1 | 1, 0 | 1, 2 | 2, 1 =>
    simp only [Bool.true_eq_false, Bool.false_eq_true, Fin.reduceEq]

/-- The tuple `(true, false, true)` repeats at `0` and `2`, so `map_piDep_comp` does not apply. -/
example : ¬ Function.Injective
    (fun i : Fin 3 => match i with | 0 => true | 1 => false | 2 => true) := by
  intro hinj
  have h : (0 : Fin 3) = 2 := hinj rfl
  simp only [Fin.reduceEq] at h

/-- Factoring `(0, 2, 0)` through `true ↦ 0, false ↦ 2` restricts a heterogeneous table on `Fin 3`
to `Bool` while keeping the repeated coordinate at indices `0` and `2`. -/
example {A : Fin 3 → Type*} (μ : ∀ i, ProbDist (A i)) :
    (ProbDist.piDep μ).map
        (fun f (k : Fin 3) => f ((fun | true => (0 : Fin 3) | false => 2)
          (match k with | 0 => true | 1 => false | 2 => true))) =
      (ProbDist.piDep fun b : Bool => μ (match b with | true => 0 | false => 2)).map
        (fun g (k : Fin 3) => g (match k with | 0 => true | 1 => false | 2 => true)) := by
  refine ProbDist.map_piDep_comp_comp μ (fun | true => (0 : Fin 3) | false => 2) ?_ _
  intro a b hab
  cases a <;> cases b <;> simp only [Fin.reduceEq] at hab ⊢

/-- Both the tuple index `ℕ` and the outcome alphabet `ℕ` may be infinite. -/
example (μ : ProbDist ℕ) :
    (ProbDist.piDep fun _ : Bool => μ).map (fun f (n : ℕ) => f (n % 2 == 0)) =
      (ProbDist.piDep fun _ : Fin 3 => μ).map
        (fun f (n : ℕ) => f (if n % 2 == 0 then 0 else 2)) := by
  apply ProbDist.map_piDep_comp_eq_of_eq_iff
  intro i j
  cases h1 : (i % 2 == 0) <;> cases h2 : (j % 2 == 0) <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, Fin.reduceEq]

/-- With distinct coordinate laws, the same coincidence pattern need not give the same law. -/
example :
    (ProbDist.piDep fun b : Bool => ProbDist.single b).map
        (fun f (_ : Fin 2) => f true) ≠
      (ProbDist.piDep fun b : Bool => ProbDist.single b).map
        (fun f (_ : Fin 2) => f false) := by
  intro h
  have hval := congrArg (fun P => P.1 (fun _ : Fin 2 => true)) h
  have hl : ((ProbDist.piDep fun b : Bool => ProbDist.single b).map
      (fun f (_ : Fin 2) => f true)).1 (fun _ : Fin 2 => true) = 1 := by
    rw [ProbDist.map_val, ProbDist.piDep_val]
    have hpt : piDep (fun b : Bool => (ProbDist.single b).1) =
        Finsupp.single (fun b : Bool => b) 1 := piDep_single (fun b => b)
    rw [hpt, fTransform_single, Finsupp.single_eq_same]
  have hr : ((ProbDist.piDep fun b : Bool => ProbDist.single b).map
      (fun f (_ : Fin 2) => f false)).1 (fun _ : Fin 2 => true) = 0 := by
    rw [ProbDist.map_val, ProbDist.piDep_val]
    have hpt : piDep (fun b : Bool => (ProbDist.single b).1) =
        Finsupp.single (fun b : Bool => b) 1 := piDep_single (fun b => b)
    rw [hpt, fTransform_single, Finsupp.single_eq_of_ne]
    intro heq
    have h0 := congrFun heq 0
    cases h0
  rw [hl, hr] at hval
  exact one_ne_zero hval

#print axioms ProbDist.map_piDep_comp_comp
#print axioms ProbDist.map_piDep_comp_eq_of_eq_iff

end Tests.IndependentTableCoincidence
