module

public import RandomSystems.System.FiniteQueries

/-!
# Finite queries over an infinite alphabet

An environment asks `7`, then asks `23` only if the first Boolean reply is true.
The false branch stops early; every branch stops after at most two queries.
-/

@[expose] public section

namespace Tests.FiniteQueries

open SystemAlgebra

/-- Ask `7`; after `true`, ask `23`; after `false` or a second reply, stop. -/
def adaptive : DDE ℕ Bool :=
  ⟨fun ys => match ys with
    | [] => Part.some 7
    | [b] => if b then Part.some 23 else Part.none
    | _ => Part.none,
    by
      intro ys y defined
      cases ys with
      | nil => exact Part.some_dom 7
      | cons b ys => cases ys <;> exact defined.elim⟩

/-- The reply-dependent second query is the last possible query. -/
lemma adaptive_bounded : QueryBounded 2 adaptive := by
  intro ys defined
  cases ys with
  | nil => exact Nat.zero_lt_succ 1
  | cons b ys =>
    cases ys with
    | nil => exact Nat.lt_succ_self 1
    | cons c ys => exact defined.elim

/-- The natural-number queries used by the adaptive environment form a finite set. -/
lemma adaptive_finite : {x | ∃ ys, x ∈ adaptive.1 ys}.Finite :=
  finite_queries_of_queryBounded adaptive adaptive_bounded

example : adaptive.1 [] = Part.some 7 := rfl
example : adaptive.1 [true] = Part.some 23 := rfl
example : adaptive.1 [false] = Part.none := rfl
example : adaptive.1 [true, false] = Part.none := rfl

/-- Horizon zero contains no reply histories and hence no proposed queries. -/
example : {x | ∃ ys, ys.length < 0 ∧ x ∈ adaptive.1 ys} = (∅ : Set ℕ) := by
  ext x
  constructor
  · rintro ⟨ys, short, _⟩
    exact (Nat.not_lt_zero _ short).elim
  · intro impossible
    exact impossible.elim

example : {x | ∃ ys, ys.length < 0 ∧ x ∈ adaptive.1 ys}.Finite :=
  finite_queries_before adaptive.1 0

/-- The empty fixed query list gives a zero-query instance of the complete-range law. -/
example : {x | ∃ ys, x ∈ (DDE.ofQueries (X := ℕ) (Y := Bool) []).1 ys}.Finite :=
  finite_queries_of_queryBounded _ (DDE.ofQueries_queryBounded [])

#print axioms SystemAlgebra.finite_queries_before
#print axioms SystemAlgebra.finite_queries_of_queryBounded
#print axioms adaptive_finite

end Tests.FiniteQueries
