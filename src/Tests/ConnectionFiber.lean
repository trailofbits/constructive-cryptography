module

public import RandomSystems.Cumulative.ConnectionObservation
public import RandomSystems.Typed.Functional
public import Mathlib.Tactic.NormNum

/-!
# Completed connection fibers

One connection asks only `false`. Its two components agree there, differ on `true`, and admit
one versus two queries. Empty input and an unfinished interaction check the completion boundary.
-/

@[expose] public section

namespace SystemAlgebra.Tests.ConnectionFiber

/-- One Boolean query/reply port, admitting at most `q` queries. -/
abbrev bits (q : ℕ) : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) q

/-- `echo(x) = x`, for one query. -/
noncomputable def echo : TypedSystem (bits 1) :=
  TypedSystem.ofFunction fun _ x => x

/-- `constantFalse(x) = false`, for up to two queries. -/
noncomputable def constantFalse : TypedSystem (bits 2) :=
  TypedSystem.ofFunction fun _ _ => false

/-- Expose every reply immediately, making no internal follow-up call. -/
def expose : (Σ _ : Unit, Bool) → (Σ _ : Unit, Bool) ⊕ (Σ _ : Unit, Bool) := Sum.inl

/-- Every external natural number submits the Boolean query `false`. -/
def submit (_ : ℕ) : Σ _ : Unit, Bool := ⟨(), false⟩

/-- The selected completed fiber is identical despite different domains and an unqueried
input on which the systems disagree. -/
theorem completed_reply :
    echo.1.connectionLaw expose submit [0] 1 [⟨(), false⟩] =
      constantFalse.1.connectionLaw expose submit [0] 1 [⟨(), false⟩] := by
  apply RandomSystem.connectionLaw_apply_eq_of_completed
  intro t hc hn _ hexp
  cases t with
  | nil => exact (RandomSystem.mass_nil _).trans (RandomSystem.mass_nil _).symm
  | cons z tail =>
    have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hn)
    subst tail
    rcases z with ⟨⟨i, x⟩, ⟨j, y⟩⟩
    cases i
    cases j
    have hx := hc [] (⟨(), x⟩, ⟨(), y⟩) (List.prefix_refl _)
    have hx' : x = false := by
      simpa [connectionQueries_nil, submit] using hx
    have hy : y = false := by
      simpa [exposedReplies, expose] using hexp
    subst x
    subst y
    norm_num [echo, constantFalse, TypedSystem.ofFunction_mass, bits, Interface.queryBudget]

/-- The selected fiber has positive mass: its single exchange already contributes one. -/
example : 1 ≤ echo.1.connectionLaw expose submit [0] 1 [⟨(), false⟩] := by
  have hc : FollowsStrategy (connectionQueries expose submit [0])
      [(⟨(), false⟩, ⟨(), false⟩)] := by
    apply (FollowsStrategy.snoc_iff (σ := connectionQueries expose submit [0])
      (h := []) (z := (⟨(), false⟩, ⟨(), false⟩))).mpr
    exact ⟨FollowsStrategy.nil, by simp [connectionQueries_nil, submit]⟩
  have bound := RandomSystem.mass_le_connectionLaw echo.1 expose submit [0] 1
    [(⟨(), false⟩, ⟨(), false⟩)] hc (by simp)
    (by simp [connectionQueries, exposedReplies, expose])
  simpa [echo, TypedSystem.ofFunction_mass, bits, Interface.queryBudget,
    exposedReplies, expose] using bound

/-- The same systems disagree on the unqueried input `true`. -/
example : echo.1 [(⟨(), true⟩, ⟨(), true⟩)] = 1 ∧
    constantFalse.1 [(⟨(), true⟩, ⟨(), true⟩)] = 0 := by
  norm_num [echo, constantFalse, TypedSystem.ofFunction_mass, bits, Interface.queryBudget]

/-- Two queries are admitted only by the second component. -/
example : ¬ (bits 1).domain [⟨(), false⟩, ⟨(), false⟩] ∧
    (bits 2).domain [⟨(), false⟩, ⟨(), false⟩] := by
  norm_num [bits, Interface.queryBudget]

/-- With no external input, the common empty interaction remains a completed fiber. -/
example : echo.1.connectionLaw expose submit [] 0 [] =
    constantFalse.1.connectionLaw expose submit [] 0 [] := by
  apply RandomSystem.connectionLaw_apply_eq_of_completed
  intro t _ hn _ _
  have ht : t = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
  subst t
  exact (RandomSystem.mass_nil _).trans (RandomSystem.mass_nil _).symm

/-- Cutting off before the first answer gives no completed probability. -/
example : echo.1.connectionLaw expose submit [0] 0 [] = 0 := by
  by_contra hne
  obtain ⟨t, _, hn, hstop, _, _⟩ :=
    RandomSystem.exists_completed_of_connectionLaw_ne_zero _ _ _ _ _ hne
  have ht : t = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
  subst t
  exact hstop (by simp [connectionQueries, exposedReplies])

#print axioms RandomSystem.connectionLaw_apply_eq_of_completed
#print axioms completed_reply

end SystemAlgebra.Tests.ConnectionFiber
