module

public import RandomSystems.Cumulative.Mixture.Defs
public import RandomSystems.Cumulative.FiniteCuts
public import RandomSystems.Cumulative.CumulativeOperations

/-!
# Mixtures commute with finite observations

`cutMass_mixMass` restricts each component of a retained mixture at the same horizon.
`mixMass_isRandomSystem` glues the existing normalized bounded mixtures along their coherent
cuts. `RandomSystem.mix_eq_mixMass` identifies the bounded operation with this expectation.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

-- `P` samples one retained index; `p i` is its cumulative query/reply behavior.
variable {ι A B : Type} (P : ProbDist ι) (p : ι → List (A × B) → ℝ)

/-- A common observation horizon commutes with averaging whole-transcript masses. -/
lemma cutMass_mixMass (q : ℕ) :
    cutMass (mixMass P p) q = mixMass P (fun i => cutMass (p i) q) := by
  funext h
  by_cases hh : h.length ≤ q
  · simp only [cutMass, mixMass, ite_eq_left hh]
  · simp only [cutMass, mixMass, ite_eq_right hh]
    exact (P.1.expect_zero_right).symm

/-- The bounded mixture is the same expectation of cumulative masses. -/
lemma RandomSystem.mix_eq_mixMass [Fintype A] [Fintype B]
    -- `R i` share the same bounded domain `D`.
    {D : Domain A B} (R : ι → RandomSystem A B D) :
    (RandomSystem.mix P R : List (A × B) → ℝ) = mixMass P (fun i => R i) := rfl

/-- A retained finite mixture of normalized behaviors on one domain is normalized. -/
theorem mixMass_isRandomSystem [_root_.Finite A] [_root_.Finite B]
    -- `D` is the common query domain; `hp` normalizes every component on it.
    {D : List (A × B) → A → Prop} (hp : ∀ i, IsRandomSystem D (p i)) :
    IsRandomSystem D (mixMass P p) := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  let R (q : ℕ) := RandomSystem.mix P (fun i => IsRandomSystem.cut D (p i) (hp i) q)
  -- Every bounded mixture retains the same component masses at an earlier depth.
  have coherent (q : ℕ) (h : List (A × B)) (hh : h.length ≤ q) : R (q + 1) h = R q h := by
    change P.1.expect _ = P.1.expect _
    apply congrArg P.1.expect
    funext i
    exact IsRandomSystem.cut_coherent D (p i) (hp i) q h hh
  -- Reading at the transcript's depth removes every component cut.
  have same : RandomSystem.limitMass D R = mixMass P p := by
    funext h
    change P.1.expect _ = P.1.expect _
    apply congrArg P.1.expect
    funext i
    exact IsRandomSystem.cut_apply_of_length_le D (p i) (hp i) h.length h le_rfl
  exact same ▸ RandomSystem.limitMass_isRandomSystem D R coherent

end SystemAlgebra
