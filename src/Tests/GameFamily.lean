module

public import ConstructiveCryptography.Game.Family
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Game-family reduction consumers

Negating a target bit supplies a nonidentity attachment and solver transformation. Its
worst-case bound is an instance of the problem-family law. An always-won source and two
opposite target guesses check that target-dependent solver choices do not give a reduction.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.GameFamily

open ConstructiveCryptography

/-- The interface carrying the unique, always-won source game. -/
inductive SourceInterface
  | port

/-- The interface carrying Boolean guessing games. -/
inductive TargetInterface
  | port

/-- Each source interface carries the unique game `()`. -/
abbrev sourceGame (_ : SourceInterface) := Unit

/-- A target game carries the bit to be guessed. -/
abbrev targetGame (_ : TargetInterface) := Bool

/-- The source is always won: `sourceWinner () = 1`. -/
def sourceWinner : Unit → ℝ := fun _ => 1

/-- `targetWinner b H = 1` exactly when the fixed guess `b` equals target bit `H`. -/
def targetWinner (b : Bool) : Bool → ℝ := fun H => if H = b then 1 else 0

/-- The source admits exactly its constant-one winner. -/
instance sourceInterpretation : Games SourceInterface sourceGame ℝ where
  winners _ := {sourceWinner}

/-- The target admits exactly the two fixed guesses. -/
instance targetInterpretation : Games TargetInterface targetGame ℝ where
  winners _ := Set.range targetWinner

/-- An admitted target solver is one of the fixed Boolean guesses. -/
abbrev TargetWinner := {W : Bool → ℝ // W ∈ Games.winners TargetInterface.port}

/-- A Boolean function acts on a target by applying that function to its bit. -/
local instance functionAttachment : HSMul (Bool → Bool) Bool Bool := ⟨fun f b => f b⟩

/-- Absorbing negation changes guess `b` into guess `!b`. -/
lemma absorb_not_mem (W : Bool → ℝ) (admitted : W ∈ Games.winners TargetInterface.port) :
    Games.absorb W Bool.not ∈ Games.winners TargetInterface.port := by
  obtain ⟨b, rfl⟩ := admitted
  refine ⟨!b, ?_⟩
  funext H
  cases b <;> cases H <;> rfl

/-- One negation converter compares the entire family of Boolean games. -/
lemma negation_reduction :
    Games.Easier (A := TargetInterface.port) (B := TargetInterface.port)
      Set.univ Set.univ :=
  Games.easier_of_attach_mem (A := TargetInterface.port) (B := TargetInterface.port)
    Bool.not absorb_not_mem (fun _ _ => Set.mem_univ _)

/-- The generic infimum law applies to the admitted-winner subtype without a game wrapper. -/
example : ∃ ρ : TargetWinner → TargetWinner, ∀ W,
    Problem.worstCase Set.univ W.1 ≤ Problem.worstCase Set.univ (ρ W).1 := by
  apply Problem.Easier.worstCase_le negation_reduction Set.univ_nonempty
  intro W
  obtain ⟨b, hb⟩ := W.2
  refine ⟨0, ?_⟩
  rintro _ ⟨H, _, rfl⟩
  rw [← hb]
  change 0 ≤ if H = b then 1 else 0
  split <;> first | exact zero_le_one | exact le_rfl

/-- Knowing the target first permits choosing its winning guess. -/
lemma targetwise_transformations :
    ∀ H : Bool, ∃ V : TargetWinner, sourceWinner () ≤ V.1 H := by
  intro H
  exact ⟨⟨targetWinner H, ⟨H, rfl⟩⟩, by
    simp only [sourceWinner, targetWinner, ite_true, le_refl]⟩

/-- A uniform admitted solver map cannot win both opposite target games. -/
lemma not_uniform_reduction :
    ¬ Games.Easier (A := SourceInterface.port) (B := TargetInterface.port)
      Set.univ Set.univ := by
  rintro ⟨ρ, reduces⟩
  let W : {W : Unit → ℝ // W ∈ Games.winners SourceInterface.port} :=
    ⟨sourceWinner, Set.mem_singleton _⟩
  obtain ⟨b, hb⟩ := (ρ W).2
  obtain ⟨G, _, comparison⟩ := reduces (!b) (Set.mem_univ _)
  have impossible := comparison W
  change sourceWinner G ≤ (ρ W).1 (!b) at impossible
  rw [← hb] at impossible
  -- The target opposite to the chosen guess defeats that fixed solver.
  cases b <;> simp only [sourceWinner, targetWinner, Bool.not_false, Bool.not_true,
    Bool.true_eq_false, Bool.false_eq_true, ite_false] at impossible <;>
    exact (not_le_of_gt zero_lt_one) impossible

#print axioms Games.easier_of_attach_mem
#print axioms negation_reduction
#print axioms not_uniform_reduction

end Tests.GameFamily
