module

public import ConstructiveCryptography.Notation
public import RandomSystems.Typed.JointAutomaton
public import Tests.QueryRouting

/-!
# Three callers of one register

The leftmost caller writes a bit through a converter that counts its calls. The outer right
caller reads and flips that bit. The middle caller then reads the flipped value. Both readers
leave the write count unchanged. The opposite attachment puts the counter on reads.
-/

@[expose] public section

open SystemAlgebra Probability Probability.Distribution CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped SystemAlgebra

namespace SystemAlgebra.Tests.JointAutomatonAttachment

open QueryRouting (bits registerPorts registerStep)

local notation "𝔹" => bits 1

/-- Forward one bit query, return its reply, and increment the retained count. -/
def countCalls : Program ℕ (bits 1).I (bits 1).I (bits 1).X (bits 1).Y (bits 1).X (bits 1).Y
  | _, i, x, [] => .inr ⟨i, x⟩
  | n, _, _, (_, ⟨_, y⟩) :: _ => .inl (n + 1, y)

lemma countCalls_bounded : countCalls.Bounded 1 :=
  Program.bounded_one_of_history_eq_nil fun _ _ _ h _ _ hq => by
    cases h with
    | nil => rfl
    | cons e h => simp only [countCalls, reduceCtorEq] at hq

/-- Start the count at zero. The single allowed outside query uses one inside query. -/
noncomputable def counter : TypedConverter 𝔹 𝔹 :=
  TypedConverter.ofProgram 0 countCalls countCalls_bounded fun _ hn hl =>
    ⟨hn, by simpa only [Nat.one_mul] using hl⟩

/-- From counter state `n`, one forwarded transition returns its reply and increments `n`. -/
lemma countCalls_step {R : Type} (step : ProbStep R (bits 1).I (bits 1).X (bits 1).Y)
    (n : ℕ) (r : R) (x : Bool) :
    countCalls.probCombine step countCalls_bounded (n, r) () x =
      (step r () x).map (fun p => ((n + 1, p.1), p.2)) := by
  apply Subtype.ext
  change countCalls.probInvoke step n () x (0 + 1) r [] = _
  rw [Program.probInvoke_succ_inr (by rfl)]
  simp only [ProbStep.outcome, List.nil_append, Program.probInvoke, countCalls,
    bindK_single_comp, ProbDist.map_val, fTransform_fTransform]
  rfl

/-- Reads pass through the counter on the right. Writes update the shared register directly. -/
example (μ : ProbDist Bool) :
    (𝟙 𝔹 ⊗ₘ counter) • TypedSystem.ofProbAutomaton registerPorts
      (ProbStep.ofDeterministic registerStep) μ =
      TypedSystem.ofProbAutomaton registerPorts
        (countCalls.rightStep countCalls_bounded (ProbStep.ofDeterministic registerStep))
        (μ.map fun r => (0, r)) :=
  TypedConverter.id_parallel_smul_ofProbAutomaton 0 _ countCalls_bounded _ _ μ

/-- With the counter on reads, a direct write stores `b` without incrementing `n`. The counted
read sees `b` and increments `n` exactly once. -/
example (n : ℕ) (r b : Bool) :
    let δ := countCalls.rightStep countCalls_bounded (ProbStep.ofDeterministic registerStep)
    δ (n, r) (.inl ()) b = ProbDist.single ((n, b), b) ∧
      δ (n, b) (.inr ()) false = ProbDist.single ((n + 1, b), b) := by
  refine ⟨Subtype.ext (fTransform_single _ _ _), ?_⟩
  change countCalls.probCombine _ countCalls_bounded _ _ _ = _
  rw [countCalls_step]
  exact Subtype.ext (fTransform_single _ _ _)

/-- On the nested interface `(write ⊗ read) ⊗ flip`, the first two ports use the register
transition; the last returns the old bit and stores its complement. -/
noncomputable def threePortsStep : ProbStep Bool (registerPorts.tensor 𝔹).I
    (registerPorts.tensor 𝔹).X (registerPorts.tensor 𝔹).Y
  | r, .inl i, x => ProbDist.single (registerStep r i x)
  | r, .inr _, _ => ProbDist.single (!r, r)

/-- The inner pair counts writes and forwards reads. -/
noncomputable abbrev writerReader :=
  countCalls.sum (Program.forward (bits 1).I (bits 1).X (bits 1).Y)

/-- Attach the writer-reader pair beside the outer flip port. -/
noncomputable abbrev routedStep :=
  writerReader.leftStep (countCalls_bounded.sum Program.forward_bounded) threePortsStep

/-- The nested converters retain one joint register initialized by the arbitrary law `μ`. -/
lemma nested_register (μ : ProbDist Bool) :
    ((counter ⊗ₘ 𝟙 𝔹) ⊗ₘ 𝟙 𝔹) •
        TypedSystem.ofProbAutomaton (registerPorts.tensor 𝔹) threePortsStep μ =
      TypedSystem.ofProbAutomaton (registerPorts.tensor 𝔹) routedStep
        (μ.map fun r => ((0, ()), r)) := by
  -- Present the inner pair as one certified program before attaching it beside the outer identity.
  change TypedConverter.parallel (TypedConverter.parallel counter (TypedConverter.id 𝔹))
    (TypedConverter.id 𝔹) • _ = _
  nth_rw 1 [TypedConverter.id_eq_ofDDC_forward 𝔹]
  rw [counter, TypedConverter.ofProgram, TypedConverter.parallel_ofDDC_ofProgramOn
    0 countCalls countCalls_bounded _ () _ Program.forward_bounded _]
  exact TypedConverter.parallel_id_smul_ofProbAutomaton (A := registerPorts) (B := registerPorts)
    (E := 𝔹) (0, ()) writerReader
    (countCalls_bounded.sum Program.forward_bounded) _ _ μ

/-- The three-query sequence is admitted: each of the three ports is used exactly once. -/
example (b : Bool) : (registerPorts.tensor 𝔹).domain
    [⟨.inl (.inl ()), b⟩, ⟨.inr (), false⟩, ⟨.inl (.inr ()), false⟩] := by
  simp [registerPorts, Interface.tensor, Interface.parallelDomain, parallelInputs,
    bits, Interface.queryBudget, sumAlphabet, restrict_cons_self, restrict_cons_ne]

/-- The writer stores `b`. The outer reader sees `b` and flips it. The inner reader sees
`!b`. Only the first query increments the converter's count. -/
lemma nested_write_flip_read (n : ℕ) (r b : Bool) :
    routedStep ((n, ()), r) (.inl (.inl ())) b = ProbDist.single (((n + 1, ()), b), b) ∧
    routedStep ((n + 1, ()), b) (.inr ()) false = ProbDist.single (((n + 1, ()), !b), b) ∧
    routedStep ((n + 1, ()), !b) (.inl (.inr ())) false =
      ProbDist.single (((n + 1, ()), !b), !b) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Counted write.
    simp only [routedStep, Program.leftStep, writerReader,
      Program.probCombine_sum_inl _ countCalls_bounded,
      threePortsStep, registerStep]
    rw [countCalls_step (fun (_ : Bool) _ (x : Bool) => ProbDist.single (x, x)), ProbDist.map_map]
    exact Subtype.ext (fTransform_single _ _ _)
  · -- The outer identity flip reaches exactly the state produced by the write.
    exact Subtype.ext (fTransform_single _ _ _)
  · -- The inner identity read reaches the state produced by the flip.
    simp only [routedStep, Program.leftStep, writerReader,
      Program.probCombine_sum_inr _ Program.forward_bounded,
      Program.probCombine_forward _ _ Nat.zero_lt_one, threePortsStep, registerStep,
      ProbDist.map_map]
    exact Subtype.ext (fTransform_single _ _ _)

#print axioms TypedConverter.parallel_id_smul_ofProbAutomaton
#print axioms TypedConverter.id_parallel_smul_ofProbAutomaton
#print axioms nested_register
#print axioms nested_write_flip_read

end SystemAlgebra.Tests.JointAutomatonAttachment
