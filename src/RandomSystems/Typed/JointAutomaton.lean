module

public import RandomSystems.Converter.ProbProgramTensor
public import RandomSystems.Typed.ProgramTensor
public import RandomSystems.Typed.ProbProgramAttachment

/-!
# Attaching a converter to one side of a joint automaton

A joint automaton on `B ⊗ D` draws one state `r ← μ`. A query on either side can change it.
`parallel_id_smul_ofProbAutomaton` attaches a program on the left and
`id_parallel_smul_ofProbAutomaton` attaches one on the right. Both keep only the active
program's state alongside `r`. For a left attachment:

```text
left query   (s,r) ── P on the left ports of the joint automaton ──► ((s',r'), reply)
right query  (s,r) ── one joint transition at the right port    ──► ((s, r'), reply)
```

The parallel program representation gives the joint attachment law below. The state map
inserting the forwarding program's unit state yields the two one-sided laws.
-/

@[expose] public section

namespace SystemAlgebra.TypedConverter

open Probability.Distribution

variable
  -- `A ⊗ C` is the outside and `B ⊗ D` the inside interface; `S`, `T` carry program states.
  {A B C D : Interface} {S T : Type}
  -- `P` runs from `s` on `A`'s domain with at most `b` inside queries per invocation; `hP`
  -- certifies its converter from `B.domain` to `A.domain` with that bound.
  (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
  (hP : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
  -- `Q`, `t`, `c`, `hQ` are the same data for the second converter `C → D`.
  (t : T) (Q : Program T C.I D.I C.X C.Y D.X D.Y) {c : ℕ} (hc : Q.Bounded c)
  (hQ : IsDDCFrom D.domain C.domain c (DDC.ofProgramOn t Q C.domain))

/-- **Attachment to a joint automaton.** The two converters attached to an automaton whose one
state `r` serves both `B` and `D` form the automaton of `(P.sum Q).probCombine step`, started at
`((s, t), r)` with `r ← μ`. -/
theorem parallel_ofDDC_ofProgramOn_smul_ofProbAutomaton {R : Type}
    -- `step` is the joint transition on `B ⊗ D`; `μ` draws its initial state once.
    (step : ProbStep R (B.tensor D).I (B.tensor D).X (B.tensor D).Y) (μ : ProbDist R) :
    TypedConverter.parallel (TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain) hP)
        (TypedConverter.ofDDC (DDC.ofProgramOn t Q C.domain) hQ) •
        TypedSystem.ofProbAutomaton (B.tensor D) step μ =
      TypedSystem.ofProbAutomaton (A.tensor C) ((P.sum Q).probCombine step (hb.sum hc))
        (μ.map fun r => ((s, t), r)) := by
  rw [parallel_ofDDC_ofProgramOn s P hb hP t Q hc hQ]
  -- The paired program attached to the automaton is its combined automaton.
  exact Subtype.ext (PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton
    (B.tensor D).nonempty_prefix (A.tensor C).nonempty_prefix (s, t) (P.sum Q) (hb.sum hc) _
    step μ)

/-- Attach `P` on the left. Its private state starts at `s`; both sides update the same
resource state drawn once from `μ`. -/
lemma parallel_id_smul_ofProbAutomaton {E : Interface} {R : Type}
    -- `step` is the joint transition on `B ⊗ E`; `μ` draws its initial state once.
    (step : ProbStep R (B.tensor E).I (B.tensor E).X (B.tensor E).Y) (μ : ProbDist R) :
    TypedConverter.parallel (TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain) hP)
        (TypedConverter.id E) • TypedSystem.ofProbAutomaton (B.tensor E) step μ =
      TypedSystem.ofProbAutomaton (A.tensor E) (P.leftStep hb step) (μ.map fun r => (s, r)) := by
  -- Present the identity by its one-call program and apply joint program attachment.
  rw [id_eq_ofDDC_forward,
    parallel_ofDDC_ofProgramOn_smul_ofProbAutomaton s P hb hP () _ Program.forward_bounded _]
  -- Inserting unit for the forwarding branch preserves each transition and the initial draw.
  let embed (p : S × R) := ((p.1, ()), p.2)
  have sim := TypedSystem.ofProbAutomaton_eq_of_stateMap (A := A.tensor E)
    (P.leftStep hb step)
    ((P.sum (Program.forward E.I E.X E.Y)).probCombine step (hb.sum Program.forward_bounded))
    embed (by
      rintro ⟨s₀, r⟩ (i | j) x
      all_goals dsimp only [embed]
      · rw [Program.probCombine_sum_inl step hb]
        rfl
      · rw [Program.probCombine_sum_inr step Program.forward_bounded,
          Program.probCombine_forward _ _ Nat.zero_lt_one, ProbDist.map_map]
        simp only [Program.leftStep, ProbDist.map_map]
        rfl) (μ.map fun r => (s, r))
  rw [ProbDist.map_map] at sim
  exact sim.symm

/-- Attach `Q` on the right. A left query reaches the joint automaton directly and
preserves `Q`'s state. -/
lemma id_parallel_smul_ofProbAutomaton {E : Interface} {R : Type}
    -- `step` is the joint transition on `E ⊗ D`; `μ` draws its initial state once.
    (step : ProbStep R (E.tensor D).I (E.tensor D).X (E.tensor D).Y) (μ : ProbDist R) :
    TypedConverter.parallel (TypedConverter.id E)
        (TypedConverter.ofDDC (DDC.ofProgramOn t Q C.domain) hQ) •
        TypedSystem.ofProbAutomaton (E.tensor D) step μ =
      TypedSystem.ofProbAutomaton (E.tensor C) (Q.rightStep hc step) (μ.map fun r => (t, r)) := by
  -- Present the identity by its one-call program and apply joint program attachment.
  rw [id_eq_ofDDC_forward,
    parallel_ofDDC_ofProgramOn_smul_ofProbAutomaton () _ Program.forward_bounded _ t Q hc hQ]
  -- Inserting unit for the forwarding branch preserves each transition and the initial draw.
  let embed (p : T × R) := (((), p.1), p.2)
  have sim := TypedSystem.ofProbAutomaton_eq_of_stateMap (A := E.tensor C)
    (Q.rightStep hc step)
    (((Program.forward E.I E.X E.Y).sum Q).probCombine step (Program.forward_bounded.sum hc))
    embed (by
      rintro ⟨s₀, r⟩ (i | j) x
      all_goals dsimp only [embed]
      · rw [Program.probCombine_sum_inl step Program.forward_bounded,
          Program.probCombine_forward _ _ Nat.zero_lt_one, ProbDist.map_map]
        simp only [Program.rightStep, ProbDist.map_map]
        rfl
      · rw [Program.probCombine_sum_inr step hc]
        rfl) (μ.map fun r => (t, r))
  rw [ProbDist.map_map] at sim
  exact sim.symm

end SystemAlgebra.TypedConverter
