module

public import RandomSystems.Typed.ReplyTransform.Basic
public import RandomSystems.Typed.Memoryless

/-!
# Laws of fresh randomized reply transformations

`sampleReplyProgram_memorylessReplyLaw` computes the independent source/resource reply law.
`TypedConverter.sampleReplies_smul_ofMemoryless` factors attachment through the independent
source and resource, applies their parallel memoryless law, then uses that invocation contract.
The model and its domain certificates are in `RandomSystems.Typed.ReplyTransform.Basic`.
-/

@[expose] public section

namespace SystemAlgebra

open DSL Probability Probability.Distribution

-- `I` indexes queries `X i` and inside replies `Z i`; `K` carries fresh randomness and `Y` replies.
variable {I : Type} {X Z : I → Type} {Y K : Type}

/-- An invocation returns the pushforward of the independent pair `(k,z) ∼ P × ν i x`. -/
lemma sampleReplyProgram_memorylessReplyLaw
    -- `P` supplies the fresh auxiliary value; `f i` combines it with the resource reply.
    (P : ProbDist K) (f : ∀ i, K → Z i → Y)
    -- `ν i x` is the resource's fresh reply law; `s` is the unique state at query `i(x)`.
    (ν : ∀ i, X i → ProbDist (Z i)) (s : Unit) (i : I) (x : X i) :
    (sampleReplyProgram f).memorylessReplyLaw
        (RandomSystem.parallelLaw ν (fun _ _ => P)) s i x 2 [] =
      ((prodProbDist P (ν i x)).map (fun kz => f i kz.1 kz.2)).1 := by
  -- Read the source value and resource reply, then push their joint law through `f i`.
  simp only [Program.memorylessReplyLaw, sampleReplyProgram, callProg, returnProg,
    List.nil_append, List.cons_append, ↓reduceDIte, RandomSystem.parallelLaw,
    ProbDist.map_val, prodProbDist_val]
  rw [prod_eq_bindK, fTransform_bindK]
  apply bindK_congr
  intro k _
  rw [fTransform_fTransform, bindK_single_comp]
  rfl

namespace TypedConverter

-- These typed components use finite ports and alphabets, with allowance `q i` at each port.
variable [Fintype I] [∀ i, Fintype (X i)] [∀ i, Fintype (Z i)] [Fintype Y] [Fintype K]

/-- Fresh resource law `ν i x` gives fresh outside law `(k,z) ↦ f i k z` under `P × ν i x`. -/
lemma sampleReplies_smul_ofMemoryless
    -- `q i` bounds calls; `P` is the auxiliary law and `f i` computes the outside reply.
    (q : I → ℕ) (P : ProbDist K) (f : ∀ i, K → Z i → Y)
    -- `ν i x` is the inside reply law, independent of previous replies and source draws.
    (ν : ∀ i, X i → ProbDist (Z i)) :
    sampleReplies I X Z q P f • TypedSystem.ofMemoryless (Interface.portBudget I X Z q) ν =
      TypedSystem.ofMemoryless (Interface.portBudget I X (fun _ => Y) q)
        (fun i x => (prodProbDist P (ν i x)).map (fun kz => f i kz.1 kz.2)) := by
  calc
    -- Attachment places the independent source beside the resource, then runs the program.
    sampleReplies I X Z q P f •
        TypedSystem.ofMemoryless (Interface.portBudget I X Z q) ν =
      sampleRepliesProgram I X Z q f • TypedSystem.parallel
        (TypedSystem.ofMemoryless (Interface.portBudget I X Z q) ν)
        (TypedSystem.source P (2 * (Interface.portBudget I X Z q).bound)) := by
      rw [sampleReplies, comp_smul, attach_rightContext]
    -- Reading successive source entries gives the fresh auxiliary law on every call.
    _ = sampleRepliesProgram I X Z q f • TypedSystem.parallel
        (TypedSystem.ofMemoryless (Interface.portBudget I X Z q) ν)
        (TypedSystem.ofMemoryless
          (Interface.source K (2 * (Interface.portBudget I X Z q).bound))
          (fun _ _ => P)) := by rw [TypedSystem.source_eq_ofMemoryless]
    -- Independent components expose the combined portwise law used by the invocation contract.
    _ = sampleRepliesProgram I X Z q f • TypedSystem.ofMemoryless
        (Interface.tensor (Interface.portBudget I X Z q)
          (Interface.source K (2 * (Interface.portBudget I X Z q).bound)))
        (RandomSystem.parallelLaw ν (fun _ _ => P)) := by
      rw [TypedSystem.parallel_ofMemoryless]
    -- The state-independent invocation law identifies every cumulative probability.
    _ = _ := ofPreservingProgram_smul_ofMemoryless _ _ _ _ _ _ _ _ rfl
      (sampleReplyProgram_memorylessReplyLaw P f ν)

end TypedConverter
end SystemAlgebra
