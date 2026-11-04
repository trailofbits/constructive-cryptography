module

public import RandomSystems.Typed.QueryRouting

/-!
# Fresh randomized reply transformations

`TypedConverter.sampleReplies` draws `k ∼ P`, forwards the current input once, and returns
`f i k z` on the inside reply `z`. It assembles `sampleReplyProgram` with `TypedSystem.source`;
the source and inside resource are independent. Each invocation consumes another source value.

```text
caller ── i(x) ──► [sampleReplyProgram]
                    1. source P: () ↦ k
                    2. resource: i(x) ↦ z
caller ◄─ f i k z ──┘
```

`sampleReplyProgram_bounded` limits each invocation to two calls. Port preservation assigns
one call to the inside resource's matching port. `sampleReplyProgram_memorylessReplyLaw`
computes one reply law; `sampleReplies_smul_ofMemoryless` lifts it to the entire system.

-/

@[expose] public section

namespace SystemAlgebra

open DSL Probability Probability.Distribution

-- `I` indexes queries `X i` and inside replies `Z i`; `K` carries fresh randomness and `Y` replies.
variable {I : Type} {X Z : I → Type} {Y K : Type}

/-- On `i(x)`, query the auxiliary source, then inside port `i`, and return `f i k z`.
The state is `Unit`; `k` is used only within this invocation. -/
noncomputable def sampleReplyProgram
    -- `f i` combines a fresh value `k : K` and inside reply `z : Z i` into the outside reply.
    (f : ∀ i, K → Z i → Y) :
    Program Unit I (I ⊕ Unit) X (fun _ => Y) (Sum.rec X (fun _ => Unit))
      (Sum.rec Z (fun _ => K)) := fun _ i x =>
  callProg (.inr ()) () fun k =>
    callProg (.inl i) x fun z => returnProg ((), f i k z)

/-- One source call followed by one resource call uses at most two inside queries. -/
lemma sampleReplyProgram_bounded (f : ∀ i, K → Z i → Y) :
    (sampleReplyProgram (X := X) f).Bounded 2 := by
  intro s i x
  exact callBound_call _ _ _ (fun _ => callBound_call _ _ _ (fun _ => callBound_return 0 _))

/-- An invocation at `i` calls resource port `inl i` once and no other resource port. -/
lemma sampleReplyProgram_portPreserving (f : ∀ i, K → Z i → Y) :
    (sampleReplyProgram (X := X) f).PortPreserving (fun i => some (.inl i)) := by
  intro s i x
  -- The source port is outside the protected resource ports.
  apply preservesAt_call_other
  · intro k
    -- The sole resource call matches `i`; returning makes no further query.
    apply preservesAt_call_self
    · intro z; exact avoids_return _ _
    · intro j hj; exact Sum.inl.inj (Option.some.inj hj)
  · intro j hj; cases hj

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

/-- The two-call program on per-port domains, before supplying its independent source.
The resource keeps allowance `q i`; the source allows the total call bound `2 * ∑ i, q i`. -/
noncomputable def sampleRepliesProgram
    -- `I`, `X`, `Z` specify the resource ports, queries and replies.
    (I : Type) [Fintype I] (X Z : I → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Z i)]
    -- `q i` bounds outside and resource calls at `i`; `f i` combines replies with fresh `K`.
    (q : I → ℕ) (f : ∀ i, K → Z i → Y) :
    TypedConverter (Interface.portBudget I X (fun _ => Y) q)
      (Interface.tensor (Interface.portBudget I X Z q)
        (Interface.source K (2 * (Interface.portBudget I X Z q).bound))) :=
  ofPreservingProgram () (sampleReplyProgram f) (sampleReplyProgram_bounded f)
    (fun i => some (.inl i)) (sampleReplyProgram_portPreserving f) q (fun _ hd => hd.2)
    (fun ys hne hl hc => Interface.perPort_tensor_admits
      (A := Interface.portBudget I X Z q)
      (B := Interface.source K (2 * (Interface.portBudget I X Z q).bound)) q
      (fun _ hn hq => ⟨hn, hq⟩) (fun _ hn hq => ⟨hn, hq⟩)
      ys hne hl (fun i => hc i _ rfl))

/-- Draw `k ∼ P` afresh, forward `i(x)` once, then return `f i k z` on resource reply `z`.
Both public interfaces permit `q i` calls at port `i`. -/
noncomputable def sampleReplies
    -- `I`, `X`, `Z` specify the resource ports, queries and replies.
    (I : Type) [Fintype I] (X Z : I → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Z i)]
    -- `q` supplies per-port allowances; `P` supplies independent auxiliary values in `K`.
    (q : I → ℕ) (P : ProbDist K) (f : ∀ i, K → Z i → Y) :
    TypedConverter (Interface.portBudget I X (fun _ => Y) q) (Interface.portBudget I X Z q) :=
  comp (sampleRepliesProgram I X Z q f)
    (rightContext _ (TypedSystem.source P (2 * (Interface.portBudget I X Z q).bound)))

/-- Fresh resource law `ν i x` gives fresh outside law `(k,z) ↦ f i k z` under `P × ν i x`. -/
lemma sampleReplies_smul_ofMemoryless
    -- `q i` bounds calls; `P` is the auxiliary law and `f i` computes the outside reply.
    (q : I → ℕ) (P : ProbDist K) (f : ∀ i, K → Z i → Y)
    -- `ν i x` is the inside reply law, independent of previous replies and source draws.
    (ν : ∀ i, X i → ProbDist (Z i)) :
    sampleReplies I X Z q P f • TypedSystem.ofMemoryless (Interface.portBudget I X Z q) ν =
      TypedSystem.ofMemoryless (Interface.portBudget I X (fun _ => Y) q)
        (fun i x => (prodProbDist P (ν i x)).map (fun kz => f i kz.1 kz.2)) := by
  -- Attachment places the independent source beside the resource, then runs the program.
  rw [sampleReplies, comp_smul, attach_rightContext,
    TypedSystem.source_eq_ofMemoryless, TypedSystem.parallel_ofMemoryless]
  -- The invocation law is state-independent, so it identifies every cumulative probability.
  exact ofPreservingProgram_smul_ofMemoryless _ _ _ _ _ _ _ _ rfl
    (sampleReplyProgram_memorylessReplyLaw P f ν)

end TypedConverter
end SystemAlgebra
