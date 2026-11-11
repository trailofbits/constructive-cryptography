module

public import RandomSystems.Typed.DSL.Converters
public import RandomSystems.Typed.Context

/-!
# Fresh randomized reply transformations

`TypedConverter.sampleReplies` draws `k ∼ P`, forwards the current input once, and returns
`f i k z` on the inside reply `z`. It assembles `sampleReplyProgram` with `TypedSystem.source`;
the source and inside resource are independent. Each invocation consumes another source value.
The source retains an independent sample table with capacity `2 * ∑ i, q i`, matching the
program's total-call bound; each invocation uses one entry and makes one resource query.

```text
caller ── i(x) ──► [sampleReplyProgram]
                    1. source P: () ↦ k
                    2. resource: i(x) ↦ z
caller ◄─ f i k z ──┘
```

`sampleReplyProgram_bounded` limits each invocation to two calls. Port preservation permits
at most one protected query, at the matching resource port. The attachment law in
`RandomSystems.Typed.ReplyTransform` identifies the resulting independent reply law.
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

/-- An invocation at `i` queries resource port `inl i` at most once and no other resource port. -/
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

end TypedConverter
end SystemAlgebra
