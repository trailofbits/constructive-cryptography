module

public import RandomSystems.Converter.QueryRoutingProgram
public import RandomSystems.Typed.CallFunctional
public import RandomSystems.Typed.Memoryless

/-!
# Typed realization of input-dependent routing

The router of `RandomSystems.Converter.QueryRouting`, attached to the fixed function `f` on the
inside interface `B`, is the fixed function `g` on the outside interface `A`. With
`(j,x) = request u`, the router computes `g(u) = answer u (j, f_j(x))`. The explicit answer map
lets the reply alphabets `B.Y j` differ from `A.Y o` and from each other.

```text
                ┌───────────────────────┐            ┌────────────┐
  o(v)      ──► │ (j,x) = request u     │ ── j(x) ─► │            │
                │ retain u = (o,v)      │            │ y = f_j(x) │
  o ⇒ g(u)  ◄── │ g(u) = answer u (j,y) │ ◄─ j ⇒ y ─ │            │
                └───────────────────────┘            └────────────┘
```

`mapReplies A f` forwards each query unchanged and returns `f i y` in a common output alphabet.
It preserves `A.domain` exactly.

## Main results

* `mapReplies_smul_ofFunction`, `mapReplies_smul_ofMemoryless` and `mapReplies_smul_source`:
  contracts for reply mapping on deterministic systems, fresh laws and sources
* `TypedConverter.routing`: one inside query and a translated reply, with an explicit domain map
* `TypedConverter.routing_smul_ofFunction`: `α • ofFunction f = ofFunction g`
* `TypedConverter.routing_smul_ofMemoryless`: fresh inside replies stay fresh; their laws are
  pushed forward through `answer` after selecting the query with `request`

The deterministic contract uses the completed-call law. The memoryless contract uses
`routingConverter_eq_ofProgramOn` to transport the program attachment law, then reduces its
single draw to `ProbDist.map`.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace SystemAlgebra.TypedConverter

/-- **The router attached to a fixed function**: if `(j,x) = request u`, the router `α` on the
outside domain `A.domain`, attached to `f`, is the function `g(u) = answer u (j, f_j(x))`:
`α • ofFunction f = ofFunction g`. The domain guarantee `ha` comes from
`routingConverter_isDDCFrom` with `F = A.domain`, `E = B.domain`, given
`F us → E (us.map request)`.

[1, Definition 3.9, p. 62]: “Whenever α outputs (in, x), then x is given as input
to s⊥, and if y ∈ Y ∪ {⊥} is the output of s⊥, then y is given as input to α. Whenever α
outputs (out, v), then v is defined to be the output of αs ...” -/
lemma ofDDC_routingConverter_smul_ofFunction {A B : Interface}
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    (ha : IsDDCFrom B.domain A.domain 1
      (routingConverter request answer A.domain))
    (f : ∀ j, B.X j → B.Y j) :
    ofDDC (routingConverter request answer A.domain) ha • TypedSystem.ofFunction f =
      TypedSystem.ofFunction (fun o u => answer ⟨o, u⟩
        ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩) := by
  -- A DDC that answers every admitted history like `g`, querying `f` at `[request u]`,
  -- turns `f` into `g` (the typed attachment law `ofDDC_smul_ofFunction`).
  apply ofDDC_smul_ofFunction ha f
    (fun o u => answer ⟨o, u⟩
      ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩)
    (fun u => [request u])
  -- The completed transcript of each admitted history is `replies_routingConverter_ofFunction`.
  intro us hUs
  simpa only [List.map_singleton, Sigma.eta] using
    replies_routingConverter_ofFunction request answer A.nonempty_prefix.2 f us hUs

open Probability.Distribution

/-- On outside input `u`, query `request u = (j,x)` once and return `answer u (j,y)` on reply
`y`. The current input is retained until that reply; successive reply computations share no state.
The outside-history filter admits only empty outside-input histories or histories in `A.domain`.
The domain map admits every requested inside history, including a pending invocation. -/
noncomputable def routing
    -- `A`, `B` are the outside and inside interfaces with their declared domains.
    {A B : Interface}
    -- `request u` selects the inside port and query value from the outside input `u`.
    (request : (Σ o, A.X o) → Σ j, B.X j)
    -- `answer u r` translates the inside reply `r` at the original outside port `u.1`.
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    -- `hmap` preserves the inside domain for every admitted outside history `us`.
    (hmap : ∀ us, A.domain us → B.domain (us.map request)) : TypedConverter A B :=
  ofDDC (routingConverter request answer A.domain)
    (routingConverter_isDDCFrom request answer A.nonempty_prefix.2 hmap)

/-- One-query translation of the function `f` returns `answer u (j, f j x)`, where
`request u = (j,x)`. -/
lemma routing_smul_ofFunction
    -- `A`, `B` carry outside and inside queries, replies, and domains.
    {A B : Interface}
    -- `request` encodes the input; `answer` translates the inside reply for that input.
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    -- `hmap` guarantees legal inside histories; `f` is the inside function.
    (hmap : ∀ us, A.domain us → B.domain (us.map request)) (f : ∀ j, B.X j → B.Y j) :
    routing request answer hmap • TypedSystem.ofFunction f =
      TypedSystem.ofFunction (fun o u => answer ⟨o, u⟩
        ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩) :=
  ofDDC_routingConverter_smul_ofFunction request answer _ f

/-- One-query translation of fresh replies with law `ν j x` gives fresh outside replies with
the mapped law of `y ↦ answer u (j,y)`, where `request u = (j,x)`. -/
lemma routing_smul_ofMemoryless
    -- `A`, `B` carry outside and inside queries, replies, and domains.
    {A B : Interface}
    -- `request` chooses the inside query; `answer` translates its reply for the retained input.
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    -- `hmap` admits each inside history; `ν j x` gives the fresh reply law at query `(j,x)`.
    (hmap : ∀ us, A.domain us → B.domain (us.map request))
    (ν : ∀ j, B.X j → ProbDist (B.Y j)) :
    routing request answer hmap • TypedSystem.ofMemoryless B ν =
      TypedSystem.ofMemoryless A (fun o u =>
        ProbDist.map (fun y => answer ⟨o, u⟩ ⟨(request ⟨o, u⟩).1, y⟩)
          (ν (request ⟨o, u⟩).1 (request ⟨o, u⟩).2)) := by
  -- The program presentation has the same canonical schedule and domain as the router.
  have he := routingConverter_eq_ofProgramOn request answer A.domain
  have hp : IsDDCFrom B.domain A.domain 1
      (DDC.ofProgramOn () (routingProgram request answer) A.domain) :=
    he ▸ routingConverter_isDDCFrom request answer A.nonempty_prefix.2 hmap
  have ht : routing request answer hmap =
      ofDDC (DDC.ofProgramOn () (routingProgram request answer) A.domain) hp := by
    unfold routing
    congr 1
  -- The single fresh inside reply is pushed forward by the input-dependent answer map.
  let κ : ∀ o, A.X o → ProbDist (A.Y o) := fun o u =>
    ProbDist.map (fun y => answer ⟨o, u⟩ ⟨(request ⟨o, u⟩).1, y⟩)
      (ν (request ⟨o, u⟩).1 (request ⟨o, u⟩).2)
  have hκ : ∀ s o u, (routingProgram request answer).memorylessReplyLaw ν s o u 1 [] =
      (κ o u).1 := by
    intro s o u
    rw [Program.memorylessReplyLaw_succ_inr (by rfl)]
    simpa only [κ, Program.memorylessReplyLaw, routingProgram, List.nil_append,
      List.map_cons, List.map_nil, routingCall, Sum.map_inl, ProbDist.map_val, id_eq] using
      bindK_single_comp (ν (request ⟨o, u⟩).1 (request ⟨o, u⟩).2).1
        (fun y => answer ⟨o, u⟩ ⟨(request ⟨o, u⟩).1, y⟩)
  rw [ht]
  exact Subtype.ext (PDCBehavior.attach_ofDDC_ofProgramOn_memoryless
    B.nonempty_prefix A.nonempty_prefix () (routingProgram request answer)
    (routingProgram_bounded request answer) hp hκ rfl (TypedSystem.ofMemoryless B ν).2)

/-- Forward query `(i,x)` once and return `f i y` on reply `y : A.Y i`.
The outside interface retains `A.domain`; successive calls share no converter state.
`routingConverter_isDDCFrom` certifies the one-call bound; `routingConverter_query_count`
counts exactly one inside query per outside input, including a pending call. -/
noncomputable def mapReplies
    -- `A` is the inside interface, including any restrictions on its input histories.
    (A : Interface)
    -- `Y` is the common outside reply alphabet; `f i` transforms replies at port `i`.
    {Y : Type} [Fintype Y] (f : ∀ i, A.Y i → Y) :
    TypedConverter (A.withReplies (fun _ => Y)) A :=
  routing id (fun _ r => f r.1 r.2)
    (fun _ h => by simpa only [List.map_id] using h)

/-- Transforming the fixed reply `g i x` returns `f i (g i x)` on the same domain. -/
lemma mapReplies_smul_ofFunction
    -- `A` fixes the admitted queries; `f i` maps their inside replies to `Y`.
    (A : Interface) {Y : Type} [Fintype Y] (f : ∀ i, A.Y i → Y)
    -- `g i x` is the deterministic inside reply to query `x` at port `i`.
    (g : ∀ i, A.X i → A.Y i) :
    mapReplies A f • TypedSystem.ofFunction g =
      TypedSystem.ofFunction (A := A.withReplies (fun _ => Y)) (fun i x => f i (g i x)) :=
  routing_smul_ofFunction _ _ _ _

/-- Fresh replies with law `ν i x` become fresh replies with law `(ν i x).map (f i)`. -/
lemma mapReplies_smul_ofMemoryless
    -- `A` fixes the admitted queries; `f i` transforms inside replies into `Y`.
    (A : Interface) {Y : Type} [Fintype Y] (f : ∀ i, A.Y i → Y)
    -- `ν i x` is the fresh inside reply law at query `(i,x)`.
    (ν : ∀ i, A.X i → ProbDist (A.Y i)) :
    mapReplies A f • TypedSystem.ofMemoryless A ν =
      TypedSystem.ofMemoryless (A.withReplies (fun _ => Y)) (fun i x => (ν i x).map (f i)) :=
  routing_smul_ofMemoryless _ _ _ _

/-- Mapping each source reply by `f` gives the source of `P.map f`, with the same allowance. -/
lemma mapReplies_smul_source
    -- `X`, `Y` are the inside and outside reply alphabets; `f` transforms one reply.
    {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y)
    -- `P` supplies fresh inside replies, for at most `q` calls.
    (P : ProbDist X) (q : ℕ) :
    mapReplies (Interface.source X q) (fun _ => f) • TypedSystem.source P q =
      TypedSystem.source (P.map f) q := by
  rw [TypedSystem.source_eq_ofMemoryless, TypedSystem.source_eq_ofMemoryless]
  exact mapReplies_smul_ofMemoryless _ _ _

end SystemAlgebra.TypedConverter
