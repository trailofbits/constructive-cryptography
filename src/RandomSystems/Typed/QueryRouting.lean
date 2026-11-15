module

public import RandomSystems.Converter.QueryRoutingProgram
public import RandomSystems.Converter.ProgramSchedule
public import RandomSystems.Typed.DSL.Programs
public import RandomSystems.Typed.CallFunctional
public import RandomSystems.Typed.Memoryless
public import RandomSystems.Typed.ProbProgramAttachment

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

## Main results

* `TypedConverter.routingAt_smul_ofProbAutomaton`: every routed call updates the same inside
  state and translates its reply at the requested port.
* `TypedConverter.routingAt_smul_ofMemoryless`: at `request u = (j,x)`, the outside reply law
  is the image of the fresh inside law at `j(x)` under `answer u`. Point laws give
  `TypedConverter.routingAt_smul_ofFunction`.
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

section RequestedPort

variable {A B : Interface}
  -- On outside input `u`, request one inside port and input; translate its typed reply.
  (request : (Σ o, A.X o) → Σ j, B.X j)
  (answer : (u : Σ o, A.X o) → B.Y (request u).1 → A.Y u.1)

/-- The program for `u ↦ (j,x) ↦ y ↦ answer u y` retains only the current input. -/
noncomputable def routingAtProgram : Program Unit A.I B.I A.X A.Y B.X B.Y :=
  fun _ o x => DSL.callProg (request ⟨o, x⟩).1 (request ⟨o, x⟩).2 fun y =>
    DSL.returnProg ((), answer ⟨o, x⟩ y)

/-- The reply translation returns immediately after the one designated call. -/
lemma routingAtProgram_costs : (routingAtProgram request answer).Costs (fun _ => 1) :=
  fun _ _ _ => DSL.callCost_call _ _ _ fun _ => DSL.callCost_return _

/-- One inside call suffices to finish any invocation of the router. -/
lemma routingAtProgram_bounded : (routingAtProgram request answer).Bounded 1 :=
  fun s o x h q hc hq => (routingAtProgram_costs request answer s o x h hc).1 q hq

/-- Route `u` to `(j,x) = request u` and return `answer u y` for its reply `y : B.Y j`. -/
noncomputable def routingAt (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → B.Y (request u).1 → A.Y u.1)
    -- Each admitted outside history maps to an admitted history on B.
    (hmap : ∀ us, A.domain us → B.domain (us.map request)) : TypedConverter A B :=
  ofDDC (b := 1) (DDC.ofProgramOn () (routingAtProgram request answer) A.domain) (by
    -- The singleton schedule covers the pending request as well as completed calls.
    refine DDC.ofProgramOn_isDDCFrom_of_schedule (fun u => [request u])
      (routingAtProgram_costs request answer) ?_ (b := 1) (fun _ => le_rfl)
      B.nonempty_prefix.2 A.nonempty_prefix.2 ?_
    · intro s o x h q hc hq
      have hl := ((routingAtProgram_costs request answer s o x h hc).1 q hq)
      have he := List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp hl)
      subst h
      exact congrArg some (Sum.inr.inj hq)
    · intro us hus
      exact Or.inr (by simpa only [List.map_eq_flatMap] using hmap us hus))

/-- At `request u = (j,x)`, a fresh draw `y ← ν j x` gives the outside reply `answer u y`. -/
lemma routingAt_smul_ofMemoryless
    -- Mapping an admitted history by `request` keeps every call inside the domain of `B`.
    (hmap : ∀ us, A.domain us → B.domain (us.map request))
    (ν : ∀ j, B.X j → ProbDist (B.Y j)) :
    routingAt request answer hmap • TypedSystem.ofMemoryless B ν =
      TypedSystem.ofMemoryless A (fun o x =>
        (ν (request ⟨o, x⟩).1 (request ⟨o, x⟩).2).map (answer ⟨o, x⟩)) := by
  -- Program attachment reduces the equality to the reply law of one invocation.
  apply Subtype.ext
  refine PDCBehavior.attach_ofDDC_ofProgramOn_memoryless B.nonempty_prefix A.nonempty_prefix
    () (routingAtProgram request answer) (routingAtProgram_bounded request answer) _ (ν := ν)
    (κ := fun o x => (ν (request ⟨o, x⟩).1 (request ⟨o, x⟩).2).map (answer ⟨o, x⟩))
    ?_ rfl (TypedSystem.ofMemoryless B ν).2
  intro s o x
  -- The lone call draws from ν; the continuation returns the image of that draw.
  rw [Program.memorylessReplyLaw_succ_inr (by rfl)]
  simpa only [routingAtProgram, Program.memorylessReplyLaw, DSL.callProg, DSL.returnProg,
    List.nil_append, ↓reduceDIte, ProbDist.map_val] using
    bindK_single_comp (ν (request ⟨o, x⟩).1 (request ⟨o, x⟩).2).1 (answer ⟨o, x⟩)

/-- Attachment to a fixed oracle computes `g(u) = answer u (f j x)` at `request u = (j,x)`. -/
lemma routingAt_smul_ofFunction
    (hmap : ∀ us, A.domain us → B.domain (us.map request))
    -- `f j x` is the inside oracle's reply at the requested port.
    (f : ∀ j, B.X j → B.Y j) :
    routingAt request answer hmap • TypedSystem.ofFunction f =
      TypedSystem.ofFunction (fun o x =>
        answer ⟨o, x⟩ (f (request ⟨o, x⟩).1 (request ⟨o, x⟩).2)) := by
  change routingAt request answer hmap •
      TypedSystem.ofMemoryless B (fun j x => ProbDist.single (f j x)) =
    TypedSystem.ofMemoryless A (fun o x =>
      ProbDist.single (answer ⟨o, x⟩ (f _ (request ⟨o, x⟩).2)))
  rw [routingAt_smul_ofMemoryless]
  -- A translated point mass is the point mass at the translated reply.
  congr 1
  funext o x
  exact Subtype.ext (fTransform_single _ _ _)

/-- One invocation updates the inside state from `r` to `r'` and translates only its reply. -/
lemma routingAtProgram_probCombine {R : Type}
    (step : ProbStep R B.I B.X B.Y) (r : R) (o : A.I) (x : A.X o) :
    (routingAtProgram request answer).probCombine step (routingAtProgram_bounded request answer)
        ((), r) o x =
      (step r (request ⟨o, x⟩).1 (request ⟨o, x⟩).2).map
        (fun p => (((), p.1), answer ⟨o, x⟩ p.2)) := by
  apply Subtype.ext
  change (routingAtProgram request answer).probInvoke step () o x (0 + 1) r [] = _
  -- Draw the inside transition at the requested port.
  rw [Program.probInvoke_succ_inr (by rfl)]
  simp only [ProbDist.map_val, ProbStep.outcome, ProbStep.tagged, bindK_fTransform,
    Function.comp_def, List.nil_append]
  -- On reply y, the continuation returns a point mass at the translated reply.
  rw [← bindK_single_comp]
  congr 1
  funext p
  apply Program.probInvoke_inl (a := ((), answer ⟨o, x⟩ p.2))
  simp only [routingAtProgram, DSL.callProg, DSL.returnProg, ↓reduceDIte]

/-- For `request u = (j,x)`, draw `(r',y) ← step r j x`, keep `r'` and return `answer u y`.
All outside ports share the single state initialized by `μ`. -/
lemma routingAt_smul_ofProbAutomaton {R : Type}
    -- Every requested history must be legal for the inside automaton.
    (hmap : ∀ us, A.domain us → B.domain (us.map request))
    -- `step` updates the retained state in `R`; `μ` is its initial law.
    (step : ProbStep R B.I B.X B.Y) (μ : ProbDist R) :
    routingAt request answer hmap • TypedSystem.ofProbAutomaton B step μ =
      TypedSystem.ofProbAutomaton A (fun r o x =>
        (step r (request ⟨o, x⟩).1 (request ⟨o, x⟩).2).map
          (fun p => (p.1, answer ⟨o, x⟩ p.2))) μ := by
  -- Program attachment pairs the router's unit state with the one inside state.
  let δ := (routingAtProgram request answer).probCombine step (routingAtProgram_bounded _ _)
  calc
    _ = TypedSystem.ofProbAutomaton A δ (μ.map fun r => ((), r)) :=
      Subtype.ext (PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton
        B.nonempty_prefix A.nonempty_prefix () _ (routingAtProgram_bounded request answer) _ step μ)
    -- The state map r ↦ ((), r) commutes with the single routed transition.
    _ = _ := by
      symm
      apply TypedSystem.ofProbAutomaton_eq_of_stateMap _ δ (fun r => ((), r))
      intro r o x
      dsimp only [δ]
      rw [routingAtProgram_probCombine, ProbDist.map_map]
      rfl

end RequestedPort

end SystemAlgebra.TypedConverter
