module

public import RandomSystems.Typed.DSL.Programs
public import RandomSystems.System.Memoryless
public import Probability.DependentProduct

/-!
# Ordered collection of heterogeneous replies

`collectCalls` composes the existing call and return bodies to visit an explicit `Fin n` schedule.
Replies retain their requested types; `finish` receives the dependent tuple. The schedule describes
actual invocation order, while the inside interface keeps its original port labels.

`collectCalls_cost` gives exactly `n` calls and `collectCalls_next` gives their exact order.
`collectCalls_reply` computes the result of matching replies. Against fresh inside laws,
`Program.memorylessReplyLaw_collectCalls` gives the pushforward of their independent product,
using `piDep_fin_zero` and `piDep_fin_succ` from `Probability.DependentProduct`.

```text
outside input → request 0 → reply 0 → … → request (n-1) → reply (n-1) → finish tuple
```

The empty schedule returns immediately. This finite schedule implements the bounded inside
queries of [1, Definition 2.2.2, pp. 17–18]; matching-port admission is inherited from `callProg`.

## References

1. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis, ETH Zurich, 2020.
-/

@[expose] public section

open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution

namespace SystemAlgebra.DSL

-- `J` carries inside ports, `X` and `Y` their query/reply types, and `R` the completed result.
variable {J R : Type} {X Y : J → Type}

/-- Query `request 0`, …, `request (n-1)` in order and pass the typed reply tuple to `finish`.
Only matching-port replies advance the existing `callProg`; each invocation uses its own history. -/
noncomputable def collectCalls :
    -- `n` is the number of scheduled calls; `request i` is the port and input at position `i`.
    (n : ℕ) → (request : Fin n → Σ j, X j) →
    -- `finish` consumes all replies, each in the reply type of its own requested port.
    (finish : ((i : Fin n) → Y (request i).1) → R) →
    List ((Σ j, X j) × (Σ j, Y j)) → R ⊕ (Σ j, X j)
  | 0, _, finish => returnProg (finish fun i => Fin.elim0 i)
  | n + 1, request, finish =>
      callProg (request 0).1 (request 0).2 fun y =>
        collectCalls n (fun i => request i.succ) fun ys => finish (Fin.cons y ys)

/-- Collection makes exactly `n` calls along its own exchanges. -/
lemma collectCalls_cost
    -- `request` lists the `n` inside queries; `finish` maps their reply tuple to the result.
    (n : ℕ) (request : Fin n → Σ j, X j)
    (finish : ((i : Fin n) → Y (request i).1) → R) :
    Program.CallCost n (collectCalls n request finish) := by
  induction n with
  | zero => exact callCost_return _
  | succ n ih =>
    -- One matching call precedes the remaining collection.
    exact callCost_call _ _ _ fun _ => ih _ _

/-- A complete sequence of matching replies returns `finish ys`. -/
lemma collectCalls_reply
    -- `request` lists the `n` queries; `finish` combines their replies `ys` into one result.
    (n : ℕ) (request : Fin n → Σ j, X j)
    (finish : ((i : Fin n) → Y (request i).1) → R) (ys : (i : Fin n) → Y (request i).1) :
    collectCalls n request finish
      (List.ofFn fun i => (request i, ⟨(request i).1, ys i⟩)) = .inl (finish ys) := by
  induction n with
  | zero =>
      -- The empty history returns the unique empty tuple.
      have he : (fun i : Fin 0 => Fin.elim0 i) = ys := by funext i; exact Fin.elim0 i
      simp only [collectCalls, returnProg, he]
  | succ n ih =>
      -- Consume the matching first reply, then prepend it to the tail's returned tuple.
      simp only [List.ofFn_succ, collectCalls, callProg, ↓reduceDIte]
      rw [ih]
      exact congrArg (Sum.inl ∘ finish) (Fin.cons_self_tail ys)

/-- After `h.length` consistent exchanges, collection issues that position of its schedule. -/
lemma collectCalls_next
    -- `request` fixes the `n` calls; `finish` computes the result once all replies arrive.
    (n : ℕ) (request : Fin n → Σ j, X j)
    (finish : ((i : Fin n) → Y (request i).1) → R)
    -- `hc` admits the exchange prefix `h`; `hq` says the next output is the inside query `q`.
    (h : List ((Σ j, X j) × (Σ j, Y j))) (q : Σ j, X j)
    (hc : Program.ExchangesOf (collectCalls n request finish) h)
    (hq : collectCalls n request finish h = .inr q) :
    (List.ofFn request)[h.length]? = some q := by
  induction n generalizing h q with
  | zero =>
    -- An empty schedule returns immediately, so it cannot issue a query.
    cases hq
  | succ n ih =>
    cases h with
    | nil =>
      -- Before any reply, the first requested query is issued.
      have he : request 0 = q := Sum.inr.inj hq
      simp only [List.length_nil, List.ofFn_succ, List.getElem?_cons_zero, he]
    | cons z h =>
      -- A consistent first exchange matches the first call; the tail follows the remaining order.
      obtain ⟨y, rfl, he, hc'⟩ := exchangesOf_callProg hc
      rw [collectCalls, he] at hq
      simpa only [List.length_cons, List.ofFn_succ, List.getElem?_cons_succ]
        using ih _ _ h q hc' hq

/-- Against fresh reply laws, ordered collection returns the reply projection `(finish ys).2`
of the independent tuple. The equality holds after a prefix whose remaining body is collection;
this marginal omits the next state `(finish ys).1`. -/
lemma _root_.SystemAlgebra.Program.memorylessReplyLaw_collectCalls
    -- `S` carries states, and `O`, `U`, `V` give the outside ports, inputs and replies of `P`.
    {S O : Type} {U V : O → Type} {P : Program S O J U V X Y}
    -- `P` starts this invocation in state `s` at outside query `o(u)`; `ν` gives fresh inside laws.
    (ν : ∀ j, X j → ProbDist (Y j)) (s : S) (o : O) (u : U o)
    -- `request` lists the remaining `n` calls; `finish` computes the next state and outside reply.
    (n : ℕ) (request : Fin n → Σ j, X j)
    (finish : ((i : Fin n) → Y (request i).1) → S × V o)
    -- `hbody` identifies the body after `priorExchanges` with the remaining ordered calls.
    (priorExchanges : List ((Σ j, X j) × (Σ j, Y j)))
    (hbody : ∀ h, P s o u (priorExchanges ++ h) = collectCalls n request finish h) :
    P.memorylessReplyLaw ν s o u n priorExchanges =
      fTransform (fun ys => (finish ys).2)
        (piDep fun i => (ν (request i).1 (request i).2).1) := by
  induction n generalizing priorExchanges with
  | zero =>
    -- An empty collection returns the unique empty tuple without an inside draw.
    have hr : P s o u priorExchanges = .inl (finish fun i => Fin.elim0 i) := by
      simpa only [List.append_nil, collectCalls, returnProg] using hbody []
    rw [Program.memorylessReplyLaw_inl hr, piDep_fin_zero, fTransform_single]
  | succ n ih =>
    -- Draw the first reply, then apply the induction hypothesis to the remaining calls.
    have hq : P s o u priorExchanges = .inr (request 0) := by
      simpa only [List.append_nil, collectCalls, callProg] using hbody []
    rw [Program.memorylessReplyLaw_succ_inr hq]
    have hcont : ∀ y : Y (request 0).1,
        P.memorylessReplyLaw ν s o u n (priorExchanges ++ [(request 0, ⟨(request 0).1, y⟩)]) =
          fTransform (fun ys => (finish (Fin.cons y ys)).2)
            (piDep fun i : Fin n => (ν (request i.succ).1 (request i.succ).2).1) := by
      intro y
      apply ih
      intro h
      simpa only [List.append_assoc, List.singleton_append, collectCalls, callProg,
        ↓reduceDIte] using hbody ((request 0, ⟨(request 0).1, y⟩) :: h)
    simp_rw [hcont]
    -- Sequentially sampling the first coordinate and its independent tail is the product law.
    rw [piDep_fin_succ, fTransform_fTransform, prod_eq_bindK, fTransform_bindK]
    simp only [fTransform_fTransform, Function.comp_def]

end SystemAlgebra.DSL
