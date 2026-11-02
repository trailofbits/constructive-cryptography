module

public import RandomSystems.Typed.DSL.Collect
public import RandomSystems.Converter.ProgramSchedule
public import RandomSystems.System.Restriction
public import RandomSystems.Typed.ParallelAllMemoryless
public import Mathlib.Data.List.FinRange

/-!
# Collecting a finite family in an explicit order

`TypedConverter.collect` sends one query to each tagged component of `⨂ k, B k` and combines
its heterogeneous replies into one outside reply. The equivalence `order : Fin n ≃ K` chooses
the actual call order; the returned tuple keeps the original index `K`. Each invocation has
exactly `n` calls (`collectProgram_costs`), with the next query given by `collectProgram_next`.

`restrict_collectSchedule_flatMap` identifies component `k`'s complete history with
`us.map (fun u => request u k)`. Thus `collectSchedule_maps_domain` admits complete schedules;
`DDC.ofProgramOn_isDDCFrom_of_schedule` in `Converter.ProgramSchedule` uses prefix closure to
admit pending calls, yielding `collectProgram_isDDCFrom`.

`TypedConverter.collect_smul_parallelAll_ofMemoryless` gives the cumulative reply law.
First, `TypedSystem.parallelAll_ofMemoryless` in `Typed.ParallelAllMemoryless` exposes the
family's memoryless port laws. Then `Program.memorylessReplyLaw_collectCalls` in `Typed.DSL.Collect`
and `fTransform_piDep_piCongrLeft` in `Probability.DependentProduct` give the invocation law
`collectProgram_memorylessReplyLaw`. Finally, `PDCBehavior.attach_ofDDC_ofProgramOn_memoryless`
in `System.Memoryless` lifts that law to cumulative behavior.

`TypedConverter.collect_smul_parallelAll_ofFunction` specializes to fixed replies;
`TypedConverter.collect_smul_parallelAll_source` gives a fresh tuple per invocation. The
collector retains no state; the components retain their own state and supply their own draws.

```text
outside o(u) → collector → order 0 : request u (order 0) → reply 0
                         → …
                         → order (n-1)                 → reply (n-1)
             ← answer u (tuple indexed by K)
```

The fixed schedule is a nonadaptive instance of [1, Definition 2.2.2, pp. 17–18]:
“a bounded number of queries to the inside interfaces”. The tags implement the family view
of [1, p. 17]: “A finite set of resources with disjoint interface sets”. Independence comes
from the existing parallel product, as expressed by `TypedSystem.parallelAll_ofMemoryless`.

## References

1. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis, ETH Zurich, 2020.
-/

@[expose] public section

open Probability Probability.Distribution
open scoped SystemAlgebra

namespace SystemAlgebra

open DSL

-- `K` indexes components `B k`; `A` supplies outside ports, alphabets and the admitted histories.
variable {K : Type} [Fintype K] {A : Interface} {B : K → Interface}
    -- `order` chooses the actual order of the `n` distinct component calls.
    {n : ℕ} (order : Fin n ≃ K)
    -- `request u k` selects the local port and input sent to component `k` for outside input `u`.
    (request : (u : Σ o, A.X o) → (k : K) → Σ j, (B k).X j)
    -- `answer u` combines replies at their original component labels into the outside reply.
    (answer : (u : Σ o, A.X o) → ((k : K) → (B k).Y (request u k).1) → A.Y u.1)

/-- The `i`-th tagged inside query is `request u (order i)`. -/
def collectSchedule
    -- `u` is this invocation's outside input; `i` selects its scheduled call position.
    (u : Σ o, A.X o) (i : Fin n) : Σ j, (⨂ k, B k).X j :=
  ⟨⟨order i, (request u (order i)).1⟩, (request u (order i)).2⟩

/-- Each component appears exactly once in one invocation's schedule. -/
lemma restrict_collectSchedule
    -- `u` is the outside input; projection selects the call at the original component label `k`.
    (u : Σ o, A.X o) (k : K) :
    restrict k ((List.ofFn (collectSchedule order request u)).map
      (Equiv.sigmaAssoc fun k j => (B k).X j)) = [request u k] := by
  classical
  -- Regroup each port into its component tag and local query, retaining the chosen order.
  have he : (List.ofFn (collectSchedule order request u)).map
      (Equiv.sigmaAssoc fun k j => (B k).X j) =
      (List.ofFn order).map (fun k => (⟨k, request u k⟩ : Σ k, Σ j, (B k).X j)) := by
    rw [List.map_ofFn, List.map_ofFn]
    rfl
  -- The order contains each component once, so projection selects its unique query.
  rw [he, restrict_map_of_nodup _ (List.nodup_ofFn_ofInjective order.injective)]
  exact ite_eq_left (List.mem_ofFn.mpr ⟨order.symm k, order.apply_symm_apply k⟩)

/-- Across complete invocations `us`, component `k` sees exactly `us.map (request · k)`. -/
lemma restrict_collectSchedule_flatMap
    -- `us` lists complete outside invocations; `k` selects the component history.
    (us : List (Σ o, A.X o)) (k : K) :
    restrict k ((us.flatMap (fun u => List.ofFn (collectSchedule order request u))).map
      (Equiv.sigmaAssoc fun k j => (B k).X j)) = us.map (fun u => request u k) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    rw [List.flatMap_cons, List.map_append, restrict_append, restrict_collectSchedule,
      ih, List.singleton_append, List.map_cons]

/-- Componentwise admission admits the combined schedule, including the empty family. -/
lemma collectSchedule_maps_domain
    -- `hmap` admits each component history produced by an admitted outside history `us`.
    (hmap : ∀ k us, A.domain us → (B k).domain (us.map fun u => request u k))
    (us : List (Σ o, A.X o)) (hu : A.domain us) :
    us.flatMap (fun u => List.ofFn (collectSchedule order request u)) = [] ∨
    (⨂ k, B k).domain
      (us.flatMap fun u => List.ofFn (collectSchedule order request u)) := by
  classical
  -- An empty family issues no calls; otherwise each projected history is admitted by `hmap`.
  by_cases he : us.flatMap (fun u => List.ofFn (collectSchedule order request u)) = []
  · exact Or.inl he
  · refine Or.inr ⟨he, fun k => Or.inr ?_⟩
    rw [restrict_collectSchedule_flatMap]
    exact hmap k us hu

/-- A stateless program calls every component once in `order`, then returns `answer u` of the
reply tuple. Its local history begins afresh for each outside invocation. -/
noncomputable def collectProgram :
    Program Unit A.I (⨂ k, B k).I A.X A.Y
      (⨂ k, B k).X (⨂ k, B k).Y :=
  fun _ o u => collectCalls n (collectSchedule order request ⟨o, u⟩) fun ys =>
    ((), answer ⟨o, u⟩ (Equiv.piCongrLeft (fun k => (B k).Y (request ⟨o, u⟩ k).1) order ys))

/-- Each invocation makes exactly one call per component. -/
lemma collectProgram_costs : (collectProgram order request answer).Costs (fun _ => n) := by
  intro s o u
  exact collectCalls_cost _ _ _

/-- The program returns within the schedule length `n`. -/
lemma collectProgram_bounded : (collectProgram order request answer).Bounded n := by
  intro s o u h q hc hq
  exact ((collectProgram_costs order request answer s o u h hc).1 q hq)

/-- Every call follows the chosen order, on the program's consistent exchange histories. -/
lemma collectProgram_next
    -- `s` is the trivial state, `o(u)` the outside query, and `h` its inside exchanges.
    (s : Unit) (o : A.I) (u : A.X o) (h) (q)
    -- `hc` admits the exchange prefix; `hq` identifies the next issued query `q`.
    (hc : (collectProgram order request answer).Consistent s o u h)
    (hq : collectProgram order request answer s o u h = .inr q) :
    (List.ofFn (collectSchedule order request ⟨o, u⟩))[h.length]? = some q :=
  collectCalls_next _ _ _ h q hc hq

/-- Componentwise input admission supplies the collector's domain guarantee and call bound. -/
lemma collectProgram_isDDCFrom
    -- `hmap` admits each component's complete query history for every admitted outside history.
    (hmap : ∀ k us, A.domain us → (B k).domain (us.map fun u => request u k)) :
    IsDDCFrom (⨂ k, B k).domain A.domain n
      (DDC.ofProgramOn () (collectProgram order request answer) A.domain) := by
  apply DDC.ofProgramOn_isDDCFrom_of_schedule
    (fun u => List.ofFn (collectSchedule order request u))
  · simpa only [List.length_ofFn] using collectProgram_costs order request answer
  · exact collectProgram_next order request answer
  · intro u; exact le_of_eq List.length_ofFn
  · exact (⨂ k, B k).nonempty_prefix.2
  · exact A.nonempty_prefix.2
  · exact collectSchedule_maps_domain order request hmap

/-- A completed invocation samples the independent requested-reply tuple, then applies `answer`. -/
lemma collectProgram_memorylessReplyLaw
    -- `ν k j x` is the fresh reply law of component `k`; `s`, `o`, `u` start one invocation.
    (ν : ∀ k j, (B k).X j → ProbDist ((B k).Y j)) (s : Unit) (o : A.I) (u : A.X o) :
    (collectProgram order request answer).memorylessReplyLaw
      (fun l x => ν l.1 l.2 x) s o u n [] =
      (ProbDist.map (answer ⟨o, u⟩)
        (ProbDist.piDep fun k => ν k (request ⟨o, u⟩ k).1 (request ⟨o, u⟩ k).2)).1 := by
  -- The call body gives the product tuple in its actual invocation order.
  rw [Program.memorylessReplyLaw_collectCalls
    (fun l x => ν l.1 l.2 x) s o u n
    (collectSchedule order request ⟨o, u⟩)
    (fun ys => ((), answer ⟨o, u⟩
      (Equiv.piCongrLeft (fun k => (B k).Y (request ⟨o, u⟩ k).1) order ys))) []
    (fun _ => rfl)]
  -- Transport that tuple explicitly back to the original component index `K`.
  change fTransform (answer ⟨o, u⟩ ∘ Equiv.piCongrLeft _ order)
    (piDep fun i => (ν (order i) (request ⟨o, u⟩ (order i)).1
      (request ⟨o, u⟩ (order i)).2).1) = _
  rw [← fTransform_fTransform, fTransform_piDep_piCongrLeft order
    (fun k => (ν k (request ⟨o, u⟩ k).1 (request ⟨o, u⟩ k).2).1)]
  rfl

namespace TypedConverter

/-- Call each component of `⨂ k, B k` once, in `order`, then return `answer u` of the replies.
The converter has no retained state, its outside domain is `A.domain`, and each invocation makes
exactly `n` inside calls: one selected query to each component. -/
noncomputable def collect
    -- `hmap` admits component `k`'s query history for every admitted outside history `us`.
    (hmap : ∀ k us, A.domain us → (B k).domain (us.map fun u => request u k)) :
    TypedConverter A (⨂ k, B k) :=
  ofDDC (DDC.ofProgramOn () (collectProgram order request answer) A.domain)
    (collectProgram_isDDCFrom order request answer hmap)

variable [DecidableEq K]

/-- Fresh component replies give the independent tuple law, followed by `answer`.
The equality is cumulative behavior on `A.domain`, so it covers repeated invocations. -/
theorem collect_smul_parallelAll_ofMemoryless
    -- `hmap` admits all component histories; `ν k j x` is the fresh law at query `j(x)` of `B k`.
    (hmap : ∀ k us, A.domain us → (B k).domain (us.map fun u => request u k))
    (ν : ∀ k j, (B k).X j → ProbDist ((B k).Y j)) :
    collect order request answer hmap • (∥ k, TypedSystem.ofMemoryless (B k) (ν k)) =
      TypedSystem.ofMemoryless A (fun o u => ProbDist.map (answer ⟨o, u⟩)
        (ProbDist.piDep fun k => ν k (request ⟨o, u⟩ k).1 (request ⟨o, u⟩ k).2)) := by
  classical
  -- Parallel closure exposes fresh port laws; the invocation law computes their tuple product.
  rw [TypedSystem.parallelAll_ofMemoryless]
  -- The attachment law lifts this state-independent invocation law to all cumulative histories.
  exact Subtype.ext (PDCBehavior.attach_ofDDC_ofProgramOn_memoryless
    (⨂ k, B k).nonempty_prefix A.nonempty_prefix ()
    (collectProgram order request answer) (collectProgram_bounded order request answer)
    (collectProgram_isDDCFrom order request answer hmap)
    (collectProgram_memorylessReplyLaw order request answer ν) rfl
    (TypedSystem.ofMemoryless (⨂ k, B k) (fun l x => ν l.1 l.2 x)).2)

/-- Functional components return the tuple of their selected outputs, combined by `answer`. -/
lemma collect_smul_parallelAll_ofFunction
    -- `hmap` admits component histories; `f k j x` is component `k`'s fixed reply at `j(x)`.
    (hmap : ∀ k us, A.domain us → (B k).domain (us.map fun u => request u k))
    (f : ∀ k j, (B k).X j → (B k).Y j) :
    collect order request answer hmap • (∥ k, TypedSystem.ofFunction (f k)) =
      TypedSystem.ofFunction (fun o u => answer ⟨o, u⟩
        (fun k => f k (request ⟨o, u⟩ k).1 (request ⟨o, u⟩ k).2)) := by
  -- `ofFunction` is definitionally `ofMemoryless` with the existing normalized point laws.
  change collect order request answer hmap •
      (∥ k, TypedSystem.ofMemoryless (B k) (fun j x => ProbDist.single (f k j x))) =
    TypedSystem.ofMemoryless A (fun o u => ProbDist.single
      (answer ⟨o, u⟩ (fun k => f k (request ⟨o, u⟩ k).1 (request ⟨o, u⟩ k).2)))
  rw [collect_smul_parallelAll_ofMemoryless]
  congr 1
  funext o u
  -- Independent point laws form the point law on the tuple of their fixed outputs.
  apply Subtype.ext
  change fTransform _ (piDep fun k => Finsupp.single _ 1) = Finsupp.single _ 1
  rw [piDep_single, fTransform_single]

/-- Collecting independent fresh sources yields the fresh source of their dependent tuple law.
Each outside trigger draws once from every component; successive triggers use fresh draws. -/
lemma collect_smul_parallelAll_source
    -- `Z k` carries component `k`'s replies.
    -- `q` bounds both outside tuple requests and each component source's triggers.
    {Z : K → Type} [∀ k, Fintype (Z k)] (q : ℕ)
    -- `μ k` is sampled independently by source `k` at each trigger.
    (μ : ∀ k, ProbDist (Z k)) :
    collect (A := Interface.source (∀ k, Z k) q)
      (B := fun k => Interface.source (Z k) q) order
      (fun _ _ => ⟨(), ()⟩) (fun _ ys => ys)
      (fun _ _ hu => Interface.queryBudget_domain_map _ le_rfl hu) •
      (∥ k, TypedSystem.source (μ k) q) =
      TypedSystem.source (ProbDist.piDep μ) q := by
  -- Each source has its fresh law at the sole port; collection takes their independent product.
  simp_rw [TypedSystem.source_eq_ofMemoryless]
  rw [collect_smul_parallelAll_ofMemoryless]
  congr 1
  funext o u
  exact Subtype.ext (fTransform_id _)

end TypedConverter

end SystemAlgebra
