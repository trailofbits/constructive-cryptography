module

public import Commons.Definitions.RandomFunction
public import Probability.List
public import RandomSystems.Typed.KeyedAutomaton

/-!
# Lazy and retained random functions

`completionLaw_update_eq` identifies recording a fresh reply with pinning one coordinate.
`tableLaw_simulates` then applies the joint pinned-product law: completing before answering
has the same law as answering and completing the resulting records.

`lazy_eq` lifts this local equality to all admitted histories by kernel simulation. The
retained-key and product-uncurrying laws identify the result with `randomFunction A μ`.
Repeated inputs reuse one draw; coordinate laws may depend on both the port and the input.
-/

@[expose] public section

namespace Commons.randomFunction

open SystemAlgebra Probability Probability.Distribution

-- `A` fixes the ports and domain; `μ i x` is the normalized law of entry `i(x)`.
variable (A : Interface) (μ : ∀ i, A.X i → ProbDist (A.Y i))

open Classical in
/-- Recording a fresh reply pins exactly its coordinate in the independent completion. -/
lemma completionLaw_update_eq
    -- `table` stores earlier replies; `miss` says that input `i(x)` is not yet recorded.
    (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i) (y : A.Y i)
    (miss : (table i).lookup x = none) :
    (completionLaw A μ (Function.update table i (table i ++ [(x, y)]))).1 =
      pinnedProduct (fun q : Σ j, A.X j => (μ q.1 q.2).1)
        (Function.update (fun q : Σ j, A.X j => (table q.1).lookup q.2) ⟨i, x⟩ (some y)) := by
  rw [completionLaw, ProbDist.pinnedProduct_val]
  apply congrArg (pinnedProduct (fun q : Σ j, A.X j => (μ q.1 q.2).1))
  funext ⟨j, z⟩
  by_cases samePort : j = i
  · subst j
    rw [Function.update_self, List.lookup_append_singleton_of_none _ x y miss z]
    by_cases sameInput : z = x
    · subst z
      simp only [ite_true, Function.update_self]
    · have different : (⟨i, z⟩ : Σ j, A.X j) ≠ ⟨i, x⟩ := by
        intro equal
        exact sameInput (eq_of_heq (Sigma.mk.inj_iff.mp equal).2)
      rw [ite_eq_right sameInput, Function.update_of_ne different]
  · have different : (⟨j, z⟩ : Σ j, A.X j) ≠ ⟨i, x⟩ :=
      fun equal => samePort (congrArg Sigma.fst equal)
    simp only [Function.update_of_ne samePort, Function.update_of_ne different]

open Classical in
/-- Completing the table commutes with answering a query, retaining the same tagged reply. -/
lemma tableLaw_simulates
    -- `table` is the lazy state; `query` chooses one port and one input at that port.
    (table : ∀ i, List (A.X i × A.Y i)) (query : Σ i, A.X i) :
    ProbStep.SimulatesAt (tableLaw A μ)
      (fun f i x => (ProbDist.single (f ⟨i, x⟩)).map (fun y => (f, y)))
      (completionLaw A μ) table query := by
  obtain ⟨i, x⟩ := query
  simp only [ProbStep.SimulatesAt, ProbStep.outcome, ProbDist.map_val, ProbDist.single,
    fTransform_single]
  rw [bindK_single_comp]
  cases lookup : (table i).lookup x with
  | none =>
    -- A miss exposes one product coordinate and records precisely that value.
    simp only [tableLaw, ProbStep.recordReplies, replyLaw, lookup, Option.elim_none,
      Option.isNone_none, ite_true, ProbDist.map_val, fTransform_fTransform,
      Function.comp_def, bindK_fTransform, ProbStep.tagged]
    have joint := fTransform_pinnedProduct_apply
      (fun q : Σ j, A.X j => (μ q.1 q.2).1)
      (fun q : Σ j, A.X j => (table q.1).lookup q.2) ⟨i, x⟩
    have tagged := congrArg (fTransform
      (fun p : (∀ q : Σ j, A.X j, A.Y q.1) × A.Y i =>
        (p.1, (⟨i, p.2⟩ : Σ j, A.Y j)))) joint
    simp only [fTransform_fTransform, fTransform_bindK, Function.comp_def,
      lookup, Option.elim_none] at tagged
    calc
      _ = bindK (μ i x).1 (fun y => fTransform (fun f => (f, (⟨i, y⟩ : Σ j, A.Y j)))
          (pinnedProduct (fun q : Σ j, A.X j => (μ q.1 q.2).1)
            (Function.update (fun q : Σ j, A.X j => (table q.1).lookup q.2)
              ⟨i, x⟩ (some y)))) := by
        simpa only [completionLaw, ProbDist.pinnedProduct_val] using tagged
      _ = _ := by
        apply bindK_congr
        intro y _
        rw [completionLaw_update_eq A μ table i x y lookup]
  | some y =>
    -- A hit leaves the records fixed, and every supported completion already returns `y`.
    simp only [tableLaw, ProbStep.recordReplies, replyLaw, lookup, Option.elim_some,
      Option.isNone_some, ProbDist.map_val, ProbDist.single, fTransform_single,
      bindK_single, one_smul, ProbStep.tagged]
    apply fTransform_congr_support
    intro f supported
    have pin := pinnedProduct_apply_eq_of_pin
      (fun q : Σ j, A.X j => (μ q.1 q.2).1) _ ⟨i, x⟩ y lookup
      (by simpa only [completionLaw, ProbDist.pinnedProduct_val] using supported)
    rw [pin]

open Classical in
/-- Lazy sampling equals one retained independent table on the entire declared domain. -/
theorem lazy_eq : lazy A μ = randomFunction A μ := by
  let table : ProbDist (∀ q : Σ i, A.X i, A.Y q.1) :=
    ProbDist.piDep fun q => μ q.1 q.2
  -- Completing empty records gives the independent coordinate law.
  have initial : (ProbDist.single (fun _ => [])).bind (completionLaw A μ) = table := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.single, bindK_single, one_smul,
      completionLaw, ProbDist.pinnedProduct_val, List.lookup_nil, pinnedProduct_none,
      table, ProbDist.piDep_val]
  have simulation := TypedSystem.ofProbAutomaton_eq_of_simulation (A := A) (tableLaw A μ)
    (fun f i x => (ProbDist.single (f ⟨i, x⟩)).map (fun y => (f, y))) (completionLaw A μ)
    (fun _ _ => True) (by intros; trivial) (by intros; apply tableLaw_simulates)
    (ProbDist.single (fun _ => [])) (by intros; trivial)
  rw [initial] at simulation
  -- The completed function is retained; only its representation changes from flat to nested.
  calc
    lazy A μ = _ := simulation
    _ = TypedSystem.keyed table (fun f i x => ProbDist.single (f ⟨i, x⟩)) :=
      TypedSystem.ofProbAutomaton_eq_keyed table _
    _ = TypedSystem.sample table.1
        (fun f => TypedSystem.ofFunction (fun i x => f ⟨i, x⟩)) :=
      TypedSystem.keyed_single table _
    _ = randomFunction A μ := by
      have transport := TypedSystem.sample_fTransform
        (Equiv.piCurry (fun i (_ : A.X i) => A.Y i)).symm
        (ProbDist.piDep (fun i => ProbDist.piDep (μ i))).1
        (fun f => TypedSystem.ofFunction (A := A) (fun i x => f ⟨i, x⟩))
      have law := congrArg
        (fun P : ProbDist (∀ q : Σ i, A.X i, A.Y q.1) =>
          TypedSystem.sample P.1 (fun f => TypedSystem.ofFunction (A := A) (fun i x => f ⟨i, x⟩)))
        (ProbDist.map_piDep_uncurry μ)
      exact law.symm.trans transport

end Commons.randomFunction
