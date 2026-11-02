module

public import Commons.Definitions.CollisionGame

/-!
# Hidden-monitor clients

An arbitrary converter sees the same automaton after its hidden condition is forgotten.
The URF client rewrites to the ideal object. The symbolic two-query test distinguishes
repeated inputs from distinct inputs with equal replies, independently of the query budget.
-/

@[expose] public section

namespace MonotoneMonitorTests

open Commons SystemAlgebra Probability Probability.Distribution
open scoped SystemAlgebra

/-- A caller with a domain-preserving converter can use the visible-system law directly. -/
lemma monitored_automaton_visible
    -- `A` is the monitored interface, `B` the caller's interface, and `S` the retained state.
    {A B : Interface} {S : Type} (α : TypedConverter B A)
    -- `step` and `initial` specify the visible automaton; `bad s` is its hidden condition.
    (step : S → (i : A.I) → A.X i → S × A.Y i)
    (initial : ProbDist S) (bad : S → MC (Σ i, A.X i)) :
    α • (TypedGame.ofAutomaton A step initial bad).visible =
      α • TypedSystem.ofAutomaton A step initial := by
  rw [TypedGame.visible_ofAutomaton]

/-- The URF instance fits the same client without inspecting its sampled functions. -/
lemma monitored_urf_visible {A B : Interface} [∀ i, Nonempty (A.Y i)]
    -- `α` is an arbitrary adaptive converter with its domain guarantee.
    (α : TypedConverter B A) :
    α • (URF.collisionGame A).visible = α • URF A := by
  rw [URF.collisionGame_visible]

/-- On two queries, the hidden predicate tests distinct inputs with equal replies. -/
lemma collision_pair_iff
    -- `X`, `Y` carry inputs and replies; `q` is the selected evaluation budget.
    {X Y : Type} [Fintype X] [Fintype Y] (q : ℕ)
    -- `f` is the retained function; `x`, `x'` are the two tested inputs.
    (f : X → Y) (x x' : X) :
    URF.Collision (Evaluation X Y q) (fun _ => f)
        [⟨.eval, x⟩, ⟨.eval, x'⟩] ↔ x ≠ x' ∧ f x = f x' := by
  constructor
  · rintro ⟨i, a, b, ha, hb, hne, he⟩
    cases i
    simp only [List.mem_cons, List.not_mem_nil, or_false, Sigma.mk.inj_iff, true_and,
      heq_eq_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hne rfl).elim
    · exact ⟨hne, he⟩
    · exact ⟨Ne.symm hne, he.symm⟩
    · exact (hne rfl).elim
  · rintro ⟨hne, he⟩
    exact ⟨.eval, x, x', List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      hne, he⟩

/-- Two queries at different ports cannot collide, regardless of their replies. -/
lemma collision_cross_port
    -- `A` supplies the alphabets; `i`, `j` are distinct queried ports.
    {A : Interface} (i j : A.I) (different : i ≠ j)
    -- `f` is retained; `x`, `y` are the inputs at those ports.
    (f : ∀ k, A.X k → A.Y k) (x : A.X i) (y : A.X j) :
    ¬ URF.Collision A f [⟨i, x⟩, ⟨j, y⟩] := by
  rintro ⟨k, a, b, ha, hb, hne, _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hne (eq_of_heq (Sigma.mk.inj_iff.mp (ha.trans hb.symm)).2)
  · exact different ((congrArg Sigma.fst ha).symm.trans (congrArg Sigma.fst hb))
  · exact different ((congrArg Sigma.fst hb).symm.trans (congrArg Sigma.fst ha))
  · exact hne (eq_of_heq (Sigma.mk.inj_iff.mp (ha.trans hb.symm)).2)

/-- The actual URF game keeps its bit unset after one query to each of two distinct ports. -/
lemma collisionGame_cross_port_unset
    -- `A` fixes the domain; `i`, `j` are different ports with inhabited reply types.
    {A : Interface} [∀ i, Nonempty (A.Y i)] (i j : A.I) (different : i ≠ j)
    (x : A.X i) (y : A.X j) (admitted : A.domain [⟨i, x⟩, ⟨j, y⟩]) :
    (URF.collisionGame A).1.1.unsetProbability [⟨i, x⟩, ⟨j, y⟩] = 1 := by
  rw [URF.collisionGame_unsetProbability A admitted,
    mass_eq_zero_of_forall_not _ (fun f => collision_cross_port i j different f x y), sub_zero]

open Classical in
/-- The monitor's actual hidden-event probability at a fixed retained function has the same
pair test, including probability zero on repeats. -/
lemma fixed_function_badProbability
    -- `X`, `Y` are the alphabets; `f` is retained, and `x`, `x'` are the two tested inputs.
    {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y) (x x' : X) :
    PDG.badProbability
        (PDG.ofAutomaton (Evaluation X Y 2) (fun (g : X → Y) _ a => (g, g a))
          (ProbDist.single f)
          (fun g => ⟨URF.Collision (Evaluation X Y 2) (fun _ => g),
            fun _ _ hp => URF.Collision.mono _ hp.subset⟩)).1
        [⟨.eval, x⟩, ⟨.eval, x'⟩] = if x ≠ x' ∧ f x = f x' then 1 else 0 := by
  rw [PDG.ofAutomaton_badProbability, ProbDist.single, mass_single]
  change (if URF.Collision (Evaluation X Y 2) (fun _ => f)
    [⟨.eval, x⟩, ⟨.eval, x'⟩] then (1 : ℝ) else 0) = _
  rw [collision_pair_iff]
  split_ifs <;> rfl

/-- Repeating one input does not win, even though its two replies agree. -/
example {X Y : Type} [Fintype X] [Fintype Y] (q : ℕ) (f : X → Y) (x : X) :
    ¬ URF.Collision (Evaluation X Y q) (fun _ => f) [⟨.eval, x⟩, ⟨.eval, x⟩] := by
  rw [collision_pair_iff]
  exact fun h => h.1 rfl

/-- Equal replies at distinct tested inputs trigger the event and every extension. -/
example {X Y : Type} [Fintype X] [Fintype Y] (q : ℕ) (f : X → Y) (x x' : X)
    (different : x ≠ x') (sameReply : f x = f x')
    (later : List (Σ i, (Evaluation X Y q).X i)) :
    URF.Collision (Evaluation X Y q) (fun _ => f) ([⟨.eval, x⟩, ⟨.eval, x'⟩] ++ later) :=
  URF.Collision.mono _ (List.prefix_append _ _).subset
    ((collision_pair_iff q f x x').mpr ⟨different, sameReply⟩)

#print axioms monitored_automaton_visible
#print axioms monitored_urf_visible
#print axioms collision_pair_iff
#print axioms fixed_function_badProbability
#print axioms collisionGame_cross_port_unset

end MonotoneMonitorTests
