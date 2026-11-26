module

public import RandomSystems.Cumulative.ObservationKernel

/-!
# Adaptive observation kernels

The first reply is a fair bit; later replies echo their query. After the first query, the
domain admits only `true`, for at most three rounds. The observer's next query depends on
its replies. Stopping and impossible histories both retain their current transcript.
-/

@[expose] public section

noncomputable section

namespace Tests.ObservationKernel

open SystemAlgebra Probability Probability.Distribution

/-- At most three queries; every query after the first must be `true`. -/
def queries : Domain Bool Bool where
  admits h x := h.length < 3 ∧ (h ≠ [] → x = true)
  bound := 3
  length_lt _ _ admitted := admitted.1

/-- Initially sample a fair bit; subsequently reply with the query itself. -/
def resource : RandomSystem Bool Bool queries :=
  RandomSystem.ofConditional (fun h x _ => if h = [] then 𝒰[Bool] else ProbDist.single x)

/-- Ask `false` first, continue with `true` after a true first reply, and stop after true again.
An impossible false second reply would trigger one further true query. -/
def observer : List Bool →. Bool
  | [] => Part.some false
  | [true] => Part.some true
  | [_, false] => Part.some true
  | _ => Part.none

/-- Every query selected by the observer is admitted by the input-dependent domain. -/
lemma compatible : resource.Compatible observer := by
  intro h x _ _ selected
  change h.length < 3 ∧ (h ≠ [] → x = true)
  rcases h with _ | ⟨⟨a, b⟩, h⟩
  · exact ⟨by norm_num, fun impossible => (impossible rfl).elim⟩
  rcases h with _ | ⟨⟨a', b'⟩, h⟩
  · cases b <;> simp only [List.map_cons, List.map_nil, observer, Part.mem_some_iff,
      Part.notMem_none] at selected
    exact ⟨by simp only [List.length_cons, List.length_nil]; norm_num, fun _ => selected⟩
  rcases h with _ | ⟨z, h⟩
  · cases b' <;> simp only [List.map_cons, List.map_nil, observer, Part.mem_some_iff,
      Part.notMem_none] at selected
    exact ⟨by simp only [List.length_cons, List.length_nil]; norm_num, fun _ => selected⟩
  · simp only [List.map_cons, observer, Part.notMem_none] at selected

/-- The first false reply stops the observer, so later horizons keep that history. -/
example : resource.observationKernel observer [(false, false)] =
    ProbDist.single [(false, false)] :=
  resource.observationKernel_eq_single_of_stopped observer _ (by
    intro impossible
    exact impossible)

/-- Either first reply has mass one half. -/
lemma first_mass (b : Bool) : resource [(false, b)] = 1 / 2 := by
  change RandomSystem.ofConditional _ ([] ++ [(false, b)]) = _
  rw [RandomSystem.ofConditional_snoc]
  norm_num [queries, RandomSystem.mass_nil, ProbDist.uniform, uniform_apply]

/-- After a true first reply, the next true query receives the deterministic reply true. -/
example : resource.observationKernel observer [(false, true)] =
    ProbDist.single [(false, true), (true, true)] := by
  have defined : (resource.conditional [(false, true)] true).Dom := by
    refine ⟨?_, ?_⟩
    · exact ⟨by norm_num, fun _ => rfl⟩
    · rw [first_mass]; norm_num
  have reply : (resource.conditional [(false, true)] true).get defined =
      ProbDist.single true := by
    apply Subtype.ext
    ext b
    rw [RandomSystem.conditional_apply, first_mass]
    change RandomSystem.ofConditional _ ([(false, true)] ++ [(true, b)]) / _ = _
    rw [RandomSystem.ofConditional_snoc]
    norm_num [queries, ProbDist.single, Finsupp.single_apply]
    change (if b = true then resource [(false, true)] else 0) / (1 / 2) =
      if b = true then 1 else 0
    rw [first_mass]
    split_ifs <;> norm_num
  rw [resource.observationKernel_eq_map observer _ (Part.mem_some _) defined, reply]
  apply Subtype.ext
  exact fTransform_single _ _ _

/-- A false second reply is impossible; the conditional kernel retains that off-support history. -/
example : resource.observationKernel observer [(false, true), (true, false)] =
    ProbDist.single [(false, true), (true, false)] := by
  apply resource.observationKernel_eq_single_of_undefined _ _ (Part.mem_some _)
  intro defined
  have zero : resource [(false, true), (true, false)] = 0 := by
    change RandomSystem.ofConditional _ ([(false, true)] ++ [(true, false)]) = _
    rw [RandomSystem.ofConditional_snoc]
    norm_num [queries, ProbDist.single, Finsupp.single_apply]
  exact defined.2 zero

/-- A fourth query is inadmissible, even when an observer requests it. -/
example : resource.observationKernel (fun _ => Part.some true)
    [(false, true), (true, true), (true, true)] =
      ProbDist.single [(false, true), (true, true), (true, true)] := by
  apply resource.observationKernel_eq_single_of_undefined _ _ (Part.mem_some _)
  intro defined
  exact (Nat.lt_irrefl 3) defined.1.1

/-- Adaptive observation obeys the same kernel evolution at every horizon. -/
example (n : ℕ) : resource.sLaw observer (n + 1) =
    bindK (resource.sLaw observer n) (fun h => (resource.observationKernel observer h).1) :=
  resource.sLaw_succ_eq_bindK observer compatible n

#print axioms RandomSystem.observationKernel
#print axioms RandomSystem.smul_conditional_eq_extensionLaw
#print axioms RandomSystem.sLaw_succ_eq_bindK
#print axioms RandomSystem.conditional_mass

end Tests.ObservationKernel
