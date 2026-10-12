import RandomSystems.Game.DiscreteMBO
import RandomSystems.PDS.Function

/-!
# Sampled-function games

A sampled function with a hidden monotone condition is a probabilistic discrete game on a domain
of input histories; its visible systems are the sampled function. The game it presents is
conditionally equivalent to an ideal sampled function once, on every fixed query sequence, the
answers jointly with the unset condition factor through the ideal answers.

## Main definitions

* `PDG.ofFunction`: a sampled function with a hidden condition
* `PDG.ofSingleFunction`: the same at a single label

## Main results

* `PDG.ofFunction_underlying`: the visible systems are the sampled function
* `PDG.ofFunction_badProbability`: the condition holds with the probability of the sampled
  conditions
* `PDG.ofFunction_conditionallyEquivalent`: conditional equivalence from the fixed-query
  factorization
-/

namespace SystemAlgebra.PDG

open Probability

section Presentation

variable {K X Y : Type} [Fintype X] [Fintype Y] (D : List X → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p) (bound : ℕ)
    (hb : ∀ h, D h → h.length ≤ bound)

/-- Sample a function and its monotone condition once for the whole interaction. -/
noncomputable def ofFunction (P : Distribution K) (f : K → X → Y) (bad : K → MC X) :
    PDG X Y (Domain.ofInputs D bound hb) :=
  -- Push `P` forward: the sample k gives the deterministic discrete game whose DDS evaluates
  -- `f k` on the input domain `D` and whose hidden condition is `bad k`. That DDS answers
  -- exactly the histories in `D`, so it has the domain.
  Distribution.fTransform (fun k => ⟨(DDS.ofFunction D hD (f k), bad k),
    HasDomain.ofInputs (DDS.ofFunction_dom D hD (f k))⟩) P

theorem ofFunction_isProbDist {P : Distribution K} (hP : P.isProbDist)
    (f : K → X → Y) (bad : K → MC X) :
    (ofFunction D hD bound hb P f bad).isProbDist := Distribution.fTransform_isProbDist _ hP

/-- The visible systems are the sampled function. -/
theorem ofFunction_underlying (P : Distribution K) (f : K → X → Y) (bad : K → MC X) :
    (ofFunction D hD bound hb P f bad).underlying = PDS.ofFunction D hD bound hb f P := by
  -- Both sides push `P` forward; compose k ↦ game ↦ its DDS into one map.
  rw [underlying, ofFunction, Distribution.fTransform_comp]
  -- The composite map is the map of `PDS.ofFunction`: k ↦ the evaluator of `f k`.
  rfl

theorem ofFunction_badProbability (P : Distribution K) (f : K → X → Y)
    (bad : K → MC X) (xs : List X) :
    (ofFunction D hD bound hb P f bad).badProbability xs = P.mass (fun k => (bad k).1 xs) := by
  -- The mass of an event under a push-forward of `P` is the `P`-mass of its preimage.
  rw [badProbability, ofFunction, Distribution.mass_fTransform]

end Presentation

variable {K I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (D : List (Σ i, X i) → Prop) (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (bound : ℕ) (hb : ∀ h, D h → h.length ≤ bound)

/-- **A sampled-function game is conditionally equivalent to the ideal sampled function** once,
on every fixed query sequence, the answers jointly with the unset condition factor through the
ideal answers. Repeated queries are handled by function consistency, without choosing new
replies or assuming the queries are distinct. -/
theorem ofFunction_conditionallyEquivalent
    (P : Distribution K) (f : K → (Σ i, X i) → Σ i, Y i) (bad : K → MC (Σ i, X i))
    {hG : (ofFunction D hD bound hb P f bad).isProbDist}
    (Q : Distribution ((Σ i, X i) → Σ i, Y i)) (hQ : Q.isProbDist)
    (factor : ∀ xs (answers : (Σ i, X i) → Σ i, Y i),
      P.mass (fun k => (∀ x ∈ xs, f k x = answers x) ∧ ¬ (bad k).1 xs) =
        (1 - P.mass (fun k => (bad k).1 xs)) *
          Q.mass (fun g => ∀ x ∈ xs, g x = answers x)) :
    ((ofFunction D hD bound hb P f bad).behavior hG).ConditionallyEquivalent
      (PDS.behavior (PDS.ofFunction D hD bound hb id Q)
        (Distribution.fTransform_isProbDist _ hQ)) := by
  -- By `conditionallyEquivalent_behavior` it suffices to show, for each transcript h with
  -- queries xs = x₁ … xₙ and replies y₁ … yₙ:
  --
  --   Pr_P[f k replies h ∧ ¬ bad k (xs)] = (1 - Pr_P[bad k (xs)]) · Pr_Q[g replies h].
  refine conditionallyEquivalent_behavior hG hD fun h => ?_
  -- Write the left side and the bad probability as masses over the samples k ∼ P.
  rw [ofFunction_badProbability, goodProbability, ofFunction, Distribution.mass_fTransform]
  -- The ideal side is the probability of h under the PDS of the ideal function,
  change _ = (1 - _) * behaviorMass _ _ _
  -- i.e. a mass over the samples g ∼ Q.
  rw [behaviorMass, PDS.ofFunction, Distribution.mass_fTransform]
  -- A fixed function replies h iff xs is admitted (or empty) and each reply is its value at
  -- the query: yᵢ = f(xᵢ) (`replies_ofFunction_iff`).
  simp only [DDS.replies_ofFunction_iff, id_eq]
  -- Case on whether xs is admitted (or empty).
  by_cases admitted : h.map Prod.fst = [] ∨ D (h.map Prod.fst)
  -- Admitted: drop the admission conjunct on both sides.
  · simp only [admitted, true_and]
    -- Case on whether the replies of h are the values of some function at the queries.
    by_cases consistent :
        ∃ answers : (Σ i, X i) → Σ i, Y i, h.map Prod.snd = (h.map Prod.fst).map answers
    -- Consistent with `answers`: a function reproduces the replies iff it agrees with
    -- `answers` on every query of xs, and the claim is `factor` at xs and `answers`.
    · obtain ⟨answers, he⟩ := consistent
      rw [he]
      simpa only [List.map_eq_map_iff, eq_comm] using factor (h.map Prod.fst) answers
    -- Inconsistent (for instance a repeated query with two different replies): no function
    -- reproduces the replies, so both masses are 0.
    · have impossible (g : (Σ i, X i) → Σ i, Y i) : h.map Prod.snd ≠ (h.map Prod.fst).map g :=
        fun he => consistent ⟨g, he⟩
      rw [Distribution.mass_eq_zero_of_forall_not P (fun k hk => impossible (f k) hk.1),
        Distribution.mass_eq_zero_of_forall_not Q impossible, mul_zero]
  -- Not admitted: no evaluator replies h, so both masses are 0.
  · simp only [admitted, false_and]
    rw [Distribution.mass_eq_zero_of_forall_not P (fun _ h => h),
      Distribution.mass_eq_zero_of_forall_not Q (fun _ h => h), mul_zero]

end SystemAlgebra.PDG

namespace SystemAlgebra

open Probability

/-- At a single interface, a reply equality is just equality of its values. -/
theorem single_interface_answers_iff {I X Y : Type} [Unique I]
    (xs : List (Σ _ : I, X)) (answers : (Σ _ : I, X) → Σ _ : I, Y) (f : X → Y) :
    (∀ x ∈ xs, (⟨x.1, f x.2⟩ : Σ _ : I, Y) = answers x) ↔
      ∀ x ∈ xs.map Sigma.snd, f x = (answers ⟨default, x⟩).2 := by
  constructor
  -- (→) A query value x comes from a query ⟨i, x⟩ of xs; its label i is the only label, and
  -- the value equation is the second component of the reply equation at ⟨i, x⟩.
  · intro h x hx
    obtain ⟨⟨i, x⟩, hi, rfl⟩ := List.mem_map.mp hx
    simpa only [show i = default from Subsingleton.elim _ _] using
      congrArg Sigma.snd (h ⟨i, x⟩ hi)
  -- (←) For a query ⟨i, x⟩ of xs, the value equation holds at x.
  · intro h ⟨i, x⟩ hx
    have he := h x (List.mem_map.mpr ⟨⟨i, x⟩, hx, rfl⟩)
    -- The label i is the only label (`Unique I`): the two replies have the same label, and
    -- their values are equal by the value equation.
    have labels : i = default := Subsingleton.elim _ _
    cases labels
    apply Sigma.ext (Subsingleton.elim _ _)
    exact heq_of_eq he

namespace PDG

/-- A sampled function at the single exposed interface, with a hidden condition
on its ordinary input histories. -/
noncomputable def ofSingleFunction {I K X Y : Type} [Unique I] [Fintype X] [Fintype Y]
    (D : List (Σ _ : I, X) → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p) (bound : ℕ)
    (hb : ∀ h, D h → h.length ≤ bound)
    (P : Distribution K) (f : K → X → Y) (bad : K → MC X) :
    PDG (Σ _ : I, X) (Σ _ : I, Y) (Domain.ofInputs D bound hb) :=
  -- Each reply keeps the label of its query; the hidden condition reads `bad k` on the query
  -- values with the labels dropped, and stays monotone since dropping labels keeps
  -- prefixes.
  ofFunction D hD bound hb P (fun k x => ⟨x.1, f k x.2⟩)
    (fun k => ⟨fun xs => (bad k).1 (xs.map Sigma.snd),
      fun {_ _} hp => (bad k).2 (hp.map Sigma.snd)⟩)

end PDG
end SystemAlgebra
