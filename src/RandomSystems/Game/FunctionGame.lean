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

open Classical Probability

section Presentation

variable {K X Y : Type} [Fintype X] [Fintype Y] (D : List X → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p) (bound : ℕ)
    (hb : ∀ h, D h → h.length ≤ bound)

/-- Sample a function and its monotone condition once for the whole interaction. -/
noncomputable def ofFunction (P : Distribution K) (f : K → X → Y) (bad : K → MC X) :
    PDG X Y (Domain.ofInputs D bound hb) :=
  Distribution.fTransform (fun k => ⟨(DDS.ofFunction D hD (f k), bad k),
    HasDomain.ofInputs (DDS.ofFunction_dom D hD (f k))⟩) P

theorem ofFunction_isProbDist {P : Distribution K} (hP : P.isProbDist)
    (f : K → X → Y) (bad : K → MC X) :
    (ofFunction D hD bound hb P f bad).isProbDist := Distribution.fTransform_isProbDist _ hP

/-- The visible systems are the sampled function. -/
theorem ofFunction_underlying (P : Distribution K) (f : K → X → Y) (bad : K → MC X) :
    (ofFunction D hD bound hb P f bad).underlying = PDS.ofFunction D hD bound hb f P := by
  rw [underlying, ofFunction, Distribution.fTransform_comp]
  rfl

theorem ofFunction_badProbability (P : Distribution K) (f : K → X → Y)
    (bad : K → MC X) (xs : List X) :
    (ofFunction D hD bound hb P f bad).badProbability xs = P.mass (fun k => (bad k).1 xs) := by
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
  refine conditionallyEquivalent_behavior hG hD fun h => ?_
  rw [ofFunction_badProbability, goodProbability, ofFunction, Distribution.mass_fTransform]
  change _ = (1 - _) * behaviorMass _ _ _
  rw [behaviorMass, PDS.ofFunction, Distribution.mass_fTransform]
  simp only [DDS.replies_ofFunction_iff, id_eq]
  by_cases admitted : h.map Prod.fst = [] ∨ D (h.map Prod.fst)
  · simp only [admitted, true_and]
    by_cases consistent :
        ∃ answers : (Σ i, X i) → Σ i, Y i, h.map Prod.snd = (h.map Prod.fst).map answers
    · obtain ⟨answers, he⟩ := consistent
      rw [he]
      simpa only [List.map_eq_map_iff, eq_comm] using factor (h.map Prod.fst) answers
    · have impossible (g : (Σ i, X i) → Σ i, Y i) : h.map Prod.snd ≠ (h.map Prod.fst).map g :=
        fun he => consistent ⟨g, he⟩
      rw [Distribution.mass_eq_zero_of_forall_not P (fun k hk => impossible (f k) hk.1),
        Distribution.mass_eq_zero_of_forall_not Q impossible, mul_zero]
  · simp only [admitted, false_and]
    rw [Distribution.mass_eq_zero_of_forall_not P (fun _ h => h),
      Distribution.mass_eq_zero_of_forall_not Q (fun _ h => h), mul_zero]

end SystemAlgebra.PDG

namespace SystemAlgebra

open Classical Probability

/-- At a single interface, a reply equality is just equality of its values. -/
theorem single_interface_answers_iff {I X Y : Type} [Unique I]
    (xs : List (Σ _ : I, X)) (answers : (Σ _ : I, X) → Σ _ : I, Y) (f : X → Y) :
    (∀ x ∈ xs, (⟨x.1, f x.2⟩ : Σ _ : I, Y) = answers x) ↔
      ∀ x ∈ xs.map Sigma.snd, f x = (answers ⟨default, x⟩).2 := by
  constructor
  · intro h x hx
    obtain ⟨⟨i, x⟩, hi, rfl⟩ := List.mem_map.mp hx
    simpa only [show i = default from Subsingleton.elim _ _] using
      congrArg Sigma.snd (h ⟨i, x⟩ hi)
  · intro h ⟨i, x⟩ hx
    have he := h x (List.mem_map.mpr ⟨⟨i, x⟩, hx, rfl⟩)
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
  ofFunction D hD bound hb P (fun k x => ⟨x.1, f k x.2⟩)
    (fun k => ⟨fun xs => (bad k).1 (xs.map Sigma.snd),
      fun {_ _} hp => (bad k).2 (hp.map Sigma.snd)⟩)

end PDG
end SystemAlgebra
