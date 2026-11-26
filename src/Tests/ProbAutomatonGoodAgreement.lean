module

public import RandomSystems.System.ProbAutomaton
public import Mathlib.Tactic.IntervalCases

/-!
# Good-prefix agreement on supported states

Two automata retain a natural-number state. They agree at initial state zero on unmarked
queries, differ on marked queries, and may differ at unreachable states. The good predicate
also reads replies. The tests apply the belief law to signed initial mass `-3`, then compare
normalized cumulative masses: two good replies have mass one, while a marked query separates
the systems with masses one and zero.
-/

@[expose] public section

open SystemAlgebra Probability Probability.Distribution

namespace Tests.ProbAutomatonGoodAgreement

/-- One Boolean query at the unit port; true queries are marked. -/
abbrev Query := Sigma (fun _ : Unit => Bool)

/-- At most two nonempty input prefixes are admitted. -/
abbrev domain : Domain Query Query := Domain.ofInputs
  (fun xs => xs ≠ [] ∧ xs.length ≤ 2) 2 (fun _ h => h.2)

/-- Both test automata retain a natural-number state; the left always replies false. -/
def left : Nat → (_ : Unit) → Bool → Nat × Bool := fun s _ _ => (s, false)

/-- The right differs on marked queries and at unreachable nonzero states. -/
def right : Nat → (_ : Unit) → Bool → Nat × Bool :=
  fun s _ marked => (s, marked || (s != 0))

/-- A good history contains only unmarked queries answered false. -/
def good (h : List (Query × Query)) : Prop :=
  ∀ z ∈ h, z.1.2 = false ∧ z.2.2 = false

lemma good_prefix (p h : List (Query × Query)) (hp : p <+: h) (hg : good h) : good p :=
  fun z hz => hg z (hp.subset hz)

/-- The left automaton's state is retained through every input sequence. -/
lemma state_retained (s : Nat) (xs : List Query) : stateAfter left s xs = s := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => rw [stateAfter_snoc, ih]; rfl

/-- Even signed starting mass at zero cannot reach another state. -/
lemma left_support_zero (w : ℝ) (h : List (Query × Query)) {s : Nat}
    (hs : s ∈ ((ProbStep.ofDeterministic left).belief domain
      (Finsupp.single 0 w) h).support) : s = 0 := by
  rw [ProbStep.belief_ofDeterministic] at hs
  obtain ⟨a, ha, rfl⟩ := mem_support_fTransform _ _ hs
  have zero : a = 0 := (Finsupp.mem_support_single a 0 w).mp
    (support_restrict_subset _ _ ha) |>.1
  rw [state_retained, zero]

/-- At supported states, a good extension selects an identical reply law. -/
lemma same_selected (w : ℝ) (h : List (Query × Query)) (x y : Query)
    (hg : good (h ++ [(x, y)])) (_admitted : domain h x)
    (s : Nat) (hs : s ∈ ((ProbStep.ofDeterministic left).belief domain
      (Finsupp.single 0 w) h).support) :
    ((ProbStep.ofDeterministic left).outcome s x).restrict (fun p => p.2 = y) =
      ((ProbStep.ofDeterministic right).outcome s x).restrict (fun p => p.2 = y) := by
  have zero := left_support_zero w h hs
  subst s
  have unmarked := (hg (x, y) (by simp)).1
  rcases x with ⟨i, x⟩
  cases i
  change x = false at unmarked
  subst x
  rfl

/-- The two good exchanges both ask false and receive false. -/
def twoGood : List (Query × Query) :=
  [(⟨(), false⟩, ⟨(), false⟩), (⟨(), false⟩, ⟨(), false⟩)]

lemma twoGood_good : good twoGood := by simp [good, twoGood]

/-- The raw agreement law accepts negative starting mass on an infinite state carrier. -/
example : (ProbStep.ofDeterministic left).belief domain (Finsupp.single 0 (-3)) twoGood =
    (ProbStep.ofDeterministic right).belief domain (Finsupp.single 0 (-3)) twoGood :=
  ProbStep.belief_eq_of_outcome_restrict_eq
    (ProbStep.ofDeterministic left) (ProbStep.ofDeterministic right) domain
    (Finsupp.single 0 (-3)) good good_prefix (same_selected (-3)) twoGood twoGood_good

/-- Taking weights transfers the same local contract to normalized cumulative systems. -/
lemma good_mass_eq :
    RandomSystem.ofProbAutomaton domain (ProbStep.ofDeterministic left)
      (ProbDist.single 0) twoGood =
    RandomSystem.ofProbAutomaton domain (ProbStep.ofDeterministic right)
      (ProbDist.single 0) twoGood :=
  RandomSystem.ofProbAutomaton_apply_eq_of_outcome_restrict_eq
    (ProbStep.ofDeterministic left) (ProbStep.ofDeterministic right) domain
    (ProbDist.single 0) good good_prefix (same_selected 1) twoGood twoGood_good

/-- The common good coefficient is one, so the equality compares positive mass. -/
lemma good_mass_one :
    RandomSystem.ofProbAutomaton domain (ProbStep.ofDeterministic left)
      (ProbDist.single 0) twoGood = 1 := by
  rw [RandomSystem.ofProbAutomaton_apply, ProbStep.belief_ofDeterministic,
    weight_fTransform, weight_restrict]
  change Distribution.mass (Finsupp.single 0 1) _ = 1
  rw [mass_single]
  apply ite_eq_left
  refine ⟨rfl, ?_⟩
  intro k hk _
  change k < 2 at hk
  interval_cases k <;>
    simp [twoGood, filterDom, automatonSystem, stateAfter, left]

/-- A marked query separates the two systems at the false reply. -/
example :
    RandomSystem.ofProbAutomaton domain (ProbStep.ofDeterministic left) (ProbDist.single 0)
      [(⟨(), true⟩, ⟨(), false⟩)] = 1 ∧
    RandomSystem.ofProbAutomaton domain (ProbStep.ofDeterministic right) (ProbDist.single 0)
      [(⟨(), true⟩, ⟨(), false⟩)] = 0 := by
  constructor
  · rw [RandomSystem.ofProbAutomaton_ofDeterministic_apply]
    change Distribution.mass (Finsupp.single 0 1) _ = 1
    rw [mass_single]
    apply ite_eq_left
    change Replies _ ([] ++ [(⟨(), true⟩ : Query)]) ([] ++ [(⟨(), false⟩ : Query)])
    rw [replies_snoc]
    simp [filterDom, automatonSystem, stateAfter, left]
  · rw [RandomSystem.ofProbAutomaton_ofDeterministic_apply]
    change Distribution.mass (Finsupp.single 0 1) _ = 0
    rw [mass_single]
    apply ite_eq_right
    change ¬ Replies _ ([] ++ [(⟨(), true⟩ : Query)]) ([] ++ [(⟨(), false⟩ : Query)])
    rw [replies_snoc]
    simp [filterDom, automatonSystem, stateAfter, right]

#print axioms ProbStep.belief_eq_of_outcome_restrict_eq
#print axioms RandomSystem.ofProbAutomaton_apply_eq_of_outcome_restrict_eq
#print axioms good_mass_eq
#print axioms good_mass_one

end Tests.ProbAutomatonGoodAgreement
