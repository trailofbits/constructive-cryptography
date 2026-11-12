module

public import RandomSystems.Cumulative.PDSSequence.Defs

/-!
# From coherent finite presentations to cumulative behavior

`PDS.behavior_cutSample` turns exact sample restriction into finite cumulative restriction.
`PDSSequence.level_coherent` then supplies the hypothesis of finite-cut gluing:
`behavior_isRandomSystem` normalizes the resulting behavior and `cut_behavior` recovers each
finite-level behavior. `behavior_eq_iff` characterizes equality by behavioral equivalence of
levels; it retains their exact sample laws as presentation data.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

-- `A`, `B` are the finite alphabets of the bounded behavior carrier; `D` is the query domain.
variable {A B : Type} [Fintype A] [Fintype B] (D : List (A × B) → A → Prop)

/-- The behavior of a restricted sample law is the corresponding cumulative cut. -/
lemma PDS.behavior_cutSample {m n : ℕ} (hmn : m ≤ n)
    -- `P` is a normalized finite law at horizon `n`; `h` is the observed transcript.
    (P : ProbDist {s : System A B // IsDDS s ∧ HasDomain (cutDomain D n) s})
    (h : List (A × B)) :
    PDS.behavior (P.map (PDS.cutSample D hmn)).1 (P.map (PDS.cutSample D hmn)).2 h =
      cutMass (PDS.behavior P.1 P.2) m h := by
  by_cases hh : h.length ≤ m
  · rw [cutMass, ite_eq_left hh, PDS.behavior_mass, PDS.behavior_mass, ProbDist.map_val]
    exact PDS.behaviorMass_cutSample D hmn P.1 _ _ (by rwa [List.length_map])
  · rw [cutMass, ite_eq_right hh]
    exact RandomSystem.mass_eq_zero_of_bound_lt _ (Nat.lt_of_not_ge hh)

namespace PDSSequence

variable {D}

/-- Exact sample compatibility preserves every cumulative mass at an earlier level. -/
lemma level_coherent (P : PDSSequence A B D) (n : ℕ)
    (h : List (A × B)) (hh : h.length ≤ n) :
    PDS.behavior (P.level (n + 1)).1 (P.level (n + 1)).2 h =
      PDS.behavior (P.level n).1 (P.level n).2 h := by
  have cut := PDS.behavior_cutSample D (Nat.le_succ n) (P.level (n + 1)) h
  rw [P.compatible, cutMass, ite_eq_left hh] at cut
  exact cut.symm

/-- A coherent normalized presentation induces a normalized cumulative behavior on `D`. -/
theorem behavior_isRandomSystem (P : PDSSequence A B D) : IsRandomSystem D P.behavior :=
  RandomSystem.limitMass_isRandomSystem D _ P.level_coherent

/-- Every finite cut recovers the behavior of that level's sample law. -/
theorem cut_behavior (P : PDSSequence A B D) (n : ℕ) :
    IsRandomSystem.cut D P.behavior P.behavior_isRandomSystem n =
      PDS.behavior (P.level n).1 (P.level n).2 :=
  RandomSystem.cut_limitMass D _ P.level_coherent n

/-- Cumulative equality is exactly behavioral equivalence at every finite level. -/
lemma behavior_eq_iff (P Q : PDSSequence A B D) :
    P.behavior = Q.behavior ↔ ∀ n, Equivalent (P.level n).1 (Q.level n).1 := by
  constructor
  · intro same n
    apply (PDS.behavior_eq_iff (P.level n).2 (Q.level n).2).mp
    rw [← P.cut_behavior n, ← Q.cut_behavior n]
    congr 1
  · intro same
    funext h
    exact congrArg (fun R => R h)
      ((PDS.behavior_eq_iff (P.level h.length).2 (Q.level h.length).2).mpr (same h.length))

end PDSSequence

end SystemAlgebra
