module

public import RandomSystems.Cumulative.Presentation.Sequence.Defs
public import RandomSystems.Cumulative.PDSSequence

/-!
# Coherent presentations from fixed conditional kernels

`presentationLevel_map_cutSample` restricts the independent table before realizing it.
`presentationLevel_behavior` identifies each level with its cumulative cut. Together they give
`IsRandomSystem.exists_pdsSequence`: every normalized behavior over finite alphabets has a
coherent sequence of normalized deterministic presentations.

On supported tables the realization square commutes:

```text
table at n ── realization ──▶ certified system at n
    │ coordinate restriction          │ cutSample
    ▼                                 ▼
table at m ── realization ──▶ certified system at m
```
-/

@[expose] public section

namespace SystemAlgebra.IsRandomSystem

open Probability Probability.Distribution Presentation

-- `A`, `B` are finite query/reply alphabets; `hp` normalizes behavior `p` on query domain `D`.
variable {A B : Type} [Fintype A] [Fintype B]
variable {D : List (A × B) → A → Prop} {p : List (A × B) → ℝ} (hp : IsRandomSystem D p)

/-- Restricting a sampled deterministic system preserves the exact earlier-level law. -/
lemma presentationLevel_map_cutSample
    -- `hmn` says the retained horizon `m` is no larger than the sampled horizon `n`.
    {m n : ℕ} (hmn : m ≤ n) :
    (hp.presentationLevel n).map (PDS.cutSample D hmn) = hp.presentationLevel m := by
  classical
  let R (k : ℕ) := cut D p hp k
  let μ (k : ℕ) (j : Node A B k) : ProbDist (Option B) :=
    ⟨hp.isSubprobabilistic.replyChoice j.1.1 j.2,
      hp.isSubprobabilistic.replyChoice_isProbDist j.1.1 j.2⟩
  let F (k : ℕ) : (Node A B k → Option B) →
      {s : System A B // IsDDS s ∧ HasDomain (cutDomain D k) s} :=
    (R k).2.isSubprobabilistic.presentationSample
    (fun _ hh => (R k).mass_eq_zero_of_bound_lt hh) _
    (fun g hg => ⟨(realization g).2, (R k).hasDomain_realization hg⟩)
  -- Each cut uses the same global conditional kernels at its retained nodes.
  have tables (k : ℕ) : (ProbDist.pi (μ k)).1 =
      (R k).2.isSubprobabilistic.choiceLaw k := (hp.choiceLaw_cutMass k).symm
  -- The level is the pushforward of that fixed-kernel table law.
  have level (k : ℕ) : hp.presentationLevel k = (ProbDist.pi (μ k)).map (F k) := by
    apply Subtype.ext
    exact congrArg (fTransform (F k)) (tables k).symm
  let restrict := fun c : Node A B n → Option B => c ∘ nodeInclusion hmn
  -- Coordinatewise support survives the injective node restriction.
  have supported (c : Node A B n → Option B) (hc : c ∈ (ProbDist.pi (μ n)).1.support) :
      restrict c ∈ (ProbDist.pi (μ m)).1.support := by
    apply (ProbDist.mem_support_pi_iff (μ m) _).mpr
    intro j
    exact (ProbDist.mem_support_pi_iff (μ n) c).mp hc (nodeInclusion hmn j)
  -- Supported samplers realize their tables, so deterministic restriction commutes.
  have realizes (k : ℕ) (c : Node A B k → Option B)
      (hc : c ∈ (ProbDist.pi (μ k)).1.support) :
      (F k c).1 = (realization (choiceAt c)).1 :=
    (R k).2.isSubprobabilistic.presentationSample_val_of_mem (n := k)
      (fun _ hh => (R k).mass_eq_zero_of_bound_lt hh) _ _ c (by rwa [← tables k])
  have square (c : Node A B n → Option B) (hc : c ∈ (ProbDist.pi (μ n)).1.support) :
      PDS.cutSample D hmn (F n c) = F m (restrict c) := by
    apply Subtype.ext
    change cutSystem (F n c).1 m = (F m (restrict c)).1
    rw [realizes n c hc, realizes m (restrict c) (supported c hc)]
    exact cutSystem_realization_choiceAt hmn c
  -- The selected independent coordinates have exactly the earlier table law.
  have marginal : (ProbDist.pi (μ n)).map restrict = ProbDist.pi (μ m) :=
    ProbDist.map_pi_comp (μ n) (nodeInclusion hmn) (nodeInclusion hmn).injective
  rw [level n, level m]
  calc
    ((ProbDist.pi (μ n)).map (F n)).map (PDS.cutSample D hmn) =
        (ProbDist.pi (μ n)).map (PDS.cutSample D hmn ∘ F n) := ProbDist.map_map _ _ _
    _ = (ProbDist.pi (μ n)).map (F m ∘ restrict) :=
      Subtype.ext (fTransform_congr_support square)
    _ = ((ProbDist.pi (μ n)).map restrict).map (F m) := (ProbDist.map_map _ _ _).symm
    _ = (ProbDist.pi (μ m)).map (F m) := congrArg (ProbDist.map (F m)) marginal

/-- Each presentation level has exactly the cumulative behavior of that finite cut. -/
lemma presentationLevel_behavior (n : ℕ) :
    PDS.behavior (hp.presentationLevel n).1 (hp.presentationLevel n).2 = cut D p hp n := by
  apply RandomSystem.ext
  intro h
  exact (cut D p hp n).2.isSubprobabilistic.presentation_mass _ _ _ h

include hp in
/-- Every normalized cumulative behavior over finite alphabets has a coherent presentation. -/
theorem exists_pdsSequence : ∃ P : PDSSequence A B D, P.behavior = p := by
  let P : PDSSequence A B D :=
    { level := hp.presentationLevel
      compatible := fun n => hp.presentationLevel_map_cutSample (Nat.le_succ n) }
  refine ⟨P, ?_⟩
  funext h
  change PDS.behavior (hp.presentationLevel h.length).1 _ h = p h
  rw [hp.presentationLevel_behavior]
  exact cut_apply_of_length_le D p hp h.length h le_rfl

end SystemAlgebra.IsRandomSystem
