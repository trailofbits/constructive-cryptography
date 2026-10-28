import Probability.DependentProduct
import RandomSystems.Cumulative.ParallelAll

/-!
# Presentations of finite parallel random systems

An n-ary cumulative product can be computed from independent deterministic presentations of
its components. The complete transcript event splits into one event per component, so its
mass is the product of the component masses. This theorem accepts arbitrary finite
presentations, including systems whose off-tree values differ.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” The independent product is the chosen finite presentation of that
resource family.
-/

namespace SystemAlgebra.RandomSystem

open Probability

variable {K : Type} [Fintype K] [DecidableEq K]
  {A B : K → Type} [∀ k, Fintype (A k)] [∀ k, Fintype (B k)]
  {D : ∀ k, Domain (A k) (B k)}

/-- Independent component presentations present the n-ary cumulative product. Jost,
Thesis, printed p. 17, regards finite disjoint-interface resources as one; this equality
derives the transcript law of the independent product from component transcript laws. -/
lemma parallelAll_mass_of_presentations {ι : K → Type}
    (R : ∀ k, RandomSystem (A k) (B k) (D k))
    (P : ∀ k, Distribution (ι k)) (s : ∀ k, ι k → System (A k) (B k))
    (hR : ∀ k h, R k h = (P k).mass (fun i =>
      Replies (s k i) (h.map Prod.fst) (h.map Prod.snd)))
    (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelAll R h = (Distribution.piDep P).mass (fun st =>
      Replies (parAll (fun k => s k (st k))) (h.map Prod.fst) (h.map Prod.snd)) := by
  -- Split each complete joint transcript into its tagged component transcripts.
  rw [parallelAll_mass, Distribution.mass_congr (Distribution.piDep P)
    (fun st => replies_parAll_iff (fun k => s k (st k)) h)]
  by_cases hh : parallelAllConsistent h
  · -- Consistency leaves a componentwise event, whose independent mass factors.
    simp only [hh, if_true, true_and]
    rw [Distribution.piDep_mass_forall P (fun k i =>
      Replies (s k i) ((restrictExchanges k h).map Prod.fst)
        ((restrictExchanges k h).map Prod.snd))]
    exact Finset.prod_congr rfl fun k _ => hR k _
  · -- An inconsistent tag has zero mass in both descriptions.
    simp only [hh, if_false, false_and]
    exact (Distribution.mass_eq_zero_of_forall_not _ (fun _ hf => hf)).symm

end SystemAlgebra.RandomSystem
