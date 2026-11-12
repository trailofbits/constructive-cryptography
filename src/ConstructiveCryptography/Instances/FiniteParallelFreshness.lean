module

public import ConstructiveCryptography.CryptographicAlgebra.FiniteParallel.Specification
public import ConstructiveCryptography.Instances.FiniteParallel
public import RandomSystems.Typed.FreshComponent
public import RandomSystems.Typed.ParallelAllSelection

/-!
# Freshness of a selected family member

`TypedSystem.AnswersFresh.parallelAll` applies `FiniteParallel.mem_parallelAll_of_mem` to the
freshness specification. Binary preservation supplies the left contract; renaming supplies
the split and reindex contracts. The selector's presentation equations identify the resulting
observer with `(Interface.selectExchange k₀ z).bind pick`.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability Probability.Distribution
open ConstructiveCryptography

/-- A selected component's fresh replies remain fresh in its independent family. -/
lemma AnswersFresh.parallelAll
    -- `R k` is the resource at interface `A k`; `k₀` selects the observed component.
    {K : Type} [Fintype K] [dK : DecidableEq K] {A : K → Interface}
    (R : ∀ k, TypedSystem (A k)) (k₀ : K)
    -- `pick` selects values in `C`; `μ v` bounds their conditional mass.
    {C : Type} [DecidableEq C]
    {pick : (Σ i, (A k₀).X i) × (Σ i, (A k₀).Y i) → Option C}
    {μ : Distribution C} (hμ : μ.NonNeg)
    -- `hR` is the sole component freshness premise.
    (hR : (R k₀).AnswersFresh pick μ) :
    (TypedSystem.parallelAll R).AnswersFresh
      (fun z => (Interface.selectExchange k₀ z).bind pick) μ := by
  classical
  -- The selected abstract family uses classical decisions; equality decisions are irrelevant.
  have hdK : dK = Classical.decEq K := Subsingleton.elim _ _
  subst dK
  let : DecidableEq (Option {k // k ≠ k₀}) := Classical.decEq _
  let : DecidableEq {k // k ≠ k₀} := Classical.decEq _
  let e := Equiv.optionSubtypeNe k₀
  let B := fun o => A (e o)
  let Index := fun I : Interface => (Σ i, I.X i) × (Σ i, I.Y i) → Option C
  -- Each map reads the same selected value through the head/tail and reindex presentations.
  let leftIndex : Index (B none) → Index ((B none).tensor (Interface.tensorAll
      (fun j => B (some j)))) := fun p z => match z with
    | (⟨.inl i, x⟩, ⟨.inl j, y⟩) => p (⟨i, x⟩, ⟨j, y⟩)
    | _ => none
  let splitIndex := fun p : Index ((B none).tensor (Interface.tensorAll
      (fun j => B (some j)))) => fun z => p
    (((optionSplitLabels B fun o i => (B o).X i).prodCongr
      (optionSplitLabels B fun o i => (B o).Y i)) z)
  let reindexIndex := fun p : Index (Interface.tensorAll B) => fun z => p
    (((reindexLabels e A fun k i => (A k).X i).prodCongr
      (reindexLabels e A fun k i => (A k).Y i)) z)
  -- The three specification contracts are the existing binary and rename laws.
  have transported := FiniteParallel.mem_parallelAll_of_mem
    (Index := Index) (fun I p => {W : TypedSystem I | W.AnswersFresh p μ}) e R
    leftIndex splitIndex reindexIndex
    (by
      intro p W hW h x v hx
      have bound := AnswersFresh.parallel_left
        (FiniteParallel.parallelAll fun j => R (e (some j))) hμ hW h x v hx
      obtain ⟨i | j, x⟩ := x <;> exact bound)
    (by
      intro p W hW
      exact AnswersFresh.rename
        (A := Interface.tensorAll B)
        (B := (B none).tensor (Interface.tensorAll fun j => B (some j)))
        (optionSplitPorts B)
        (optionSplitLabels B fun o i => (B o).X i)
        (optionSplitLabels B fun o i => (B o).Y i)
        (optionSplitLabels_fst B fun o i => (B o).X i)
        (optionSplitLabels_fst B fun o i => (B o).Y i)
        (tensor_domain_optionSplitLabels B) hW)
    (by
      intro p W hW
      exact AnswersFresh.rename
        (A := Interface.tensorAll A) (B := Interface.tensorAll B)
        (Equiv.sigmaCongrLeft (β := fun k => (A k).I) e).symm
        (reindexLabels e A fun k i => (A k).X i)
        (reindexLabels e A fun k i => (A k).Y i)
        (reindexLabels_fst e A fun k i => (A k).X i)
        (reindexLabels_fst e A fun k i => (A k).Y i)
        (tensorAll_domain_reindexLabels e A) hW) hR
  change (FiniteParallel.parallelAll R).AnswersFresh
    (reindexIndex (splitIndex (leftIndex pick))) μ at transported
  rw [Interface.cc_parallelAll_eq] at transported
  -- The two presentation equations turn the transported observer into direct selection.
  have observer : reindexIndex (splitIndex (leftIndex pick)) =
      fun z => (Interface.selectExchange k₀ z).bind pick := by
    funext z
    change reindexIndex (splitIndex (leftIndex pick)) z =
      (Interface.selectExchange (e none) z).bind pick
    rw [Interface.selectExchange_reindex]
    have split := Interface.selectExchange_optionSplit B
      (((reindexLabels e A fun k i => (A k).X i).prodCongr
        (reindexLabels e A fun k i => (A k).Y i)) z)
    -- The split selector uses derived Option decisions; the selected class uses classical ones.
    rw [Subsingleton.elim
      (@Option.instDecidableEq {k // k ≠ k₀} (Classical.decEq _))
      (Classical.decEq (Option {k // k ≠ k₀}))] at split
    rw [split]
    dsimp only [reindexIndex, splitIndex, leftIndex]
    generalize ((optionSplitLabels B fun o i => (B o).X i).prodCongr
      (optionSplitLabels B fun o i => (B o).Y i))
      (((reindexLabels e A fun k i => (A k).X i).prodCongr
        (reindexLabels e A fun k i => (A k).Y i)) z) = w
    obtain ⟨⟨(i | j), x⟩, ⟨(l | m), y⟩⟩ := w <;> rfl
  rw [observer] at transported
  exact transported

end SystemAlgebra.TypedSystem
