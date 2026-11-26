module

public import Probability.List
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Card

/-!
# Permutations extending list positions

`List.exists_perm_apply_idxOf_eq` extends an injective evaluation of a finite list to a
permutation of its label alphabet. The cardinality bound comes from the same injection;
`idxOf` supplies the position labels without an additional rank representation.
-/

@[expose] public section

namespace List

/-- An injection on a finite list extends from its distinct positions to a permutation of `B`. -/
theorem exists_perm_apply_idxOf_eq
    -- `xs` lists distinct `A`-values; its equality test is the one used by `idxOf`.
    {A B : Type*} [BEq A] [LawfulBEq A] [Fintype B]
    (xs : List A) (distinct : xs.Nodup)
    -- `labels` enumerates `B`; `evaluate` is injective only on entries of `xs`.
    (labels : Fin (Fintype.card B) ≃ B) (evaluate : A → B)
    (good : Set.InjOn evaluate {a | a ∈ xs}) :
    -- `capacity` bounds the list size; `θ` sends each position label to its evaluated value.
    ∃ capacity : xs.length ≤ Fintype.card B, ∃ θ : Equiv.Perm B,
      ∀ a (present : a ∈ xs),
        θ (labels ⟨xs.idxOf a, (idxOf_lt_length_of_mem present).trans_le capacity⟩) =
          evaluate a := by
  classical
  let J := {a // a ∈ xs.toFinset}
  have mapped : Set.InjOn evaluate (xs.toFinset : Set A) := by
    intro a ha b hb equal
    exact good (mem_toFinset.mp ha) (mem_toFinset.mp hb) equal
  have capacity : xs.length ≤ Fintype.card B := by
    simpa only [toFinset_card_of_nodup distinct, Finset.card_univ] using
      (Finset.card_le_card_of_injOn evaluate
        (t := (Finset.univ : Finset B)) (fun _ _ => Finset.mem_univ _) mapped)
  -- List positions and evaluated values give two embeddings of the same finite set.
  let ranked : J ↪ B :=
    ⟨fun a => labels ⟨xs.idxOf a.1,
        (idxOf_lt_length_of_mem (mem_toFinset.mp a.2)).trans_le capacity⟩,
      fun a b equal => Subtype.ext ((idxOf_inj (mem_toFinset.mp a.2)).mp
        (congrArg Fin.val (labels.injective equal)))⟩
  let evaluated : J ↪ B :=
    ⟨fun a => evaluate a.1,
      fun a b equal => Subtype.ext (mapped a.2 b.2 equal)⟩
  obtain ⟨θ, agrees⟩ := Equiv.Perm.exists_extending_pair
    ranked evaluated ranked.injective evaluated.injective
  exact ⟨capacity, θ, fun a present => agrees ⟨a, mem_toFinset.mpr present⟩⟩

end List
