module

public import Probability.Counting

/-!
# Conditional collisions after distinct tested inputs

`uniform_mass_transcript_collision_le_card` refines the conditional collision bound in
`Probability.Counting`: after a collision-free revealed history with `d` distinct inputs,
a fresh query contributes at most `d / |Y|` times the history mass, and a repeat contributes
zero. Deduplicating a consistent history removes repeated records without changing its event.
This supplies the per-query probability contract for adaptive collision games.

The sampled object remains the uniform function table of [1, §3.2, p. 6]:
“a uniformly chosen function table F”.

## References

1. U. Maurer and R. Renner. From Indifferentiability to Constructive Cryptography (and Back).
   In *Theory of Cryptography*, TCC 2016-B, LNCS 9985, pp. 3–24, Springer, 2016.
-/

@[expose] public section

namespace Probability.Counting

/-- A repeated query has zero collision cost. A fresh query costs at most the number of
distinct previously tested inputs divided by `|Y|`, times the mass of the revealed history.
At the identity projection, this replaces `|h|` in
`uniform_mass_transcript_projected_collision_le` by the number of distinct inputs. -/
lemma uniform_mass_transcript_collision_le_card
    -- `X`, `Y` are finite table alphabets, with inhabited replies in `Y`.
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    -- `h` is the revealed input/reply history; `x` is the next query.
    (h : List (X × Y)) (x : X)
    -- `hgood` says that equal replies in `h` came from the same input.
    (hgood : ∀ a ∈ h, ∀ b ∈ h, a.2 = b.2 → a.1 = b.1) :
    (Distribution.uniform (X → Y)).mass (fun f =>
      (∀ z ∈ h, f z.1 = z.2) ∧ ∃ z ∈ h, z.1 ≠ x ∧ f x = z.2) ≤
      (if x ∈ h.map Prod.fst then 0 else ((h.map Prod.fst).toFinset.card : ℝ) /
        Fintype.card Y) *
        (Distribution.uniform (X → Y)).mass (fun f => ∀ z ∈ h, f z.1 = z.2) := by
  classical
  -- A repeat cannot create a collision on a good history.
  by_cases hx : x ∈ h.map Prod.fst
  · rw [ite_eq_left hx, zero_mul]
    apply le_of_eq
    apply Distribution.mass_eq_zero_of_forall_not
    rintro f ⟨hf, z, hz, hne, he⟩
    obtain ⟨w, hw, hwx⟩ := List.mem_map.mp hx
    have hzw := hgood z hz w hw (he.symm.trans (hwx ▸ hf w hw))
    exact hne (hzw.trans hwx)
  · rw [ite_eq_right hx]
    -- Consistent histories have one recorded pair per distinct input after deduplication.
    by_cases hc : ∃ f : X → Y, ∀ z ∈ h, f z.1 = z.2
    · obtain ⟨f, hf⟩ := hc
      have hi : Set.InjOn Prod.fst (h.toFinset : Set (X × Y)) := by
        intro a ha b hb hab
        apply Prod.ext hab
        rw [← hf a (List.mem_toFinset.mp ha), ← hf b (List.mem_toFinset.mp hb), hab]
      have hcard : h.dedup.length = (h.map Prod.fst).toFinset.card := by
        rw [← List.card_toFinset]
        change h.toFinset.card = ((↑h : Multiset (X × Y)).map Prod.fst).toFinset.card
        rw [Multiset.toFinset_map]
        exact (Finset.card_image_iff.mpr hi).symm
      -- The conditional collision bound counts the deduplicated history.
      have hb := uniform_mass_transcript_projected_collision_le id
        (Distribution.fTransform_id _) h.dedup x (fun a ha b hb =>
          hgood a (List.mem_dedup.mp ha) b (List.mem_dedup.mp hb))
      simpa only [List.mem_dedup, id_eq, hcard] using hb
    · -- No function answers an inconsistent history, so its joint event has zero mass.
      have hz : (Distribution.uniform (X → Y)).mass (fun f =>
          (∀ z ∈ h, f z.1 = z.2) ∧ ∃ z ∈ h, z.1 ≠ x ∧ f x = z.2) = 0 :=
        Distribution.mass_eq_zero_of_forall_not _ (fun f hf => hc ⟨f, hf.1⟩)
      rw [hz]
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Distribution.uniform_nonNeg.mass_nonneg _)

end Probability.Counting
