module

public import Commons.Definitions.AbstractModel
public import Mathlib.Data.List.Basic

/-!
# Legal histories of an abstract computation model

`Admitted.prefix` preserves legal reads, the ordinary-query budget, and terminal submission
under nonempty prefixes. `Admitted.length_le` bounds the total length by `k + 1`.
`admitted_snoc_iff` checks the next command from the previous legal history and its initialized
addresses. These certificates supply the domain of the register converter's outside interface.
-/

@[expose] public section

namespace Commons.AbstractModel

variable
  -- `M` gives command arities; `ι` names registers, compared by the selected equality test.
  {S P ι : Type} {M : AbstractModel S P} [DecidableEq ι]

/-- A nonempty prefix of an admitted history is admitted. -/
lemma Admitted.prefix
    -- `input` is initially populated, and `k` bounds ordinary commands.
    {input : ι} {k : ℕ} {p h : List (M.Command ι)}
    -- `hp` selects the prefix `p`; `hne` excludes the empty history.
    (hp : p <+: h) (hne : p ≠ []) (hh : M.Admitted input k h) :
    M.Admitted input k p := by
  obtain ⟨-, count, last, reads⟩ := hh
  refine ⟨hne, (hp.sublist.countP_le).trans count, fun z hz => last z ?_,
    fun t z hz => reads t z (hz.trans hp)⟩
  -- A command before the prefix's last command is also before the full history's last one.
  obtain ⟨rest, rfl⟩ := hp
  rcases List.eq_nil_or_concat rest with rfl | ⟨rest, w, rfl⟩
  · simpa only [List.append_nil] using hz
  · rw [List.concat_eq_append, ← List.append_assoc, List.dropLast_concat]
    exact List.mem_append_left _ (List.dropLast_subset p hz)

/-- At most `k` ordinary commands and one terminal submission give total length at most `k+1`. -/
lemma Admitted.length_le
    -- `input` is initially populated; `h` is admitted with ordinary-query allowance `k`.
    {input : ι} {k : ℕ} {h : List (M.Command ι)}
    (hh : M.Admitted input k h) : h.length ≤ k + 1 := by
  obtain ⟨hne, count, last, -⟩ := hh
  -- Every command before the last is ordinary and therefore charged to k.
  have before : h.dropLast.length ≤ k := by
    rw [← List.countP_eq_length.mpr last]
    exact ((List.dropLast_sublist h).countP_le).trans count
  have := List.length_pos_iff.mpr hne
  rw [List.length_dropLast] at before
  omega

/-- Appending `z` preserves admission exactly when the budget holds, no submission preceded
`z`, and every operand of `z` was initialized by its prefix. -/
lemma admitted_snoc_iff
    -- `input` names the initial register; `k` bounds computation and query commands together.
    (input : ι) (k : ℕ)
    -- `h` contains earlier commands; `z` is the next command.
    (h : List (M.Command ι)) (z : M.Command ι) :
    M.Admitted input k (h ++ [z]) ↔
      (h = [] ∨ M.Admitted input k h) ∧ (h ++ [z]).countP M.ordinary ≤ k ∧
        (∀ u ∈ h, M.ordinary u) ∧ M.reads z ⊆ M.initialized input h := by
  constructor
  · intro hh
    refine ⟨?_, hh.2.1, ?_, hh.2.2.2 h z (List.prefix_refl _)⟩
    · by_cases he : h = []
      · exact Or.inl he
      · exact Or.inr (hh.prefix (List.prefix_append _ _) he)
    · simpa only [List.dropLast_concat] using hh.2.2.1
  · rintro ⟨prior, count, ordinary, reads⟩
    refine ⟨List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), count,
      by simpa only [List.dropLast_concat] using ordinary, ?_⟩
    intro t u hpref
    -- A prefix either reaches the new command or stays in the earlier history.
    rcases List.prefix_concat_iff.mp hpref with same | hp
    · obtain ⟨rfl, hu⟩ := List.append_inj' same rfl
      obtain rfl := List.singleton_injective hu
      exact reads
    · rcases prior with rfl | prior
      · simp only [List.prefix_nil, List.append_eq_nil_iff,
          List.cons_ne_nil, and_false] at hp
      · exact prior.2.2.2 t u hp

end Commons.AbstractModel
