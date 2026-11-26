module

public import Commons.Definitions.AbstractModel
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Legal histories of an abstract computation model

`Admitted.prefix` preserves legal reads, the ordinary-query budget, and terminal submission
under nonempty prefixes. `Admitted.length_le` bounds the total length by `k + 1`.
`admitted_snoc_iff` checks the next command from the previous legal history and its initialized
addresses. These certificates supply the domain of the register converter's outside interface.
`Admitted.mapCommand` transports legality along any address map;
`admitted_mapCommand_iff` reflects it along an embedding.
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

/-! ## Address maps -/

omit [DecidableEq ι] in
/-- An address decoder also decodes operand vectors, destinations, and complete commands. -/
lemma mapCommand_leftInverse
    -- `f` encodes addresses and `g` decodes them; submitted values are unchanged.
    {κ : Type} (f : ι → κ) (g : κ → ι) (inverse : Function.LeftInverse g f) :
    Function.LeftInverse (M.mapCommand g) (M.mapCommand f) := by
  have decoded (x : ι) : g (f x) = x := inverse x
  intro z
  obtain ⟨o | ρ | _, z⟩ := z
  · obtain ⟨a, destination⟩ := z
    simp only [mapCommand, Sigma.map, id_eq, mapInput, Function.comp_def, decoded]
  · simp only [mapCommand, Sigma.map, id_eq, mapInput, Function.comp_def, decoded]
  · rfl

/-- The operands of a renamed command are the image of its original operands. -/
lemma reads_mapCommand
    {κ : Type} [DecidableEq κ] (f : ι → κ) (z : M.Command ι) :
    M.reads (M.mapCommand f z) = (M.reads z).image f := by
  obtain ⟨o | ρ | _, z⟩ := z
  · obtain ⟨a, destination⟩ := z
    simp only [mapCommand, Sigma.map, id_eq, mapInput, reads, Finset.image_image]
  · simp only [mapCommand, Sigma.map, id_eq, mapInput, reads, Finset.image_image]
  · simp only [mapCommand, Sigma.map, id_eq, mapInput, reads, Finset.image_empty]

omit [DecidableEq ι] in
/-- A computation's destination is renamed; a query or submission still has none. -/
lemma target_mapCommand
    {κ : Type} (f : ι → κ) (z : M.Command ι) :
    M.target (M.mapCommand f z) = (M.target z).map f := by
  obtain ⟨o | ρ | _, z⟩ := z
  · obtain ⟨a, destination⟩ := z
    rfl
  · rfl
  · rfl

omit [DecidableEq ι] in
/-- Address maps preserve which commands consume the ordinary-query allowance. -/
lemma ordinary_mapCommand
    {κ : Type} (f : ι → κ) (z : M.Command ι) :
    M.ordinary (M.mapCommand f z) = M.ordinary z := by
  obtain ⟨o | ρ | _, z⟩ := z
  · obtain ⟨a, destination⟩ := z
    rfl
  · rfl
  · rfl

/-- Renaming the initial address and every destination maps the initialized-register set. -/
lemma initialized_mapCommand
    -- `f` maps addresses; `input` is initially populated and `h` contains completed commands.
    {κ : Type} [DecidableEq κ] (f : ι → κ) (input : ι) (h : List (M.Command ι)) :
    M.initialized (f input) (h.map (M.mapCommand f)) = (M.initialized input h).image f := by
  have destinations : (h.map (M.mapCommand f)).filterMap M.target =
      (h.filterMap M.target).map f := by
    simp only [List.filterMap_map, List.map_filterMap, Function.comp_def, target_mapCommand]
  simp only [initialized, Finset.image_insert]
  congr 1
  rw [destinations]
  exact Multiset.toFinset_map f (h.filterMap M.target)

/-- Every address map preserves legal reads, terminal submission, and the query allowance. -/
lemma Admitted.mapCommand
    -- `f` may identify addresses; every previously initialized operand remains initialized.
    {κ : Type} [DecidableEq κ] (f : ι → κ)
    {input : ι} {k : ℕ} {h : List (M.Command ι)} (admitted : M.Admitted input k h) :
    M.Admitted (f input) k (h.map (M.mapCommand f)) := by
  induction h using List.reverseRecOn with
  | nil => exact (admitted.1 rfl).elim
  | append_singleton h z ih =>
    obtain ⟨prior, count, ordinary, operands⟩ := (admitted_snoc_iff input k h z).mp admitted
    rw [List.map_append, List.map_singleton, admitted_snoc_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases prior with rfl | prior
      · exact Or.inl rfl
      · exact Or.inr (ih prior)
    · simpa only [List.countP_append, List.countP_cons, List.countP_nil, List.countP_map,
        Function.comp_def, ordinary_mapCommand] using count
    · simpa only [List.forall_mem_map, ordinary_mapCommand] using ordinary
    · rw [reads_mapCommand, initialized_mapCommand]
      exact Finset.image_mono f operands

/-- An embedding preserves and reflects admission of a renamed history. -/
theorem admitted_mapCommand_iff
    -- `d` keeps distinct addresses distinct; `input` is the initially populated register.
    {κ : Type} [DecidableEq κ] (d : ι ↪ κ) (input : ι) (k : ℕ)
    (h : List (M.Command ι)) :
    M.Admitted (d input) k (h.map (M.mapCommand d)) ↔ M.Admitted input k h := by
  classical
  -- The existing input address supplies a default only for the inverse outside `d`'s range.
  let : Nonempty ι := ⟨input⟩
  have inverse : Function.LeftInverse (Function.invFun d) d :=
    Function.leftInverse_invFun d.injective
  have commands := mapCommand_leftInverse (M := M) d (Function.invFun d) inverse
  constructor
  · intro admitted
    have restored := admitted.mapCommand (Function.invFun d)
    simpa only [inverse input, List.map_map, commands.comp_eq_id, List.map_id]
      using restored
  · exact fun admitted => admitted.mapCommand d

end Commons.AbstractModel
