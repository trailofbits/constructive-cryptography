module

public import Commons.Definitions.AbstractModel.Registers
public import Commons.Definitions.AbstractModel.Domain
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# Initialized operands and register updates

`read_isSome` characterizes successful operand reads. `registers_snoc` and `initialized_snoc`
follow the value map and its initialized-address set through one command. Together they prove
`registers_isSome`: along histories whose reads are legal, the occupied registers are exactly
the initial address and computation destinations. This supplies the register converter's
legal-domain read certificate without a finiteness assumption on names or values.
-/

@[expose] public section

namespace Commons.AbstractModel

variable
  -- `ι` names registers and `W` carries their internal values.
  {ι W : Type}

/-- The designated input register contains the initial value. -/
lemma initial_self [DecidableEq ι] (input : ι) (x : W) : initial input x input = some x :=
  Function.update_self _ _ _

/-- Exactly the designated input address is initialized. -/
lemma initial_isSome [DecidableEq ι] (input : ι) (x : W) (i : ι) :
    (initial input x i).isSome ↔ i = input := by
  by_cases hi : i = input
  · subst i
    exact iff_of_true (by rw [initial_self]; rfl) rfl
  · rw [initial, Function.update_of_ne hi]
    exact iff_of_false Bool.false_ne_true hi

/-- Reading succeeds exactly when every selected operand address contains a value. -/
lemma read_isSome
    -- `r` is the register map; `a` selects the `n` operands.
    (r : ι → Option W) {n : ℕ} (a : Fin n → ι) :
    (read r a).isSome ↔ ∀ j, (r (a j)).isSome := by
  unfold read
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false Bool.false_ne_true h

variable
  -- `M` gives command arities; `operate` interprets its operations on `W` at a fixed parameter.
  {S P : Type} {M : Commons.AbstractModel S P} [DecidableEq ι]
  (operate : (o : M.Operation) → (Fin (M.arity o) → W) → W)

/-- Appending a command applies its one register update after the earlier commands. -/
lemma registers_snoc
    -- `r` is the initial map; `h` is the completed prefix and `z` the next command.
    (r : ι → Option W) (h : List (M.Command ι)) (z : M.Command ι) :
    M.registers operate r (h ++ [z]) = M.write operate (M.registers operate r h) z := by
  simp only [registers, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A computation adds its destination to initialized addresses; other commands preserve them. -/
lemma initialized_snoc
    -- `input` is initially populated; `h` is the prefix and `z` the next command.
    (input : ι) (h : List (M.Command ι)) (z : M.Command ι) :
    M.initialized input (h ++ [z]) =
      match M.target z with
      | none => M.initialized input h
      | some i => insert i (M.initialized input h) := by
  cases hz : M.target z <;>
    simp only [initialized, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      hz, List.toFinset_append, List.toFinset_nil, Finset.union_empty, List.toFinset_cons,
      Finset.union_insert, Finset.insert_comm]

/-- With legal reads, the registers containing values are exactly the initialized addresses. -/
theorem registers_isSome
    -- `r` initially contains a value exactly at `input`; `h` lists completed commands.
    (r : ι → Option W) (input : ι)
    (hinit : ∀ i, (r i).isSome ↔ i = input) (h : List (M.Command ι))
    -- `legal` requires each command's operands to have been initialized by its prefix.
    (legal : ∀ t z, t ++ [z] <+: h → M.reads z ⊆ M.initialized input t)
    (i : ι) : (M.registers operate r h i).isSome ↔ i ∈ M.initialized input h := by
  induction h using List.reverseRecOn generalizing i with
  | nil =>
    simpa only [registers, List.foldl_nil, initialized, List.filterMap_nil, List.toFinset_nil,
      Finset.mem_insert, Finset.notMem_empty, or_false] using hinit i
  | append_singleton h z ih =>
    -- Earlier commands retain the invariant; the new command may read only those addresses.
    have prior : ∀ j, (M.registers operate r h j).isSome ↔ j ∈ M.initialized input h :=
      fun j => ih (fun t u hu => legal t u (hu.trans (List.prefix_append h [z]))) j
    have arguments := legal h z (List.prefix_refl _)
    rw [registers_snoc, initialized_snoc]
    obtain ⟨o | ρ | _, z⟩ := z
    · obtain ⟨a, destination⟩ := z
      have ready : (read (M.registers operate r h) a).isSome :=
        (read_isSome _ _).mpr fun j => (prior (a j)).mpr
          (arguments (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩))
      -- A successful computation initializes its destination and keeps every other address.
      by_cases he : i = destination
      · subst i
        simpa only [write, Function.update_self, Option.isSome_map, target,
          Finset.mem_insert, true_or] using iff_true_intro ready
      · simpa only [write, Function.update_of_ne he, target, Finset.mem_insert, he,
          false_or] using prior i
    · exact prior i
    · exact prior i

end Commons.AbstractModel
