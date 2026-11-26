module

public import Commons.Definitions.AbstractModel.Domain
public import RandomSystems.System.FiniteQueries
public import Mathlib.Data.Finset.Option

/-!
# Finite register addresses

`exists_fin_address_encoding` codes a finite set of commands using a finite
address footprint containing the initial register, all operands, and every destination.
`exists_fin_address_encoding_of_queryBounded` applies it to the finite query support of
an adaptive bounded caller. Decoding recovers each supported command and its submitted value.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra

variable
  -- `S` carries register values, `P` model parameters, and `ι` register addresses.
  -- `M` supplies the operation and observation arities that determine command operands.
  {S P ι : Type} {M : Commons.AbstractModel S P} [DecidableEq ι]

/-- A finite command set uses finitely many operands, destinations and initial addresses. -/
theorem exists_fin_address_encoding
    -- `input` is the initial register; `K` is the finite set of possible caller commands.
    (input : ι) (K : Set (M.Command ι)) (finite : K.Finite) :
    -- `code` assigns finite addresses; `decode` embeds them back into the original registers.
    ∃ (n : ℕ) (code : ι → Fin n) (decode : Fin n ↪ ι),
      decode (code input) = input ∧
      (∀ z ∈ K, ∀ a, a ∈ M.reads z ∨ M.target z = some a → decode (code a) = a) ∧
      (∀ z ∈ K, M.mapCommand decode (M.mapCommand code z) = z) := by
  let addresses : M.Command ι → Finset ι := fun z => M.reads z ∪ (M.target z).toFinset
  let footprint : Set ι := insert input (⋃ z ∈ K, (addresses z : Set ι))
  have small : footprint.Finite :=
    (finite.biUnion (fun z _ => (addresses z).finite_toSet)).insert input
  obtain ⟨n, code, decode, inverse⟩ := small.exists_fin_encoding
  have initial : decode (code input) = input := inverse input (Set.mem_insert _ _)
  have covers (z : M.Command ι) (hz : z ∈ K) (a : ι)
      (ha : a ∈ M.reads z ∨ M.target z = some a) : decode (code a) = a := by
    apply inverse a
    apply Set.mem_insert_of_mem
    refine Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, ?_⟩⟩
    change a ∈ M.reads z ∪ (M.target z).toFinset
    rcases ha with operand | target
    · exact Finset.mem_union_left _ operand
    · exact Finset.mem_union_right _ (by rw [target]; exact Finset.mem_singleton_self a)
  refine ⟨n, code, decode, initial, covers, ?_⟩
  intro z hz
  exact mapCommand_mapCommand_eq_of_inverse_on code decode z
    (fun a ha => covers z hz a (Or.inl ha)) (fun a ha => covers z hz a (Or.inr ha))

/-- A bounded caller has one address code valid across every adaptive reply branch. -/
theorem exists_fin_address_encoding_of_queryBounded
    -- `B` carries replies; the command and register alphabets remain arbitrary.
    {B : Type} [_root_.Finite B] (input : ι) (E : DDE (M.Command ι) B)
    -- `bounded` limits every adaptive branch to fewer than `q` replies before another query.
    {q : ℕ} (bounded : QueryBounded q E) :
    -- `code` assigns finite addresses; `decode` embeds them back into the original registers.
    ∃ (n : ℕ) (code : ι → Fin n) (decode : Fin n ↪ ι),
      decode (code input) = input ∧
      (∀ ys z, z ∈ E.1 ys → ∀ a,
        a ∈ M.reads z ∨ M.target z = some a → decode (code a) = a) ∧
      (∀ ys z, z ∈ E.1 ys → M.mapCommand decode (M.mapCommand code z) = z) := by
  obtain ⟨n, code, decode, initial, addresses, commands⟩ :=
    exists_fin_address_encoding input {z | ∃ ys, z ∈ E.1 ys}
      (finite_queries_of_queryBounded E bounded)
  exact ⟨n, code, decode, initial,
    fun ys z hz => addresses z ⟨ys, hz⟩, fun ys z hz => commands z ⟨ys, hz⟩⟩

end Commons.AbstractModel
