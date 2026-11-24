module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Set.Function

/-!
# Directed partial-permutation tables for sponge proofs

A query at `x` and an inverse query at `π x` determine the same pair `(x, π x)`.
`insertEdge` records the direction of the first query. `insertEdge_query_agrees_iff`
characterizes the permutations consistent with the resulting table.

For absorption, each block `b` gives one edge:

```text
state ──absorb b──▶ input ──π──▶ next state
       same capacity
```

`recordAbsorption_local` lets a second permutation replay the path using the recorded pairs.
Under `CapacityCollisionFree`, the capacity identifies each reached parent. If absorption at
that parent is injective in the block, `blocks_eq_of_absorbBlocks_eq` recovers the whole block
sequence from the final state. This uses the rooted graph of [1, §§3.2, 4.3].

## References

[1] Guido Bertoni, Joan Daemen, Michaël Peeters, and Gilles Van Assche, *On the
Indifferentiability of the Sponge Construction*, EUROCRYPT 2008, LNCS 4965, pp. 181–197.
-/

@[expose] public section

namespace Commons.Sponge

section Table

variable {State : Type*}

/-- A recorded directed permutation edge `(input, output)` with its query direction. -/
structure PermutationEdge (State : Type*) where
  /-- The permutation input `x` of the recorded pair `(x, π x)`. -/
  input : State
  /-- The permutation output `y = π x` of the recorded pair. -/
  output : State
  /-- `false` for a forward query `π(input)` and `true` for an inverse query `π⁻¹(output)`. -/
  inverse : Bool
  deriving DecidableEq

/-- The answer to the query: the output of a forward call or the preimage of an inverse call. -/
def PermutationEdge.freshEndpoint (edge : PermutationEdge State) : State :=
  if edge.inverse then edge.input else edge.output

/-- States produced as outputs of forward permutation queries in `table`. -/
def forwardOutputs (table : List (PermutationEdge State)) : Set State :=
  {s | ∃ edge ∈ table, edge.inverse = false ∧ edge.output = s}

/-- Inputs produced as preimages of inverse permutation queries in `table`. -/
def inverseInputs (table : List (PermutationEdge State)) : Set State :=
  {s | ∃ edge ∈ table, edge.inverse = true ∧ edge.input = s}

/-- Every recorded edge in `table` agrees with `π`. -/
def AgreesWith (table : List (PermutationEdge State)) (π : Equiv.Perm State) : Prop :=
  ∀ edge ∈ table, π edge.input = edge.output

/-- The directed edge induced by querying `π` in direction `inverse` at `point`. -/
def queryEdge (π : Equiv.Perm State) (inverse : Bool) (point : State) : PermutationEdge State :=
  if inverse then ⟨π.symm point, point, true⟩ else ⟨point, π point, false⟩

/-- Append `edge` to `table` unless its input is already recorded. -/
def insertEdge [DecidableEq State] (table : List (PermutationEdge State))
    (edge : PermutationEdge State) : List (PermutationEdge State) :=
  if ∃ prev ∈ table, prev.input = edge.input then table else table ++ [edge]

/-- A previously recorded input keeps its original edge, including its query direction. -/
lemma insertEdge_eq_self_of_input_mem [DecidableEq State] {table : List (PermutationEdge State)}
    {edge prev : PermutationEdge State} (hprev : prev ∈ table) (hx : prev.input = edge.input) :
    insertEdge table edge = table :=
  ite_eq_left ⟨prev, hprev, hx⟩

/-- The set of distinct `(input, output)` constraint pairs present in `table`. -/
def recordedPairs [DecidableEq State] (table : List (PermutationEdge State)) :
    Finset (State × State) :=
  (table.map fun edge => (edge.input, edge.output)).toFinset

/-- Capacities already taken by `zeroCap` or any endpoint of an edge in `table`. -/
def occupiedCapacities {Cap : Type*} [DecidableEq Cap]
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) : Finset Cap :=
  insert zeroCap
    ((table.map fun edge => capacity edge.input).toFinset ∪
      (table.map fun edge => capacity edge.output).toFinset)

/-- Capacity collision-freeness invariant [1, §4.3]: forward outputs have distinct nonzero
capacities, and inverse inputs avoid `zeroCap` and every forward output's capacity. -/
def CapacityCollisionFree {Cap : Type*}
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) : Prop :=
  Set.InjOn capacity (forwardOutputs table) ∧
    (∀ s ∈ forwardOutputs table, capacity s ≠ zeroCap) ∧
    (∀ x ∈ inverseInputs table,
      capacity x ≠ zeroCap ∧ ∀ s ∈ forwardOutputs table, capacity x ≠ capacity s)

/-- Freshness condition on a newly added edge: its freshly sampled endpoint avoids all capacities
occupied by `zeroCap` or existing endpoints in `table`. -/
def AvoidsOccupiedCapacity {Cap : Type*} [DecidableEq Cap]
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) (edge : PermutationEdge State) : Prop :=
  capacity edge.freshEndpoint ∉ occupiedCapacities capacity zeroCap table

lemma forwardOutputs_nil : forwardOutputs ([] : List (PermutationEdge State)) = ∅ := by
  ext s
  simp only [forwardOutputs, Set.mem_ofPred_eq, List.not_mem_nil, false_and, exists_false,
    Set.mem_empty_iff_false]

lemma inverseInputs_nil : inverseInputs ([] : List (PermutationEdge State)) = ∅ := by
  ext s
  simp only [inverseInputs, Set.mem_ofPred_eq, List.not_mem_nil, false_and, exists_false,
    Set.mem_empty_iff_false]

/-- The empty table trivially satisfies `CapacityCollisionFree`. -/
lemma capacityCollisionFree_nil {Cap : Type*}
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap) :
    CapacityCollisionFree capacity zeroCap ([] : List (PermutationEdge State)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [forwardOutputs_nil]
    exact Set.injOn_empty _
  · intro s hs
    rw [forwardOutputs_nil] at hs
    cases hs
  · intro x hx
    rw [inverseInputs_nil] at hx
    cases hx

lemma forwardOutputs_append_singleton (table : List (PermutationEdge State))
    (edge : PermutationEdge State) :
    forwardOutputs (table ++ [edge]) =
      if edge.inverse = false then insert edge.output (forwardOutputs table)
      else forwardOutputs table := by
  ext s
  by_cases hi : edge.inverse = false
  · simp only [hi, ↓reduceIte, forwardOutputs, Set.mem_insert_iff, Set.mem_ofPred_eq,
      List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨e, he | rfl, hf, hs⟩
      · exact Or.inr ⟨e, he, hf, hs⟩
      · exact Or.inl hs.symm
    · rintro (rfl | ⟨e, he, hf, hs⟩)
      · exact ⟨edge, Or.inr rfl, hi, rfl⟩
      · exact ⟨e, Or.inl he, hf, hs⟩
  · simp only [hi, forwardOutputs, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨e, he | rfl, hf, hs⟩
      · exact ⟨e, he, hf, hs⟩
      · exact False.elim (hi hf)
    · rintro ⟨e, he, hf, hs⟩
      exact ⟨e, Or.inl he, hf, hs⟩

lemma inverseInputs_append_singleton (table : List (PermutationEdge State))
    (edge : PermutationEdge State) :
    inverseInputs (table ++ [edge]) =
      if edge.inverse = true then insert edge.input (inverseInputs table)
      else inverseInputs table := by
  ext s
  by_cases hi : edge.inverse = true
  · simp only [hi, ↓reduceIte, inverseInputs, Set.mem_insert_iff, Set.mem_ofPred_eq,
      List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨e, he | rfl, hf, hs⟩
      · exact Or.inr ⟨e, he, hf, hs⟩
      · exact Or.inl hs.symm
    · rintro (rfl | ⟨e, he, hf, hs⟩)
      · exact ⟨edge, Or.inr rfl, hi, rfl⟩
      · exact ⟨e, Or.inl he, hf, hs⟩
  · simp only [hi, inverseInputs, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨e, he | rfl, hf, hs⟩
      · exact ⟨e, he, hf, hs⟩
      · exact False.elim (hi hf)
    · rintro ⟨e, he, hf, hs⟩
      exact ⟨e, Or.inl he, hf, hs⟩

lemma occupiedCapacities_zero {Cap : Type*} [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap) (table : List (PermutationEdge State)) :
    zeroCap ∈ occupiedCapacities capacity zeroCap table :=
  Finset.mem_insert_self _ _

lemma occupiedCapacities_input {Cap : Type*} [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap) (table : List (PermutationEdge State))
    {edge : PermutationEdge State} (he : edge ∈ table) :
    capacity edge.input ∈ occupiedCapacities capacity zeroCap table := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨edge, he, rfl⟩)

lemma occupiedCapacities_output {Cap : Type*} [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap) (table : List (PermutationEdge State))
    {edge : PermutationEdge State} (he : edge ∈ table) :
    capacity edge.output ∈ occupiedCapacities capacity zeroCap table := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨edge, he, rfl⟩)

/-- The occupied capacity set has at most `2 * table.length + 1` elements. -/
lemma occupiedCapacities_card_le {Cap : Type*} [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap) (table : List (PermutationEdge State)) :
    (occupiedCapacities capacity zeroCap table).card ≤ 2 * table.length + 1 := by
  have hi : (table.map fun edge => capacity edge.input).toFinset.card ≤ table.length :=
    (List.toFinset_card_le _).trans (by simp only [List.length_map, le_rfl])
  have ho : (table.map fun edge => capacity edge.output).toFinset.card ≤ table.length :=
    (List.toFinset_card_le _).trans (by simp only [List.length_map, le_rfl])
  have hu :
      ((table.map fun edge => capacity edge.input).toFinset ∪
        (table.map fun edge => capacity edge.output).toFinset).card ≤
      2 * table.length := by
    calc
      ((table.map fun edge => capacity edge.input).toFinset ∪
          (table.map fun edge => capacity edge.output).toFinset).card
        ≤ (table.map fun edge => capacity edge.input).toFinset.card +
          (table.map fun edge => capacity edge.output).toFinset.card := Finset.card_union_le _ _
      _ ≤ table.length + table.length := Nat.add_le_add hi ho
      _ = 2 * table.length := (Nat.two_mul table.length).symm
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hu 1)

/-- In a capacity-collision-free table, any edge whose input shares the capacity of a
zero-capacity state or a forward output must be a forward edge. -/
theorem rooted_edge_forward {Cap : Type*}
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table)
    {edge : PermutationEdge State} (he : edge ∈ table)
    -- `parent` is a reached state (having `zeroCap` or lying in `forwardOutputs table`).
    (parent : State) (hp : capacity parent = zeroCap ∨ parent ∈ forwardOutputs table)
    (hcap : capacity edge.input = capacity parent) : edge.inverse = false := by
  cases hi : edge.inverse with
  | false => rfl
  | true =>
    have hinv : edge.input ∈ inverseInputs table := ⟨edge, he, hi, rfl⟩
    rcases hp with hz | hf
    · exact False.elim ((hg.2.2 _ hinv).1 (hcap.trans hz))
    · exact False.elim ((hg.2.2 _ hinv).2 parent hf hcap)

/-- Appending an edge satisfying `AvoidsOccupiedCapacity` preserves `CapacityCollisionFree`. -/
theorem capacityCollisionFree_append {Cap : Type*} [DecidableEq Cap]
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table)
    (edge : PermutationEdge State) (hf : AvoidsOccupiedCapacity capacity zeroCap table edge) :
    CapacityCollisionFree capacity zeroCap (table ++ [edge]) := by
  cases hi : edge.inverse with
  | false =>
    have hcap : capacity edge.output ∉ occupiedCapacities capacity zeroCap table := by
      simpa only [AvoidsOccupiedCapacity, PermutationEdge.freshEndpoint, hi, Bool.false_eq_true,
        ↓reduceIte] using hf
    have hfor := forwardOutputs_append_singleton table edge
    have hinv := inverseInputs_append_singleton table edge
    simp only [hi, ↓reduceIte, Bool.false_eq_true] at hfor hinv
    rw [CapacityCollisionFree, hfor, hinv]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb he
      rcases Set.mem_insert_iff.mp ha with rfl | haOld
      · rcases Set.mem_insert_iff.mp hb with rfl | hbOld
        · rfl
        · obtain ⟨e, hm, _, rfl⟩ := hbOld
          exact False.elim (hcap (he ▸ occupiedCapacities_output capacity zeroCap table hm))
      · rcases Set.mem_insert_iff.mp hb with rfl | hbOld
        · obtain ⟨e, hm, _, rfl⟩ := haOld
          exact False.elim (hcap (he.symm ▸ occupiedCapacities_output capacity zeroCap table hm))
        · exact hg.1 haOld hbOld he
    · intro s hs
      rcases Set.mem_insert_iff.mp hs with rfl | hsOld
      · intro hz
        exact hcap (hz ▸ occupiedCapacities_zero capacity zeroCap table)
      · exact hg.2.1 s hsOld
    · intro x hx
      refine ⟨(hg.2.2 x hx).1, ?_⟩
      intro s hs
      rcases Set.mem_insert_iff.mp hs with rfl | hsOld
      · obtain ⟨e, hm, _, rfl⟩ := hx
        intro he
        exact hcap (he.symm ▸ occupiedCapacities_input capacity zeroCap table hm)
      · exact (hg.2.2 x hx).2 s hsOld
  | true =>
    have hcap : capacity edge.input ∉ occupiedCapacities capacity zeroCap table := by
      simpa only [AvoidsOccupiedCapacity, PermutationEdge.freshEndpoint, hi, ↓reduceIte] using hf
    have hfor := forwardOutputs_append_singleton table edge
    have hinv := inverseInputs_append_singleton table edge
    simp only [hi, ↓reduceIte, Bool.true_eq_false] at hfor hinv
    rw [CapacityCollisionFree, hfor, hinv]
    refine ⟨hg.1, hg.2.1, ?_⟩
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hxOld
    · refine ⟨fun hz => hcap (hz ▸ occupiedCapacities_zero capacity zeroCap table), ?_⟩
      intro s hs he
      obtain ⟨e, hm, _, rfl⟩ := hs
      exact hcap (he ▸ occupiedCapacities_output capacity zeroCap table hm)
    · exact hg.2.2 x hxOld

/-- Inserting an edge via `insertEdge` preserves `CapacityCollisionFree`: duplicate inputs leave
the table unchanged, while fresh edges satisfy `AvoidsOccupiedCapacity`. -/
theorem capacityCollisionFree_insertEdge {Cap : Type*} [DecidableEq State] [DecidableEq Cap]
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table)
    (edge : PermutationEdge State)
    -- Only newly inserted (non-duplicate) edges must avoid occupied capacities.
    (hf : (∀ prev ∈ table, prev.input ≠ edge.input) →
      AvoidsOccupiedCapacity capacity zeroCap table edge) :
    CapacityCollisionFree capacity zeroCap (insertEdge table edge) := by
  unfold insertEdge
  split_ifs with hdup
  · exact hg
  · exact capacityCollisionFree_append capacity zeroCap table hg edge
      (hf (fun prev hp he => hdup ⟨prev, hp, he⟩))

/-- Appending an edge preserves injectivity of `digest` on `forwardOutputs` when a forward edge's
output avoids existing digests. -/
theorem digest_injOn_append {Out : Type*}
    -- `digest` extracts the observable output projection.
    (digest : State → Out)
    (table : List (PermutationEdge State)) (hdig : Set.InjOn digest (forwardOutputs table))
    (edge : PermutationEdge State)
    (hf : edge.inverse = false →
      ∀ s ∈ forwardOutputs table, digest edge.output ≠ digest s) :
    Set.InjOn digest (forwardOutputs (table ++ [edge])) := by
  rw [forwardOutputs_append_singleton]
  split_ifs with hi
  · intro a ha b hb he
    rcases Set.mem_insert_iff.mp ha with rfl | haOld
    · rcases Set.mem_insert_iff.mp hb with rfl | hbOld
      · rfl
      · exact False.elim (hf hi b hbOld he)
    · rcases Set.mem_insert_iff.mp hb with rfl | hbOld
      · exact False.elim (hf hi a haOld he.symm)
      · exact hdig haOld hbOld he
  · exact hdig

/-- Inserting an edge via `insertEdge` preserves injectivity of `digest` on `forwardOutputs`. -/
theorem digest_injOn_insertEdge {Out : Type*} [DecidableEq State]
    -- `digest` extracts the observable output projection.
    (digest : State → Out)
    (table : List (PermutationEdge State)) (hdig : Set.InjOn digest (forwardOutputs table))
    (edge : PermutationEdge State)
    -- Only newly inserted forward edges must avoid existing digests.
    (hf : (∀ prev ∈ table, prev.input ≠ edge.input) →
      edge.inverse = false → ∀ s ∈ forwardOutputs table, digest edge.output ≠ digest s) :
    Set.InjOn digest (forwardOutputs (insertEdge table edge)) := by
  unfold insertEdge
  split_ifs with hdup
  · exact hdig
  · exact digest_injOn_append digest table hdig edge
      (hf (fun prev hp he => hdup ⟨prev, hp, he⟩))

/-- In a capacity-collision-free table, a root state with capacity `zeroCap` and all forward
outputs have pairwise distinct capacities. -/
lemma reached_capacity_injective {Cap : Type*}
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    -- `root` is an initial state whose capacity equals `zeroCap`.
    (root : State) (hroot : capacity root = zeroCap)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table) :
    Set.InjOn capacity (insert root (forwardOutputs table)) := by
  intro a ha b hb he
  rcases Set.mem_insert_iff.mp ha with rfl | haOld
  · rcases Set.mem_insert_iff.mp hb with rfl | hbOld
    · rfl
    · exact False.elim (hg.2.1 b hbOld (he.symm.trans hroot))
  · rcases Set.mem_insert_iff.mp hb with rfl | hbOld
    · exact False.elim (hg.2.1 a haOld (he.trans hroot))
    · exact hg.1 haOld hbOld he

lemma insertEdge_subset [DecidableEq State] (table : List (PermutationEdge State))
    (edge : PermutationEdge State) :
    ∀ prev ∈ table, prev ∈ insertEdge table edge := by
  intro prev hp
  unfold insertEdge
  split_ifs
  · exact hp
  · exact List.mem_append_left _ hp

lemma length_insertEdge_le [DecidableEq State] (table : List (PermutationEdge State))
    (edge : PermutationEdge State) :
    (insertEdge table edge).length ≤ table.length + 1 := by
  unfold insertEdge
  split_ifs
  · exact Nat.le_succ _
  · simp only [List.length_append, List.length_singleton, le_rfl]

lemma insertEdge_input_mem [DecidableEq State] (table : List (PermutationEdge State))
    (edge : PermutationEdge State) :
    ∃ prev ∈ insertEdge table edge, prev.input = edge.input := by
  unfold insertEdge
  split_ifs with h
  · exact h
  · exact ⟨edge, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

lemma queryEdge_agrees (π : Equiv.Perm State) (inverse : Bool) (point : State) :
    π (queryEdge π inverse point).input = (queryEdge π inverse point).output := by
  cases inverse <;>
    simp only [queryEdge, Bool.false_eq_true, ↓reduceIte, Equiv.apply_symm_apply]

lemma insertEdge_agrees [DecidableEq State] (table : List (PermutationEdge State))
    (edge : PermutationEdge State) (π : Equiv.Perm State)
    (ht : AgreesWith table π) (he : π edge.input = edge.output) :
    AgreesWith (insertEdge table edge) π := by
  unfold insertEdge
  split_ifs
  · exact ht
  · intro item hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ht item hi
    · rw [List.mem_singleton.mp hi]
      exact he

/-- Inserting an edge agrees with `π` iff the existing table and the new edge both agree with
`π`. -/
theorem insertEdge_agrees_iff [DecidableEq State] (table : List (PermutationEdge State))
    (edge : PermutationEdge State) (π : Equiv.Perm State)
    -- If `edge.input` already appears in `table`, its existing output must match `edge.output`.
    (hdup : ∀ prev ∈ table, prev.input = edge.input → prev.output = edge.output) :
    AgreesWith (insertEdge table edge) π ↔
      AgreesWith table π ∧ π edge.input = edge.output := by
  constructor
  · intro ha
    refine ⟨fun prev hp => ha prev (insertEdge_subset table edge prev hp), ?_⟩
    unfold insertEdge at ha
    split_ifs at ha with h
    · obtain ⟨prev, hp, hpi⟩ := h
      rw [← hpi, ha prev hp, hdup prev hp hpi]
    · exact ha edge (List.mem_append_right _ (List.mem_singleton_self _))
  · rintro ⟨ht, he⟩
    exact insertEdge_agrees table edge π ht he

lemma queryEdge_constraint (π : Equiv.Perm State) (inverse : Bool) (point : State)
    (ρ : Equiv.Perm State) :
    ρ (queryEdge π inverse point).input = (queryEdge π inverse point).output ↔
      (if inverse then ρ.symm point = π.symm point else ρ point = π point) := by
  cases inverse with
  | false =>
    simp only [queryEdge, Bool.false_eq_true, ↓reduceIte]
  | true =>
    simp only [queryEdge, ↓reduceIte]
    constructor
    · intro h
      exact (ρ.eq_symm_apply.mpr h).symm
    · intro h
      exact ρ.eq_symm_apply.mp h.symm

/-- Inserting a query edge of `π` constrains `ρ` to agree with `table` and match `π` on the
queried point. -/
theorem insertEdge_query_agrees_iff [DecidableEq State] (table : List (PermutationEdge State))
    (π : Equiv.Perm State) (ht : AgreesWith table π)
    (inverse : Bool) (point : State) (ρ : Equiv.Perm State) :
    AgreesWith (insertEdge table (queryEdge π inverse point)) ρ ↔
      AgreesWith table ρ ∧
        (if inverse then ρ.symm point = π.symm point else ρ point = π point) := by
  rw [insertEdge_agrees_iff, queryEdge_constraint]
  intro prev hp hpi
  rw [← ht prev hp, hpi, queryEdge_agrees]

/-- The recorded constraint pair set has cardinality at most `table.length`. -/
lemma recordedPairs_card_le [DecidableEq State] (table : List (PermutationEdge State)) :
    (recordedPairs table).card ≤ table.length :=
  (List.toFinset_card_le _).trans (by simp only [List.length_map, le_rfl])

/-- Agreement with `table` is equivalent to satisfying every constraint in `recordedPairs`. -/
theorem recordedPairs_agrees_iff [DecidableEq State] (table : List (PermutationEdge State))
    (π : Equiv.Perm State) :
    AgreesWith table π ↔ ∀ pair ∈ recordedPairs table, π pair.1 = pair.2 := by
  constructor
  · intro ha pair hp
    obtain ⟨edge, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact ha edge he
  · intro hc edge he
    exact hc (edge.input, edge.output)
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨edge, he, rfl⟩))

end Table

section Absorption

variable {State Block : Type*}

/-- The final state reached by absorbing `blocks` from `state` through `absorb` and `π`. -/
def absorbBlocks (absorb : State → Block → State) (π : Equiv.Perm State)
    (state : State) (blocks : List Block) : State :=
  blocks.foldl (fun s block => π (absorb s block)) state

/-- The list of permutation inputs queried while absorbing `blocks` from `state`. -/
def absorptionCalls (absorb : State → Block → State) (π : Equiv.Perm State)
    (state : State) : List Block → List State
  | [] => []
  | block :: rest =>
    let x := absorb state block
    x :: absorptionCalls absorb π (π x) rest

/-- Record every forward permutation edge queried while absorbing `blocks` from `state`. -/
def recordAbsorption [DecidableEq State] (absorb : State → Block → State)
    (π : Equiv.Perm State) :
    List (PermutationEdge State) → State → List Block → List (PermutationEdge State)
  | table, _, [] => table
  | table, state, block :: rest =>
    let x := absorb state block
    let table' := insertEdge table (queryEdge π false x)
    recordAbsorption absorb π table' (π x) rest

lemma absorbBlocks_nil (absorb : State → Block → State) (π : Equiv.Perm State)
    (state : State) :
    absorbBlocks absorb π state [] = state := rfl

lemma absorbBlocks_cons (absorb : State → Block → State) (π : Equiv.Perm State)
    (state : State) (block : Block) (blocks : List Block) :
    absorbBlocks absorb π state (block :: blocks) =
      absorbBlocks absorb π (π (absorb state block)) blocks := rfl

lemma absorbBlocks_append (absorb : State → Block → State) (π : Equiv.Perm State)
    (state : State) (first second : List Block) :
    absorbBlocks absorb π state (first ++ second) =
      absorbBlocks absorb π (absorbBlocks absorb π state first) second := by
  simp only [absorbBlocks, List.foldl_append]

lemma absorptionCalls_nil (absorb : State → Block → State) (π : Equiv.Perm State)
    (state : State) :
    absorptionCalls absorb π state [] = [] := rfl

lemma absorptionCalls_cons (absorb : State → Block → State) (π : Equiv.Perm State)
    (state : State) (block : Block) (blocks : List Block) :
    absorptionCalls absorb π state (block :: blocks) =
      absorb state block :: absorptionCalls absorb π (π (absorb state block)) blocks := rfl

lemma absorptionCalls_append (absorb : State → Block → State) (π : Equiv.Perm State)
    (state : State) (first second : List Block) :
    absorptionCalls absorb π state (first ++ second) =
      absorptionCalls absorb π state first ++
        absorptionCalls absorb π (absorbBlocks absorb π state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons block first ih =>
    simp only [List.cons_append, absorptionCalls_cons, ih, absorbBlocks_cons]

lemma recordAbsorption_subset [DecidableEq State] (absorb : State → Block → State)
    (π : Equiv.Perm State) (table : List (PermutationEdge State)) (state : State)
    (blocks : List Block) :
    ∀ edge ∈ table, edge ∈ recordAbsorption absorb π table state blocks := by
  induction blocks generalizing table state with
  | nil => intro edge he; exact he
  | cons block rest ih =>
    intro edge he
    exact ih _ _ edge (insertEdge_subset table _ edge he)

lemma length_recordAbsorption_le [DecidableEq State] (absorb : State → Block → State)
    (π : Equiv.Perm State) (table : List (PermutationEdge State)) (state : State)
    (blocks : List Block) :
    (recordAbsorption absorb π table state blocks).length ≤ table.length + blocks.length := by
  induction blocks generalizing table state with
  | nil => simp only [recordAbsorption, List.length_nil, Nat.add_zero, le_rfl]
  | cons block rest ih =>
    simp only [recordAbsorption, List.length_cons]
    have hstep :=
      length_insertEdge_le table (queryEdge π false (absorb state block))
    have hrest := ih (insertEdge table (queryEdge π false (absorb state block)))
      (π (absorb state block))
    omega

lemma recordAbsorption_agrees [DecidableEq State] (absorb : State → Block → State)
    (π : Equiv.Perm State) (table : List (PermutationEdge State)) (ha : AgreesWith table π)
    (state : State) (blocks : List Block) :
    AgreesWith (recordAbsorption absorb π table state blocks) π := by
  induction blocks generalizing table state with
  | nil => exact ha
  | cons block rest ih =>
    exact ih _ (insertEdge_agrees table _ π ha rfl) _

lemma recordAbsorption_covers [DecidableEq State] (absorb : State → Block → State)
    (π : Equiv.Perm State) (table : List (PermutationEdge State)) (state : State)
    (blocks : List Block) :
    ∀ x ∈ absorptionCalls absorb π state blocks,
      ∃ edge ∈ recordAbsorption absorb π table state blocks, edge.input = x := by
  induction blocks generalizing table state with
  | nil => intro x hx; cases hx
  | cons block rest ih =>
    intro x hx
    simp only [absorptionCalls_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · obtain ⟨edge, he, hi⟩ :=
        insertEdge_input_mem table ⟨absorb state block, π (absorb state block), false⟩
      exact ⟨edge, recordAbsorption_subset absorb π _ _ rest edge he, hi⟩
    · exact ih _ _ x hx

/-- Absorption recording is local: any two permutations agreeing with the recorded table produce
the same recorded edges and final state. -/
theorem recordAbsorption_local [DecidableEq State] (absorb : State → Block → State)
    (π ρ : Equiv.Perm State) (table : List (PermutationEdge State)) (state : State)
    (blocks : List Block)
    (hπ : AgreesWith (recordAbsorption absorb π table state blocks) π)
    (hρ : AgreesWith (recordAbsorption absorb π table state blocks) ρ) :
    recordAbsorption absorb ρ table state blocks =
        recordAbsorption absorb π table state blocks ∧
      absorbBlocks absorb ρ state blocks = absorbBlocks absorb π state blocks := by
  induction blocks generalizing table state with
  | nil => exact ⟨rfl, rfl⟩
  | cons block rest ih =>
    have hmem :
        ∃ edge ∈ recordAbsorption absorb π table state (block :: rest),
          edge.input = absorb state block :=
      recordAbsorption_covers absorb π table state (block :: rest) _ List.mem_cons_self
    obtain ⟨edge, he, hi⟩ := hmem
    have hval : ρ (absorb state block) = π (absorb state block) := by
      rw [← hi, hρ edge he, hπ edge he]
    simp only [recordAbsorption, absorbBlocks_cons, queryEdge, Bool.false_eq_true, ↓reduceIte, hval]
    exact ih _ (π (absorb state block)) hπ hρ

/-- Every nonempty rooted block sequence covered by a capacity-collision-free table ends at a
forward output. -/
lemma absorbBlocks_mem_forwardOutputs {Cap : Type*}
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    -- `absorb` preserves `capacity` on every block.
    (absorb : State → Block → State) (hcap : ∀ s b, capacity (absorb s b) = capacity s)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table)
    (π : Equiv.Perm State) (ha : AgreesWith table π)
    (state : State) (hs : capacity state = zeroCap ∨ state ∈ forwardOutputs table)
    (blocks : List Block) (hn : blocks ≠ [])
    (hc : ∀ x ∈ absorptionCalls absorb π state blocks, ∃ edge ∈ table, edge.input = x) :
    absorbBlocks absorb π state blocks ∈ forwardOutputs table := by
  induction blocks generalizing state with
  | nil => exact False.elim (hn rfl)
  | cons block blocks ih =>
    let x := absorb state block
    obtain ⟨edge, he, hx⟩ := hc x List.mem_cons_self
    have hf : edge.inverse = false :=
      rooted_edge_forward capacity zeroCap table hg he state hs (by rw [hx, hcap])
    have hnext : π x ∈ forwardOutputs table := ⟨edge, he, hf, (hx ▸ ha edge he).symm⟩
    cases blocks with
    | nil => exact hnext
    | cons next blocks =>
      exact ih (π x) (Or.inr hnext) (List.cons_ne_nil _ _)
        (fun y hy => hc y (List.mem_cons_of_mem _ hy))

/-- Every prefix endpoint of a covered rooted block sequence is either `root` or a forward
output. -/
lemma absorbBlocks_reached {Cap : Type*}
    (capacity : State → Cap) (zeroCap : Cap)
    (absorb : State → Block → State) (hcap : ∀ s b, capacity (absorb s b) = capacity s)
    (root : State) (hroot : capacity root = zeroCap)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table)
    (π : Equiv.Perm State) (ha : AgreesWith table π) (blocks : List Block)
    (hc : ∀ x ∈ absorptionCalls absorb π root blocks, ∃ edge ∈ table, edge.input = x) :
    absorbBlocks absorb π root blocks ∈ insert root (forwardOutputs table) := by
  by_cases hn : blocks = []
  · subst blocks
    exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _
      (absorbBlocks_mem_forwardOutputs capacity zeroCap absorb hcap table hg π ha root
        (Or.inl hroot) blocks hn hc)

/-- A covered rooted path in a capacity-collision-free table is uniquely determined by its final
state. -/
theorem blocks_eq_of_absorbBlocks_eq {Cap : Type*}
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    -- `absorb` preserves capacity and is injective in the absorbed block at every state.
    (absorb : State → Block → State) (hcap : ∀ s b, capacity (absorb s b) = capacity s)
    (hinj : ∀ s, Function.Injective (absorb s))
    -- `root` is the initial state with capacity `zeroCap`.
    (root : State) (hroot : capacity root = zeroCap)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table)
    (π : Equiv.Perm State) (ha : AgreesWith table π)
    (first second : List Block)
    (hf : ∀ x ∈ absorptionCalls absorb π root first, ∃ edge ∈ table, edge.input = x)
    (hs : ∀ x ∈ absorptionCalls absorb π root second, ∃ edge ∈ table, edge.input = x)
    (he : absorbBlocks absorb π root first = absorbBlocks absorb π root second) :
    first = second := by
  induction first using List.reverseRecOn generalizing second with
  | nil =>
    by_cases hn : second = []
    · exact hn.symm
    · have hmem :=
        absorbBlocks_mem_forwardOutputs capacity zeroCap absorb hcap table hg π ha root
          (Or.inl hroot) second hn hs
      have hzero : capacity (absorbBlocks absorb π root second) = zeroCap :=
        (congrArg capacity he.symm).trans hroot
      exact False.elim (hg.2.1 _ hmem hzero)
  | append_singleton first block ih =>
    cases second using List.reverseRecOn with
    | nil =>
      have hn : first ++ [block] ≠ [] :=
        List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
      have hmem :=
        absorbBlocks_mem_forwardOutputs capacity zeroCap absorb hcap table hg π ha root
          (Or.inl hroot) _ hn hf
      have hzero : capacity (absorbBlocks absorb π root (first ++ [block])) = zeroCap :=
        (congrArg capacity he).trans hroot
      exact False.elim (hg.2.1 _ hmem hzero)
    | append_singleton second last =>
      -- Dropping the last block keeps every earlier query covered by the same table.
      have prefixCovered {bs : List Block} {b : Block}
          (covered : ∀ x ∈ absorptionCalls absorb π root (bs ++ [b]),
            ∃ edge ∈ table, edge.input = x) :
          ∀ x ∈ absorptionCalls absorb π root bs, ∃ edge ∈ table, edge.input = x := by
        rw [absorptionCalls_append] at covered
        exact fun x hx => covered x (List.mem_append_left _ hx)
      have hfp := prefixCovered hf
      have hsp := prefixCovered hs
      simp only [absorbBlocks_append, absorbBlocks_cons, absorbBlocks_nil] at he
      -- Equal final states have the same permutation input and hence the same parent capacity.
      have hx := π.injective he
      have hcapEq := congrArg capacity hx
      simp only [hcap] at hcapEq
      have hparent := reached_capacity_injective capacity zeroCap root hroot table hg
        (absorbBlocks_reached capacity zeroCap absorb hcap root hroot table hg π ha first hfp)
        (absorbBlocks_reached capacity zeroCap absorb hcap root hroot table hg π ha second hsp)
        hcapEq
      -- Once the parent is known, injectivity of absorption determines the last block.
      have hb : block = last := by
        rw [hparent] at hx
        exact hinj _ hx
      rw [ih second hfp hsp hparent, hb]

end Absorption

end Commons.Sponge
