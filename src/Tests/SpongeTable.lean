module

public import Commons.Schemes.Sponge.Table

/-!
# Contract tests for directed partial-permutation tables

Exercises `Commons.Schemes.Sponge.Table`: capacity collision-freeness under fresh and duplicate
insertions, orthogonal digest injectivity, query constraint equivalence, absorption locality, and
rooted-path uniqueness.
-/

@[expose] public section

namespace SpongeTableTests

open Commons.Sponge

/-- Appending a forward edge, an inverse edge, and a duplicate-input replay via `insertEdge`
preserves `CapacityCollisionFree`. -/
lemma capacityCollisionFree_insertEdge_contract :
    let e1 : PermutationEdge (Fin 4) := ⟨0, 1, false⟩
    let e2 : PermutationEdge (Fin 4) := ⟨2, 3, true⟩
    let eDup : PermutationEdge (Fin 4) := ⟨0, 1, true⟩
    let t1 := insertEdge ([] : List (PermutationEdge (Fin 4))) e1
    let t2 := insertEdge t1 e2
    let t3 := insertEdge t2 eDup
    CapacityCollisionFree (id : Fin 4 → Fin 4) (0 : Fin 4) t3 := by
  intro e1 e2 eDup t1 t2 t3
  have h0 : CapacityCollisionFree (id : Fin 4 → Fin 4) 0 ([] : List (PermutationEdge (Fin 4))) :=
    capacityCollisionFree_nil id 0
  have h1 : CapacityCollisionFree (id : Fin 4 → Fin 4) 0 t1 := by
    apply capacityCollisionFree_insertEdge id 0 [] h0 e1
    intro _
    simp only [AvoidsOccupiedCapacity, PermutationEdge.freshEndpoint, occupiedCapacities,
      List.map_nil, List.toFinset_nil, Finset.union_empty, Finset.mem_insert,
      Finset.notMem_empty, or_false, Bool.false_eq_true, ↓reduceIte, id_eq, e1]
    intro h
    have hv : (1 : Nat) = 0 := congrArg Fin.val h
    omega
  have h2 : CapacityCollisionFree (id : Fin 4 → Fin 4) 0 t2 := by
    apply capacityCollisionFree_insertEdge id 0 t1 h1 e2
    intro _
    simp only [AvoidsOccupiedCapacity, PermutationEdge.freshEndpoint, occupiedCapacities,
      t1, insertEdge, List.not_mem_nil, false_and, exists_false, ↓reduceIte, List.nil_append,
      List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil, Finset.mem_insert,
      Finset.mem_union, Finset.notMem_empty, or_false, id_eq, e1, e2]
    rintro (h | h | h)
    · have hv : (2 : Nat) = 0 := congrArg Fin.val h
      omega
    · have hv : (2 : Nat) = 0 := congrArg Fin.val h
      omega
    · have hv : (2 : Nat) = 1 := congrArg Fin.val h
      omega
  apply capacityCollisionFree_insertEdge id 0 t2 h2 eDup
  intro hfresh
  have hmem : e1 ∈ t2 :=
    insertEdge_subset t1 e2 e1
      (by simp only [t1, insertEdge, List.not_mem_nil, false_and, exists_false, ↓reduceIte,
        List.nil_append, List.mem_singleton])
  exact False.elim (hfresh e1 hmem rfl)

/-- After a forward query at `x`, an inverse query at `π x` returns along the same edge.
The table keeps one entry with its original forward direction. -/
example {State : Type*} [DecidableEq State] (π : Equiv.Perm State) (x : State) :
    let forward := queryEdge π false x
    insertEdge [forward] (queryEdge π true (π x)) = [forward] := by
  intro forward
  apply insertEdge_eq_self_of_input_mem (List.mem_singleton_self forward)
  exact (π.symm_apply_apply x).symm

/-- Orthogonal digest injectivity is preserved by `digest_injOn_insertEdge`. -/
lemma digest_injOn_insertEdge_contract :
    let e1 : PermutationEdge (Fin 4) := ⟨0, 1, false⟩
    let e2 : PermutationEdge (Fin 4) := ⟨2, 3, true⟩
    let t1 := insertEdge ([] : List (PermutationEdge (Fin 4))) e1
    let t2 := insertEdge t1 e2
    Set.InjOn (id : Fin 4 → Fin 4) (forwardOutputs t2) := by
  intro e1 e2 t1 t2
  have h0 : Set.InjOn (id : Fin 4 → Fin 4)
      (forwardOutputs ([] : List (PermutationEdge (Fin 4)))) := by
    rw [forwardOutputs_nil]
    exact Set.injOn_empty _
  have h1 : Set.InjOn (id : Fin 4 → Fin 4) (forwardOutputs t1) := by
    apply digest_injOn_insertEdge id [] h0 e1
    intro _ _ s hs
    rw [forwardOutputs_nil] at hs
    cases hs
  apply digest_injOn_insertEdge id t1 h1 e2
  intro _ hinv
  exact Bool.noConfusion hinv

/-- Inserting a forward and inverse query of `π` constrains `ρ` to match `π` on both queries. -/
lemma insertEdge_query_contract {State : Type*} [DecidableEq State]
    (π ρ : Equiv.Perm State) (x y : State) :
    let t1 := insertEdge ([] : List (PermutationEdge State)) (queryEdge π false x)
    let t2 := insertEdge t1 (queryEdge π true y)
    (∀ pair ∈ recordedPairs t2, ρ pair.1 = pair.2) ↔
      ρ x = π x ∧ ρ.symm y = π.symm y := by
  intro t1 t2
  have h0 : AgreesWith ([] : List (PermutationEdge State)) π := fun _ h => by cases h
  have h1 : AgreesWith t1 π :=
    insertEdge_agrees [] (queryEdge π false x) π h0 (queryEdge_agrees π false x)
  rw [← recordedPairs_agrees_iff]
  rw [insertEdge_query_agrees_iff t1 π h1 true y ρ]
  rw [insertEdge_query_agrees_iff [] π h0 false x ρ]
  simp only [↓reduceIte, Bool.false_eq_true]
  constructor
  · rintro ⟨⟨_, hx⟩, hy⟩
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨(fun _ h => by cases h), hx⟩, hy⟩

/-- Any permutation agreeing with `recordAbsorption` computes the same final state. -/
lemma recordAbsorption_local_contract {State Block : Type*} [DecidableEq State]
    (absorb : State → Block → State) (π ρ : Equiv.Perm State)
    (state : State) (blocks : List Block)
    (hρ : AgreesWith (recordAbsorption absorb π [] state blocks) ρ) :
    absorbBlocks absorb ρ state blocks = absorbBlocks absorb π state blocks := by
  have hπ : AgreesWith (recordAbsorption absorb π [] state blocks) π :=
    recordAbsorption_agrees absorb π [] (fun _ h => by cases h) state blocks
  exact (recordAbsorption_local absorb π ρ [] state blocks hπ hρ).2

/-- On a product state `Rate × Cap` with XOR absorption on the rate coordinate, two covered rooted
paths reaching the same state must have identical block sequences. -/
lemma blocks_eq_product_state_contract
    (table : List (PermutationEdge (BitVec 8 × BitVec 8)))
    (hg : CapacityCollisionFree Prod.snd (0 : BitVec 8) table)
    (π : Equiv.Perm (BitVec 8 × BitVec 8)) (ha : AgreesWith table π)
    (first second : List (BitVec 8))
    (hf : ∀ x ∈ absorptionCalls (fun s b => (s.1 ^^^ b, s.2)) π (0, 0) first,
      ∃ edge ∈ table, edge.input = x)
    (hs : ∀ x ∈ absorptionCalls (fun s b => (s.1 ^^^ b, s.2)) π (0, 0) second,
      ∃ edge ∈ table, edge.input = x)
    (he : absorbBlocks (fun s b => (s.1 ^^^ b, s.2)) π (0, 0) first =
      absorbBlocks (fun s b => (s.1 ^^^ b, s.2)) π (0, 0) second) :
    first = second := by
  refine blocks_eq_of_absorbBlocks_eq Prod.snd 0 (fun s b => (s.1 ^^^ b, s.2))
    (fun _ _ => rfl) ?_ (0, 0) rfl table hg π ha first second hf hs he
  intro s a b h
  have h1 : s.1 ^^^ a = s.1 ^^^ b := congrArg Prod.fst h
  have hcancel := congrArg (fun x => s.1 ^^^ x) h1
  simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using hcancel

/-! ## Axiom audit of key exported theorems -/

#print axioms Commons.Sponge.rooted_edge_forward
#print axioms Commons.Sponge.capacityCollisionFree_append
#print axioms Commons.Sponge.capacityCollisionFree_insertEdge
#print axioms Commons.Sponge.digest_injOn_append
#print axioms Commons.Sponge.digest_injOn_insertEdge
#print axioms Commons.Sponge.insertEdge_agrees_iff
#print axioms Commons.Sponge.insertEdge_query_agrees_iff
#print axioms Commons.Sponge.recordedPairs_agrees_iff
#print axioms Commons.Sponge.recordAbsorption_local
#print axioms Commons.Sponge.blocks_eq_of_absorbBlocks_eq

end SpongeTableTests
