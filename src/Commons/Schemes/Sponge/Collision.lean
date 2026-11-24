module

public import Commons.Definitions.PermutationTableGame
public import Commons.Schemes.Sponge.Basic
public import Mathlib.Data.BitVec

/-!
# Adaptive collision resistance of the generic sponge construction

Adaptive security bounds for the byte-oriented sponge over a bidirectional ideal permutation
`StrongURP (ByteState p.stateBytes) q` [1, §4], [2, §4.3], built on the generic
`StrongURP.tableMonitorGame` framework (`Commons.Definitions.PermutationTableGame`):

* **Tight capacity set (`freshCapacities`)**: only `zeroCap` and the freshly sampled endpoint of
  each recorded edge can cause a capacity collision, shrinking the forbidden-capacity set from
  `2 |table| + 1` to `|table| + 1` and matching the `C(q + 1, 2) / |C|` constant [2, §4.3].
* **Adaptive capacity collision game (`capacityCollisionGame`)**: monitors
  `CapacityCollisionFree` on `StrongURP`; every winner succeeds with probability at most
  `(|S| / (|S| - q)) · C(q + 1, 2) / |C|` (`capacityCollisionGame_win_le`).
* **Combined sponge collision game (`spongeCollisionGame`)**: monitors both
  `CapacityCollisionFree` and forward digest injectivity on `StrongURP`; every winner succeeds
  with probability at most `(|S| / (|S| - q)) · (C(q + 1, 2) / |C| + C(q, 2) / |O|)`
  (`spongeCollisionGame_win_le`), and unset transcripts preclude `spongeHash` collisions on all
  covered inputs (`spongeCollisionGame_unset_no_collision`).

## References

1. National Institute of Standards and Technology. *SHA-3 Standard: Permutation-Based Hash and
   Extendable-Output Functions*. FIPS PUB 202, August 2015.
2. G. Bertoni, J. Daemen, M. Peeters, and G. Van Assche. *On the Indifferentiability of the
   Sponge Construction*. EUROCRYPT 2008, LNCS 4965, pp. 181–197.
3. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Commons.Sponge

open CategoryTheory SystemAlgebra Probability Probability.Distribution Probability.Counting
open Commons.StrongURP
open scoped BigOperators NNReal SystemAlgebra

/-! ### Tight fresh-capacity set -/

section FreshCapacities

variable {State Cap : Type*}

/-- Capacities taken by `zeroCap` or the freshly sampled endpoint of any recorded edge. -/
def freshCapacities [DecidableEq Cap]
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) : Finset Cap :=
  insert zeroCap (table.map fun edge => capacity edge.freshEndpoint).toFinset

lemma freshCapacities_zero [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap) (table : List (PermutationEdge State)) :
    zeroCap ∈ freshCapacities capacity zeroCap table :=
  Finset.mem_insert_self _ _

lemma freshCapacities_fresh [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap) (table : List (PermutationEdge State))
    {edge : PermutationEdge State} (he : edge ∈ table) :
    capacity edge.freshEndpoint ∈ freshCapacities capacity zeroCap table :=
  Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map.mpr ⟨edge, he, rfl⟩))

/-- The fresh capacity set has cardinality at most `table.length + 1`. -/
lemma freshCapacities_card_le [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap) (table : List (PermutationEdge State)) :
    (freshCapacities capacity zeroCap table).card ≤ table.length + 1 := by
  have hm : (table.map fun edge => capacity edge.freshEndpoint).toFinset.card ≤ table.length :=
    (List.toFinset_card_le _).trans (by simp only [List.length_map, le_rfl])
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hm 1)

/-- Avoiding `freshCapacities` on the newly sampled endpoint suffices to preserve
`CapacityCollisionFree` when appending an edge. -/
theorem capacityCollisionFree_append_of_fresh [DecidableEq Cap]
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table)
    (edge : PermutationEdge State)
    (hf : capacity edge.freshEndpoint ∉ freshCapacities capacity zeroCap table) :
    CapacityCollisionFree capacity zeroCap (table ++ [edge]) := by
  have hfor_mem {s : State} (hs : s ∈ forwardOutputs table) :
      capacity s ∈ freshCapacities capacity zeroCap table := by
    obtain ⟨e, hm, hinv, rfl⟩ := hs
    have hfresh : e.freshEndpoint = e.output := by
      simp only [PermutationEdge.freshEndpoint, hinv, Bool.false_eq_true, ↓reduceIte]
    rw [← hfresh]
    exact freshCapacities_fresh capacity zeroCap table hm
  have hinv_mem {x : State} (hx : x ∈ inverseInputs table) :
      capacity x ∈ freshCapacities capacity zeroCap table := by
    obtain ⟨e, hm, hinv, rfl⟩ := hx
    have hfresh : e.freshEndpoint = e.input := by
      simp only [PermutationEdge.freshEndpoint, hinv, ↓reduceIte]
    rw [← hfresh]
    exact freshCapacities_fresh capacity zeroCap table hm
  cases hi : edge.inverse with
  | false =>
    have hcap : capacity edge.output ∉ freshCapacities capacity zeroCap table := by
      simpa only [PermutationEdge.freshEndpoint, hi, Bool.false_eq_true, ↓reduceIte] using hf
    have hfor := forwardOutputs_append_singleton table edge
    have hinv := inverseInputs_append_singleton table edge
    simp only [hi, ↓reduceIte, Bool.false_eq_true] at hfor hinv
    rw [CapacityCollisionFree, hfor, hinv]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb he
      rcases Set.mem_insert_iff.mp ha with rfl | haOld
      · rcases Set.mem_insert_iff.mp hb with rfl | hbOld
        · rfl
        · exact False.elim (hcap (he ▸ hfor_mem hbOld))
      · rcases Set.mem_insert_iff.mp hb with rfl | hbOld
        · exact False.elim (hcap (he.symm ▸ hfor_mem haOld))
        · exact hg.1 haOld hbOld he
    · intro s hs
      rcases Set.mem_insert_iff.mp hs with rfl | hsOld
      · intro hz
        exact hcap (hz ▸ freshCapacities_zero capacity zeroCap table)
      · exact hg.2.1 s hsOld
    · intro x hx
      refine ⟨(hg.2.2 x hx).1, ?_⟩
      intro s hs
      rcases Set.mem_insert_iff.mp hs with rfl | hsOld
      · intro he
        exact hcap (he.symm ▸ hinv_mem hx)
      · exact (hg.2.2 x hx).2 s hsOld
  | true =>
    have hcap : capacity edge.input ∉ freshCapacities capacity zeroCap table := by
      simpa only [PermutationEdge.freshEndpoint, hi, ↓reduceIte] using hf
    have hfor := forwardOutputs_append_singleton table edge
    have hinv := inverseInputs_append_singleton table edge
    simp only [hi, ↓reduceIte, Bool.true_eq_false] at hfor hinv
    rw [CapacityCollisionFree, hfor, hinv]
    refine ⟨hg.1, hg.2.1, ?_⟩
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hxOld
    · refine ⟨fun hz => hcap (hz ▸ freshCapacities_zero capacity zeroCap table), ?_⟩
      intro s hs he
      exact hcap (he ▸ hfor_mem hs)
    · exact hg.2.2 x hxOld

/-- Inserting an edge preserves `CapacityCollisionFree` whenever a non-duplicate edge avoids
`freshCapacities`. -/
theorem capacityCollisionFree_insertEdge_of_fresh [DecidableEq State] [DecidableEq Cap]
    -- `capacity` extracts the inner state; `zeroCap` is the initial capacity.
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) (hg : CapacityCollisionFree capacity zeroCap table)
    (edge : PermutationEdge State)
    -- Only newly inserted (non-duplicate) edges must avoid `freshCapacities`.
    (hf : (∀ prev ∈ table, prev.input ≠ edge.input) →
      capacity edge.freshEndpoint ∉ freshCapacities capacity zeroCap table) :
    CapacityCollisionFree capacity zeroCap (insertEdge table edge) := by
  unfold insertEdge
  split_ifs with hdup
  · exact hg
  · exact capacityCollisionFree_append_of_fresh capacity zeroCap table hg edge
      (hf (fun prev hp he => hdup ⟨prev, hp, he⟩))

/-- `CapacityCollisionFree` is downward-closed under edge-list inclusion. -/
lemma capacityCollisionFree_of_subset
    (capacity : State → Cap) (zeroCap : Cap)
    {t₁ t₂ : List (PermutationEdge State)} (hsub : ∀ e ∈ t₁, e ∈ t₂)
    (hg : CapacityCollisionFree capacity zeroCap t₂) :
    CapacityCollisionFree capacity zeroCap t₁ := by
  have hfor : forwardOutputs t₁ ⊆ forwardOutputs t₂ := by
    rintro s ⟨e, hm, hinv, rfl⟩
    exact ⟨e, hsub e hm, hinv, rfl⟩
  have hinv : inverseInputs t₁ ⊆ inverseInputs t₂ := by
    rintro x ⟨e, hm, hdir, rfl⟩
    exact ⟨e, hsub e hm, hdir, rfl⟩
  exact ⟨hg.1.mono hfor, fun s hs => hg.2.1 s (hfor hs),
    fun x hx => ⟨(hg.2.2 x (hinv hx)).1, fun s hs => (hg.2.2 x (hinv hx)).2 s (hfor hs)⟩⟩

/-- Forward digest injectivity is downward-closed under edge-list inclusion. -/
lemma digest_injOn_of_subset {Out : Type*} (digest : State → Out)
    {t₁ t₂ : List (PermutationEdge State)} (hsub : ∀ e ∈ t₁, e ∈ t₂)
    (hdig : Set.InjOn digest (forwardOutputs t₂)) :
    Set.InjOn digest (forwardOutputs t₁) := by
  refine hdig.mono ?_
  rintro s ⟨e, hm, hinv, rfl⟩
  exact ⟨e, hsub e hm, hinv, rfl⟩

end FreshCapacities

/-! ### Finite byte states and uniform projections -/

section ByteStateUniform

/-- `BitVec 8` is finite via `BitVec.equivFin`, giving `Fintype (ByteState n)`. -/
instance instFintypeByte : Fintype (BitVec 8) :=
  Fintype.ofEquiv (Fin (2 ^ 8)) BitVec.equivFin.toEquiv.symm

lemma card_byteState (n : ℕ) : Fintype.card (ByteState n) = 256 ^ n := by
  rw [Fintype.card_fun, Fintype.card_fin]
  have hb : Fintype.card (BitVec 8) = 256 := by
    rw [Fintype.card_congr BitVec.equivFin.toEquiv, Fintype.card_fin]
    norm_num
  rw [hb]

/-- Projecting a uniform state onto its capacity bytes yields the uniform capacity law. -/
lemma fTransform_capacityPart_uniform (p : Parameters) (hr : p.rateBytes ≤ p.stateBytes) :
    Distribution.fTransform (capacityPart p) (Distribution.uniform (ByteState p.stateBytes)) =
      Distribution.uniform (ByteState p.capacityBytes) := by
  let idx : Fin p.capacityBytes → Fin p.stateBytes := fun i =>
    ⟨p.rateBytes + i.val, by
      have hi := i.isLt
      simp only [Parameters.capacityBytes] at hi
      omega⟩
  have hinj : Function.Injective idx := by
    intro a b h
    have hv : p.rateBytes + a.val = p.rateBytes + b.val := congrArg Fin.val h
    exact Fin.ext (by omega)
  have hfun : capacityPart p = fun s i => s (idx i) := by
    funext s i
    have hlt : p.rateBytes + i.val < p.stateBytes := by
      have hi := i.isLt
      simp only [Parameters.capacityBytes] at hi
      omega
    simp only [capacityPart, idx, hlt, ↓reduceDIte]
  rw [hfun]
  exact Counting.fTransform_eval_uniform_eq_uniform idx hinj

/-- Projecting a uniform state onto its digest bytes yields the uniform digest law. -/
lemma fTransform_digestPart_uniform (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes) :
    Distribution.fTransform (digestPart p) (Distribution.uniform (ByteState p.stateBytes)) =
      Distribution.uniform (ByteState p.outputBytes) := by
  let idx : Fin p.outputBytes → Fin p.stateBytes := fun i =>
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt ho⟩
  have hinj : Function.Injective idx := by
    intro a b h
    have hv : (idx a).val = (idx b).val := congrArg Fin.val h
    exact Fin.ext hv
  have hfun : digestPart p = fun s i => s (idx i) := by
    funext s i
    have hlt : i.val < p.stateBytes := Nat.lt_of_lt_of_le i.isLt ho
    simp only [digestPart, idx, hlt, ↓reduceDIte]
  rw [hfun]
  exact Counting.fTransform_eval_uniform_eq_uniform idx hinj

open Classical in
/-- Probability that a uniform full state has capacity in `F`. -/
lemma uniform_mass_capacityPart_mem (p : Parameters) (hr : p.rateBytes ≤ p.stateBytes)
    (F : Finset (ByteState p.capacityBytes)) :
    (Distribution.uniform (ByteState p.stateBytes)).mass (fun s => capacityPart p s ∈ F) =
      (F.card : ℝ) / Fintype.card (ByteState p.capacityBytes) := by
  classical
  have hm := Distribution.mass_fTransform (capacityPart p)
    (Distribution.uniform (ByteState p.stateBytes)) (fun c => c ∈ F)
  rw [fTransform_capacityPart_uniform p hr, Distribution.uniform_mass_eq_card_filter] at hm
  rw [← hm, Finset.filter_mem_eq_inter, Finset.univ_inter]

open Classical in
/-- Probability that a uniform full state has digest in `D`. -/
lemma uniform_mass_digestPart_mem (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes)
    (D : Finset (ByteState p.outputBytes)) :
    (Distribution.uniform (ByteState p.stateBytes)).mass (fun s => digestPart p s ∈ D) =
      (D.card : ℝ) / Fintype.card (ByteState p.outputBytes) := by
  classical
  have hm := Distribution.mass_fTransform (digestPart p)
    (Distribution.uniform (ByteState p.stateBytes)) (fun d => d ∈ D)
  rw [fTransform_digestPart_uniform p ho, Distribution.uniform_mass_eq_card_filter] at hm
  rw [← hm, Finset.filter_mem_eq_inter, Finset.univ_inter]

end ByteStateUniform

/-! ### Part A: Reusable adaptive capacity-collision game on `StrongURP` -/

section CapacityCollisionGame

noncomputable section

/-- Adaptive game on `StrongURP (ByteState p.stateBytes) q` setting the MBO when
`CapacityCollisionFree` fails on the directed query history table [2, §4.3]. -/
def capacityCollisionGame (p : Parameters) (q : ℕ) :
    TypedGame (Bidirectional (ByteState p.stateBytes) q) :=
  tableMonitorGame q (CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes))
    (fun hsub hg => capacityCollisionFree_of_subset _ _ hsub hg)

/-- Hiding the MBO of `capacityCollisionGame` gives `StrongURP (ByteState p.stateBytes)`. -/
lemma capacityCollisionGame_visible (p : Parameters) (q : ℕ) :
    (capacityCollisionGame p q).visible = StrongURP (ByteState p.stateBytes) (q := q) :=
  tableMonitorGame_visible q _ (fun hsub hg => capacityCollisionFree_of_subset _ _ hsub hg)

/-- Tight adaptive capacity-collision upper bound `(|S| / (|S| - q)) · C(q + 1, 2) / |C|`. -/
def capacityCollisionBound (p : Parameters) (q : ℕ) : ℝ :=
  ((Fintype.card (ByteState p.stateBytes) : ℝ) /
      (Fintype.card (ByteState p.stateBytes) - q : ℝ)) *
    (((q + 1).choose 2 : ℝ) / Fintype.card (ByteState p.capacityBytes))

open Classical in
/-- Every compatible stopping distinguisher wins `capacityCollisionGame p q` with probability at
most `(|S| / (|S| - q)) · C(q + 1, 2) / |C|`. -/
lemma capacityCollisionGame_winProbability_le (p : Parameters) (hp : p.Valid) (q : ℕ)
    (hq : q < Fintype.card (ByteState p.stateBytes))
    (P : (Bidirectional (ByteState p.stateBytes) q).inputDomain.Distinguisher) :
    P.winProbability (capacityCollisionGame p q).1.1 ≤ capacityCollisionBound p q := by
  classical
  have hlin := tableMonitorGame_winProbability_le_of_linear q hq
    (CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes))
    (capacityCollisionFree_nil _ _)
    (fun hsub hg => capacityCollisionFree_of_subset _ _ hsub hg)
    (1 / Fintype.card (ByteState p.capacityBytes) : ℝ) 0
    (div_nonneg zero_le_one (Nat.cast_nonneg _)) le_rfl
    (by
      intro table _ hg
      refine ⟨fun s => capacityPart p s ∈
        freshCapacities (capacityPart p) (zeroState p.capacityBytes) table, ?_, ?_⟩
      · intro edge _ hng
        by_contra hnot
        exact hng (capacityCollisionFree_append_of_fresh _ _ table hg edge hnot)
      · rw [uniform_mass_capacityPart_mem p (Nat.le_of_lt hp.2.1), zero_mul, add_zero,
          one_div_mul_eq_div]
        have hcard :
            ((freshCapacities (capacityPart p) (zeroState p.capacityBytes) table).card : ℝ) ≤
              (table.length : ℝ) + 1 := by
          exact_mod_cast
            freshCapacities_card_le (capacityPart p) (zeroState p.capacityBytes) table
        exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _))
    P
  refine hlin.trans (le_of_eq ?_)
  dsimp only [capacityCollisionBound]
  ring

/-- Every admitted winner on `Bidirectional (ByteState p.stateBytes) q` breaks
`CapacityCollisionFree` with probability at most `(|S| / (|S| - q)) · C(q + 1, 2) / |C|`
[2, §4.3]. -/
theorem capacityCollisionGame_win_le (p : Parameters) (hp : p.Valid) (q : ℕ)
    (hq : q < Fintype.card (ByteState p.stateBytes))
    {winner : TypedGame (Bidirectional (ByteState p.stateBytes) q) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners
      (Bidirectional (ByteState p.stateBytes) q)) :
    winner (capacityCollisionGame p q) ≤ capacityCollisionBound p q :=
  Interface.win_le (capacityCollisionGame_winProbability_le p hp q hq) hw

/-- Any system conditionally equivalent to `capacityCollisionGame p q` is within
`capacityCollisionBound p q` of `StrongURP (ByteState p.stateBytes)` [3, Theorem 4.17]. -/
theorem capacityCollisionGame_dist_le (p : Parameters) (hp : p.Valid) (q : ℕ)
    (hq : q < Fintype.card (ByteState p.stateBytes))
    {T : TypedSystem (Bidirectional (ByteState p.stateBytes) q)}
    (hc : capacityCollisionGame p q |≡ T) :
    Δ (StrongURP (ByteState p.stateBytes) (q := q)) T ≤
      ENNReal.ofReal (capacityCollisionBound p q) := by
  rw [← capacityCollisionGame_visible p q]
  exact dist_visible_le_of_winProbability_le hc
    (capacityCollisionGame_winProbability_le p hp q hq)

end

end CapacityCollisionGame

/-! ### Part B: Combined sponge collision game and `spongeHash` collision resistance -/

section SpongeCollisionGame

noncomputable section

/-- Distinct digests of forward-created outputs recorded in `table`. -/
def forwardDigests (p : Parameters)
    (table : List (PermutationEdge (ByteState p.stateBytes))) :
    Finset (ByteState p.outputBytes) :=
  ((table.filter fun e => !e.inverse).map fun e => digestPart p e.output).toFinset

lemma forwardDigests_card_le (p : Parameters)
    (table : List (PermutationEdge (ByteState p.stateBytes))) :
    (forwardDigests p table).card ≤ table.length := by
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map]
  exact List.length_filter_le _ _

lemma digest_mem_forwardDigests {p : Parameters}
    {table : List (PermutationEdge (ByteState p.stateBytes))}
    {s : ByteState p.stateBytes} (hs : s ∈ forwardOutputs table) :
    digestPart p s ∈ forwardDigests p table := by
  obtain ⟨e, hm, hinv, rfl⟩ := hs
  refine List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, ?_, rfl⟩)
  exact List.mem_filter.mpr ⟨hm, by simp only [hinv, Bool.not_false]⟩

/-- Adaptive game on `StrongURP (ByteState p.stateBytes) q` setting the MBO when either
`CapacityCollisionFree` or forward digest injectivity fails [2, §4.3]. -/
def spongeCollisionGame (p : Parameters) (q : ℕ) :
    TypedGame (Bidirectional (ByteState p.stateBytes) q) :=
  tableMonitorGame q
    (fun table => CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table ∧
      Set.InjOn (digestPart p) (forwardOutputs table))
    (fun hsub ⟨hg, hdig⟩ =>
      ⟨capacityCollisionFree_of_subset _ _ hsub hg, digest_injOn_of_subset _ hsub hdig⟩)

/-- Hiding the MBO of `spongeCollisionGame` gives `StrongURP (ByteState p.stateBytes)`. -/
lemma spongeCollisionGame_visible (p : Parameters) (q : ℕ) :
    (spongeCollisionGame p q).visible = StrongURP (ByteState p.stateBytes) (q := q) :=
  tableMonitorGame_visible q _
    (fun hsub ⟨hg, hdig⟩ =>
      ⟨capacityCollisionFree_of_subset _ _ hsub hg, digest_injOn_of_subset _ hsub hdig⟩)

/-- Tight adaptive sponge collision upper bound
`(|S| / (|S| - q)) · (C(q + 1, 2) / |C| + C(q, 2) / |O|)`. -/
def spongeCollisionBound (p : Parameters) (q : ℕ) : ℝ :=
  ((Fintype.card (ByteState p.stateBytes) : ℝ) /
      (Fintype.card (ByteState p.stateBytes) - q : ℝ)) *
    (((q + 1).choose 2 : ℝ) / Fintype.card (ByteState p.capacityBytes) +
      (q.choose 2 : ℝ) / Fintype.card (ByteState p.outputBytes))

open Classical in
/-- Every compatible stopping distinguisher wins `spongeCollisionGame p q` with probability at
most `(|S| / (|S| - q)) · (C(q + 1, 2) / |C| + C(q, 2) / |O|)`. -/
lemma spongeCollisionGame_winProbability_le (p : Parameters) (hp : p.Valid) (q : ℕ)
    (hq : q < Fintype.card (ByteState p.stateBytes))
    (P : (Bidirectional (ByteState p.stateBytes) q).inputDomain.Distinguisher) :
    P.winProbability (spongeCollisionGame p q).1.1 ≤ spongeCollisionBound p q := by
  classical
  have ho_le : p.outputBytes ≤ p.stateBytes := hp.2.2.2.1.trans (Nat.le_of_lt hp.2.1)
  have hnil :
      CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) [] ∧
        Set.InjOn (digestPart p) (forwardOutputs []) := by
    refine ⟨capacityCollisionFree_nil _ _, ?_⟩
    rw [forwardOutputs_nil]
    exact Set.injOn_empty _
  have hlin := tableMonitorGame_winProbability_le_of_linear q hq
    (fun table => CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table ∧
      Set.InjOn (digestPart p) (forwardOutputs table))
    hnil
    (fun hsub ⟨hg, hdig⟩ =>
      ⟨capacityCollisionFree_of_subset _ _ hsub hg, digest_injOn_of_subset _ hsub hdig⟩)
    (1 / Fintype.card (ByteState p.capacityBytes) : ℝ)
    (1 / Fintype.card (ByteState p.outputBytes) : ℝ)
    (div_nonneg zero_le_one (Nat.cast_nonneg _))
    (div_nonneg zero_le_one (Nat.cast_nonneg _))
    (by
      intro table inverse ⟨hg, hdig⟩
      have hcapCard :
          ((freshCapacities (capacityPart p) (zeroState p.capacityBytes) table).card : ℝ) ≤
            (table.length : ℝ) + 1 := by
        exact_mod_cast
          freshCapacities_card_le (capacityPart p) (zeroState p.capacityBytes) table
      cases inverse with
      | false =>
        refine ⟨fun s =>
          capacityPart p s ∈ freshCapacities (capacityPart p) (zeroState p.capacityBytes) table ∨
            digestPart p s ∈ forwardDigests p table, ?_, ?_⟩
        · intro edge hinv hng
          by_contra hnot
          push Not at hnot
          obtain ⟨hcapFresh, hdigFresh⟩ := hnot
          have hg' := capacityCollisionFree_append_of_fresh _ _ table hg edge hcapFresh
          have hdig' : Set.InjOn (digestPart p) (forwardOutputs (table ++ [edge])) := by
            apply digest_injOn_append (digestPart p) table hdig edge
            intro _ s hs he
            have hfe : edge.freshEndpoint = edge.output := by
              simp only [PermutationEdge.freshEndpoint, hinv, Bool.false_eq_true, ↓reduceIte]
            rw [hfe] at hdigFresh
            exact hdigFresh (he ▸ digest_mem_forwardDigests hs)
          exact hng ⟨hg', hdig'⟩
        · refine (Distribution.mass_or_le Distribution.uniform_nonNeg _ _).trans ?_
          rw [uniform_mass_capacityPart_mem p (Nat.le_of_lt hp.2.1),
            uniform_mass_digestPart_mem p ho_le, one_div_mul_eq_div, one_div_mul_eq_div]
          have hdigCard : ((forwardDigests p table).card : ℝ) ≤ (table.length : ℝ) := by
            exact_mod_cast forwardDigests_card_le p table
          exact add_le_add
            (div_le_div_of_nonneg_right hcapCard (Nat.cast_nonneg _))
            (div_le_div_of_nonneg_right hdigCard (Nat.cast_nonneg _))
      | true =>
        refine ⟨fun s =>
          capacityPart p s ∈ freshCapacities (capacityPart p) (zeroState p.capacityBytes) table,
          ?_, ?_⟩
        · intro edge hinv hng
          by_contra hnot
          have hg' := capacityCollisionFree_append_of_fresh _ _ table hg edge hnot
          have hdig' : Set.InjOn (digestPart p) (forwardOutputs (table ++ [edge])) := by
            apply digest_injOn_append (digestPart p) table hdig edge
            intro hf
            exact Bool.noConfusion (hinv.symm.trans hf)
          exact hng ⟨hg', hdig'⟩
        · rw [uniform_mass_capacityPart_mem p (Nat.le_of_lt hp.2.1), one_div_mul_eq_div,
            one_div_mul_eq_div]
          refine (div_le_div_of_nonneg_right hcapCard (Nat.cast_nonneg _)).trans ?_
          exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    P
  refine hlin.trans (le_of_eq ?_)
  dsimp only [spongeCollisionBound]
  ring

/-- Every admitted winner on `Bidirectional (ByteState p.stateBytes) q` triggers a capacity or
digest collision with probability at most
`(|S| / (|S| - q)) · (C(q + 1, 2) / |C| + C(q, 2) / |O|)` [2, §4.3]. -/
theorem spongeCollisionGame_win_le (p : Parameters) (hp : p.Valid) (q : ℕ)
    (hq : q < Fintype.card (ByteState p.stateBytes))
    {winner : TypedGame (Bidirectional (ByteState p.stateBytes) q) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners
      (Bidirectional (ByteState p.stateBytes) q)) :
    winner (spongeCollisionGame p q) ≤ spongeCollisionBound p q :=
  Interface.win_le (spongeCollisionGame_winProbability_le p hp q hq) hw

open Classical in
/-- On any unset transcript of `spongeCollisionGame p q`, no two distinct covered inputs can
collide under `spongeHash p π` [1, §4], [2, §4.3]. -/
theorem spongeCollisionGame_unset_no_collision (p : Parameters) (hp : p.Valid) (q : ℕ)
    (h : List ((Σ i, (Bidirectional (ByteState p.stateBytes) q).X i) ×
      Σ i, (Bidirectional (ByteState p.stateBytes) q).Y i))
    (hunset : (spongeCollisionGame p q).1.1 (unsetMBOs h) ≠ 0)
    (π : Equiv.Perm (ByteState p.stateBytes))
    (ha : AgreesWith (transcriptTable q h) π)
    (first second : List (BitVec 8))
    (hf : ∀ x ∈ spongeCalls p π first, ∃ edge ∈ transcriptTable q h, edge.input = x)
    (hs : ∀ x ∈ spongeCalls p π second, ∃ edge ∈ transcriptTable q h, edge.input = x)
    (he : spongeHash p π first = spongeHash p π second) :
    first = second := by
  have hnil :
      CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) [] ∧
        Set.InjOn (digestPart p) (forwardOutputs []) := by
    refine ⟨capacityCollisionFree_nil _ _, ?_⟩
    rw [forwardOutputs_nil]
    exact Set.injOn_empty _
  have hgood :
      CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) (transcriptTable q h) ∧
        Set.InjOn (digestPart p) (forwardOutputs (transcriptTable q h)) := by
    by_contra hng
    apply hunset
    rw [spongeCollisionGame,
      tableMonitorGame_unsetMBOs_eq q _ hnil
        (fun hsub ⟨hg, hdig⟩ =>
          ⟨capacityCollisionFree_of_subset _ _ hsub hg, digest_injOn_of_subset _ hsub hdig⟩)
        h,
      ite_eq_right hng]
  exact input_eq_of_spongeHash_eq p hp (transcriptTable q h) hgood.1 hgood.2 π ha first second
    hf hs he

/-- Any system conditionally equivalent to `spongeCollisionGame p q` is within
`spongeCollisionBound p q` of `StrongURP (ByteState p.stateBytes)` [3, Theorem 4.17]. -/
theorem spongeCollisionGame_dist_le (p : Parameters) (hp : p.Valid) (q : ℕ)
    (hq : q < Fintype.card (ByteState p.stateBytes))
    {T : TypedSystem (Bidirectional (ByteState p.stateBytes) q)}
    (hc : spongeCollisionGame p q |≡ T) :
    Δ (StrongURP (ByteState p.stateBytes) (q := q)) T ≤
      ENNReal.ofReal (spongeCollisionBound p q) := by
  rw [← spongeCollisionGame_visible p q]
  exact dist_visible_le_of_winProbability_le hc (spongeCollisionGame_winProbability_le p hp q hq)

/-- Attaching any converter `α` preserves the sponge collision distance bound. -/
theorem spongeCollisionGame_attach_dist_le (p : Parameters) (hp : p.Valid) (q : ℕ)
    (hq : q < Fintype.card (ByteState p.stateBytes))
    {A : Interface} (α : A ⟶ Bidirectional (ByteState p.stateBytes) q)
    {T : TypedSystem (Bidirectional (ByteState p.stateBytes) q)}
    (hc : spongeCollisionGame p q |≡ T) :
    Δ (α • StrongURP (ByteState p.stateBytes) (q := q)) (α • T) ≤
      ENNReal.ofReal (spongeCollisionBound p q) :=
  (ConstructiveCryptography.CryptographicAlgebra.distance_attach_le α _ _).trans
    (spongeCollisionGame_dist_le p hp q hq hc)

/-- Any system conditionally equivalent to `spongeCollisionGame p q` substitutes for `StrongURP`
within `spongeCollisionBound p q` against any admissible distinguisher class. -/
theorem spongeCollisionGame_substitutesWithin
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    (p : Parameters) (hp : p.Valid) (q : ℕ)
    (hq : q < Fintype.card (ByteState p.stateBytes))
    {T : TypedSystem (Bidirectional (ByteState p.stateBytes) q)}
    (hc : spongeCollisionGame p q |≡ T) :
    StrongURP (ByteState p.stateBytes) (q := q) ≃[fun _ =>
      ENNReal.ofReal (spongeCollisionBound p q)] T :=
  substitutesWithin_of_dist_le (spongeCollisionGame_dist_le p hp q hq hc)

end

end SpongeCollisionGame

end Commons.Sponge
