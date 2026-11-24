module

public import Commons.Schemes.Sponge.Simulator
public import RandomSystems.Distance.RatioCost

/-!
# Sponge indifferentiability via direct H-coefficient (`RatioCost`)

Proves statistical indifferentiability of the single-squeeze sponge construction over
`StrongURP (ByteState p.stateBytes)` in one hop using `RatioCost`
(`transcriptDistance_le_add_of_ratio_and_transcriptCost`) [1, §§3–4].

* `sponge_indifferentiability_hCoefficient_tight`: tight `Q^2 / |C|` distance bound.
* `sponge_indifferentiability_of_hCoefficient`: unified `Q^2 / |C| + C(Q, 2) / |S|` distance bound
  matching the 2-hop `≡g` game-equivalence engine.

## References

1. G. Bertoni, J. Daemen, M. Peeters, and G. Van Assche. *On the Indifferentiability of the Sponge
   Construction*. In *Advances in Cryptology — EUROCRYPT 2008*, LNCS 4965, pp. 181–197, 2008.
-/

@[expose] public section

namespace Commons.Sponge

open CategoryTheory ConstructiveCryptography SystemAlgebra
open Probability Probability.Distribution Commons.BidirectionalSwitching
open scoped BigOperators NNReal SystemAlgebra ConstructiveCryptography MonoidalCategory

/-! ### Path B: Direct 1-hop H-coefficient proof via `RatioCost` -/

section HCoefficientProof

variable (p : Parameters) (M : Type) [Fintype M] [DecidableEq M]


/-- Messages recorded in the lazy RO table `ro` whose sponge absorption is not yet complete
in `table`. -/
def uncompletedRO (encode : M → List (BitVec 8))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (ro : List (M × ByteState p.outputBytes)) : List (M × ByteState p.outputBytes) :=
  ro.filter fun md =>
    (evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode md.1))).isNone

open Classical in
/-- Single-step update of `replayGoodIdeal` for an exchange `(xq, yq)`. -/
noncomputable def replayGoodStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (ro : List (M × ByteState p.outputBytes))
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o)
    (yq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o) :
    Option (List (PermutationEdge (ByteState p.stateBytes)) ×
      List (M × ByteState p.outputBytes)) :=
  match xq, yq with
  | ⟨Sum.inl Evaluation.Port.eval, m⟩, ⟨Sum.inl Evaluation.Port.eval, d⟩ =>
    match ro.lookup m with
    | some d' => if d = d' then some (table, ro) else none
    | none => some (table, ro ++ [(m, d)])
  | ⟨Sum.inr Bidirectional.Port.forward, x⟩, ⟨Sum.inr Bidirectional.Port.forward, y⟩ =>
    match lookupForwardEdge table x with
    | some y' => if y = y' then some (table, ro) else none
    | none =>
      if capacityPart p y ∉
          occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table then
        match completingMessage p encode table x with
        | some m =>
          match ro.lookup m with
          | some d =>
            if digestPart p y = d then some (recordForwardEdge table x y, ro) else none
          | none => some (recordForwardEdge table x y, ro ++ [(m, digestPart p y)])
        | none => some (recordForwardEdge table x y, ro)
      else none
  | ⟨Sum.inr Bidirectional.Port.inverse, y⟩, ⟨Sum.inr Bidirectional.Port.inverse, x⟩ =>
    match lookupInverseEdge table y with
    | some x' => if x = x' then some (table, ro) else none
    | none =>
      if capacityPart p x ∉
          occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table then
        some (recordInverseEdge table x y, ro)
      else none
  | _, _ => none

open Classical in
/-- Deterministic good-transcript replay of `idealLazyStep`, rejecting any fresh public draw
that violates `AvoidsOccupiedCapacity`. -/
noncomputable def replayGoodIdeal {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)) →
      Option (List (PermutationEdge (ByteState p.stateBytes)) ×
        List (M × ByteState p.outputBytes)) :=
  let rec go (pre : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
      (state : List (PermutationEdge (ByteState p.stateBytes)) ×
        List (M × ByteState p.outputBytes)) :
      List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
        (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)) →
        Option (List (PermutationEdge (ByteState p.stateBytes)) ×
          List (M × ByteState p.outputBytes))
    | [] => some state
    | (xq, yq) :: rest =>
      if (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain pre xq then
        match replayGoodStep p M spec q_pub state.1 state.2 xq yq with
        | none => none
        | some st' => go (pre ++ [(xq, yq)]) st' rest
      else none
  go [] ([], [])

lemma replayGoodIdeal_nil {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    replayGoodIdeal p M spec q_pub [] = some ([], []) := rfl

open Classical in
lemma replayGoodIdeal_snoc {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o)
    (yq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o) :
    replayGoodIdeal p M spec q_pub (h ++ [(xq, yq)]) =
      if (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain h xq then
        match replayGoodIdeal p M spec q_pub h with
        | none => none
        | some (table, ro) => replayGoodStep p M spec q_pub table ro xq yq
      else none := by
  have hgo : ∀ (pre rest : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
      (st : List (PermutationEdge (ByteState p.stateBytes)) ×
        List (M × ByteState p.outputBytes)),
      replayGoodIdeal.go p M spec q_pub pre st (rest ++ [(xq, yq)]) =
        if (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain (pre ++ rest) xq then
          match replayGoodIdeal.go p M spec q_pub pre st rest with
          | none => none
          | some (table, ro) => replayGoodStep p M spec q_pub table ro xq yq
        else none := by
    intro pre rest
    induction rest generalizing pre with
    | nil =>
      intro ⟨table, ro⟩
      simp only [List.nil_append, List.append_nil, replayGoodIdeal.go]
      split_ifs with hd
      · cases replayGoodStep p M spec q_pub table ro xq yq <;> rfl
      · rfl
    | cons z tail ih =>
      intro ⟨table, ro⟩
      rcases z with ⟨x1, y1⟩
      simp only [List.cons_append, replayGoodIdeal.go]
      by_cases hd1 : (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain pre x1
      · rw [ite_eq_left hd1, ite_eq_left hd1]
        cases hst : replayGoodStep p M spec q_pub table ro x1 y1 with
        | none =>
          split_ifs <;> rfl
        | some st' =>
          simpa only [List.append_assoc, List.singleton_append] using
            ih (pre ++ [(x1, y1)]) st'
      · rw [ite_eq_right hd1, ite_eq_right hd1]
        split_ifs <;> rfl
  simpa only [List.nil_append, replayGoodIdeal] using hgo [] h ([], [])

/-- Structural invariant maintained by `replayGoodIdeal` on every good transcript `h`. -/
structure GoodReplayInv {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (ro : List (M × ByteState p.outputBytes)) : Prop where
  admitted : h = [] ∨ (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain (h.map Prod.fst)
  partialBij : IsPartialBijection (toPairs table)
  capFree : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table
  roNodup : (ro.map Prod.fst).Nodup
  tableLenLe : table.length ≤ publicQueryCount h
  completedInRO : ∀ m s,
    evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode m)) = some s →
      ro.lookup m = some (digestPart p s)
  uncompHonest : ∀ md ∈ uncompletedRO p M encode table ro,
    md.1 ∈ honestMessages p M spec q_pub h
  pubRecorded : ∀ z ∈ h,
    match z with
    | (⟨Sum.inr Bidirectional.Port.forward, x⟩, ⟨Sum.inr Bidirectional.Port.forward, y⟩) =>
      (x, y) ∈ toPairs table
    | (⟨Sum.inr Bidirectional.Port.inverse, y⟩, ⟨Sum.inr Bidirectional.Port.inverse, x⟩) =>
      (x, y) ∈ toPairs table
    | (⟨Sum.inl Evaluation.Port.eval, m⟩, ⟨Sum.inl Evaluation.Port.eval, d⟩) =>
      ro.lookup m = some d
    | _ => False

lemma lookup_eq_none_of_not_mem_map_fst {α β : Type*} [DecidableEq α]
    {l : List (α × β)} {a : α} (h : a ∉ l.map Prod.fst) : l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup_cons, beq_eq_false_iff_ne.mpr h.1]
    exact ih h.2

lemma mem_map_fst_of_lookup_eq_some {α β : Type*} [DecidableEq α]
    {l : List (α × β)} {a : α} {b : β} (h : l.lookup a = some b) : a ∈ l.map Prod.fst := by
  by_contra hn
  rw [lookup_eq_none_of_not_mem_map_fst hn] at h
  cases h

lemma lookup_mem_of_nodup {α β : Type*} [DecidableEq α]
    {l : List (α × β)} (hn : (l.map Prod.fst).Nodup) {a : α} {b : β} :
    l.lookup a = some b ↔ (a, b) ∈ l := by
  induction l with
  | nil => simp only [List.lookup_nil, List.not_mem_nil, reduceCtorEq]
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.lookup_cons, List.mem_cons, Prod.mk.injEq]
    by_cases hak : a = k
    · subst hak
      simp only [beq_self_eq_true, Option.some.injEq, true_and]
      constructor
      · intro hv; exact Or.inl hv.symm
      · rintro (rfl | hmem)
        · rfl
        · exact False.elim (hn.1 (List.mem_map.mpr ⟨(a, b), hmem, rfl⟩))
    · simp only [beq_eq_false_iff_ne.mpr hak, hak, false_and, false_or]
      exact ih hn.2

omit [Fintype M] [DecidableEq M] in
lemma lookup_isSome_of_mem_map_fst {α β : Type*} [DecidableEq α]
    {l : List (α × β)} {a : α} (h : a ∈ l.map Prod.fst) : ∃ b, l.lookup a = some b := by
  induction l with
  | nil => simp only [List.map_nil, List.not_mem_nil] at h
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.lookup_cons]
    by_cases hak : a = k
    · subst hak; exact ⟨v, by simp only [beq_self_eq_true]⟩
    · simp only [beq_eq_false_iff_ne.mpr hak]
      simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | htl
      · exact False.elim (hak rfl)
      · exact ih htl

omit [Fintype M] [DecidableEq M] in
lemma nodup_append_singleton_of_lookup_none {α β : Type*} [DecidableEq α]
    {l : List (α × β)} (hn : (l.map Prod.fst).Nodup) {a : α} (b : β)
    (hnone : l.lookup a = none) :
    ((l ++ [(a, b)]).map Prod.fst).Nodup := by
  rw [List.map_append, List.map_singleton, List.nodup_append]
  refine ⟨hn, List.nodup_singleton a, ?_⟩
  rintro x hx y hy rfl
  rw [List.mem_singleton.mp hy] at hx
  rcases lookup_isSome_of_mem_map_fst hx with ⟨c, hc⟩
  rw [hc] at hnone
  cases hnone

omit [Fintype M] [DecidableEq M] in
lemma uncompletedRO_append_edge_of_no_new_completion
    (encode : M → List (BitVec 8))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (ro : List (M × ByteState p.outputBytes))
    (edge : PermutationEdge (ByteState p.stateBytes))
    (hno : ∀ m : M,
      evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode m)) = none →
      evalAbsorption p (table ++ [edge]) (zeroState p.stateBytes) (paddedBlocks p (encode m)) =
        none) :
    uncompletedRO p M encode (table ++ [edge]) ro = uncompletedRO p M encode table ro := by
  unfold uncompletedRO
  apply List.filter_congr
  intro md _
  cases h : evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode md.1)) with
  | none =>
    rw [hno md.1 h]
  | some s =>
    rw [evalAbsorption_mono p h]


/-- Every good transcript replayed by `replayGoodIdeal` satisfies `GoodReplayInv`. -/
theorem replayGoodIdeal_inv (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    {table : List (PermutationEdge (ByteState p.stateBytes))}
    {ro : List (M × ByteState p.outputBytes)}
    (hrep : replayGoodIdeal p M spec q_pub h = some (table, ro)) :
    GoodReplayInv p M spec q_pub h table ro := by
  induction h using List.reverseRecOn generalizing table ro with
  | nil =>
    rw [replayGoodIdeal_nil] at hrep
    rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
    refine ⟨Or.inl rfl, ⟨List.nodup_nil, List.nodup_nil⟩,
      capacityCollisionFree_nil (capacityPart p) (zeroState p.capacityBytes),
      List.nodup_nil, Nat.zero_le _, ?_, ?_, fun _ hz => False.elim (List.not_mem_nil hz)⟩
    · intro m s hs
      have hne := paddedBlocks_ne_nil p hp.1 (encode m)
      cases hbl : paddedBlocks p (encode m) with
      | nil => exact False.elim (hne hbl)
      | cons b rest =>
        rw [hbl] at hs
        simp only [evalAbsorption, lookupForwardEdge] at hs
        cases hs
    · intro md hmd
      simp only [uncompletedRO, List.filter_nil, List.not_mem_nil] at hmd
  | append_singleton h z ih =>
    rcases z with ⟨xq, yq⟩
    rw [replayGoodIdeal_snoc] at hrep
    split_ifs at hrep with hadm
    · cases hpre : replayGoodIdeal p M spec q_pub h with
      | none => rw [hpre] at hrep; cases hrep
      | some st =>
        rcases st with ⟨table0, ro0⟩
        rw [hpre] at hrep
        have inv0 := ih hpre
        have hadm_dom : (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain
            (h.map Prod.fst ++ [xq]) := hadm
        have hadm' : h ++ [(xq, yq)] = [] ∨
            (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain
              ((h ++ [(xq, yq)]).map Prod.fst) :=
          Or.inr (by simpa only [List.map_append, List.map_singleton] using hadm_dom)
        unfold replayGoodStep at hrep
        rcases xq with ⟨o, u⟩; rcases yq with ⟨o', v⟩
        rcases o with o | o <;> rcases o' with o' | o'
        · cases o; cases o'
          cases hlu : ro0.lookup u with
          | some d' =>
            simp only [hlu] at hrep
            split_ifs at hrep with hvd
            subst hvd
            rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
            refine ⟨hadm', inv0.partialBij, inv0.capFree, inv0.roNodup, ?_,
              inv0.completedInRO, ?_, ?_⟩
            · rw [publicQueryCount_snoc]
              exact inv0.tableLenLe.trans (Nat.le_add_right _ _)
            · intro md hmd
              have hm := inv0.uncompHonest md hmd
              simp only [honestMessages, List.filterMap_append, List.mem_append]
              exact Or.inl hm
            · intro w hw
              rcases List.mem_append.mp hw with hw | hw
              · exact inv0.pubRecorded w hw
              · rw [List.mem_singleton.mp hw]; exact hlu
          | none =>
            simp only [hlu] at hrep
            rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
            refine ⟨hadm', inv0.partialBij, inv0.capFree,
              nodup_append_singleton_of_lookup_none inv0.roNodup v hlu, ?_, ?_, ?_, ?_⟩
            · rw [publicQueryCount_snoc]
              exact inv0.tableLenLe.trans (Nat.le_add_right _ _)
            · intro m s hs
              have h0 := inv0.completedInRO m s hs
              have hne : m ≠ u := by
                intro heq; subst heq; rw [h0] at hlu; cases hlu
              rw [lookup_append_singleton_of_none ro0 u v hlu m, ite_eq_right hne]
              exact h0
            · intro md hmd
              simp only [uncompletedRO, List.filter_append, List.filter_cons, List.filter_nil,
                List.mem_append] at hmd
              simp only [honestMessages, List.filterMap_append, List.filterMap_cons,
                List.filterMap_nil, List.mem_append, List.mem_singleton]
              rcases hmd with hmd | hmd
              · exact Or.inl (inv0.uncompHonest md hmd)
              · split_ifs at hmd with hnone
                · rw [List.mem_singleton.mp hmd]; exact Or.inr rfl
                · cases hmd
            · intro w hw
              rcases List.mem_append.mp hw with hw | hw
              · have hr0 := inv0.pubRecorded w hw
                rcases w with ⟨⟨ow, uw⟩, ⟨ow', vw⟩⟩
                rcases ow with ow | ow <;> rcases ow' with ow' | ow'
                · cases ow; cases ow'
                  dsimp only at hr0 ⊢
                  have hne : uw ≠ u := by
                    intro heq; subst heq; rw [hr0] at hlu; cases hlu
                  rw [lookup_append_singleton_of_none ro0 u v hlu uw, ite_eq_right hne]
                  exact hr0
                · cases ow; cases ow' <;> exact False.elim hr0
                · cases ow <;> cases ow' <;> exact False.elim hr0
                · cases ow <;> cases ow' <;> exact hr0
              · rw [List.mem_singleton.mp hw]
                dsimp only
                rw [lookup_append_singleton_of_none ro0 u v hlu u, ite_eq_left rfl]
        · cases o; cases o' <;> cases hrep
        · cases o <;> cases o' <;> cases hrep
        · cases o <;> cases o'
          · cases hlu : lookupForwardEdge table0 u with
            | some y' =>
              simp only [hlu] at hrep
              split_ifs at hrep with hvy
              subst hvy
              rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
              refine ⟨hadm', inv0.partialBij, inv0.capFree, inv0.roNodup, ?_,
                inv0.completedInRO, ?_, ?_⟩
              · rw [publicQueryCount_snoc]
                exact inv0.tableLenLe.trans (Nat.le_add_right _ _)
              · intro md hmd
                simp only [honestMessages, List.filterMap_append, List.mem_append]
                exact Or.inl (inv0.uncompHonest md hmd)
              · intro w hw
                rcases List.mem_append.mp hw with hw | hw
                · exact inv0.pubRecorded w hw
                · rw [List.mem_singleton.mp hw]
                  dsimp only
                  rcases lookupForwardEdge_eq_some_mem hlu with ⟨e, he, hin, hout⟩
                  exact List.mem_map.mpr ⟨e, he, Prod.ext hin hout⟩
            | none =>
              simp only [hlu] at hrep
              split_ifs at hrep with hcap
              have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes)
                  table0 ⟨u, v, false⟩ := hcap
              have hx_not : u ∉ (toPairs table0).map Prod.fst := by
                have hnf := (lookupForwardEdge_eq_none_iff table0 u).mp hlu
                intro hmem
                rcases List.mem_map.mp hmem with ⟨⟨a, b⟩, hab, rfl⟩
                rcases List.mem_map.mp hab with ⟨e, he, hpe⟩
                exact hnf e he (congrArg Prod.fst hpe)
              have hy_not : v ∉ (toPairs table0).map Prod.snd := by
                have hnf := output_not_mem_of_avoidsOccupied (capacityPart p)
                  (zeroState p.capacityBytes) table0 (x := u) (y := v) hf
                simpa only [toPairs, List.map_map, Function.comp_def] using hnf
              have hrec : recordForwardEdge table0 u v = table0 ++ [⟨u, v, false⟩] :=
                recordForwardEdge_eq_append_of_avoids p table0 hcap
              have hpb' : IsPartialBijection (toPairs (recordForwardEdge table0 u v)) := by
                rw [hrec, toPairs, List.map_append, List.map_singleton]
                exact isPartialBijection_append inv0.partialBij hx_not hy_not
              have hcf' : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes)
                  (recordForwardEdge table0 u v) := by
                rw [hrec]
                exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                  table0 inv0.capFree ⟨u, v, false⟩ hf
              have hlen' : (recordForwardEdge table0 u v).length ≤
                  publicQueryCount (h ++ [(⟨Sum.inr Bidirectional.Port.forward, u⟩,
                    ⟨Sum.inr Bidirectional.Port.forward, v⟩)]) := by
                rw [hrec, List.length_append, List.length_singleton,
                  publicQueryCount_snoc]
                simp only [Sum.isRight_inr, ↓reduceIte]
                exact Nat.add_le_add_right inv0.tableLenLe 1
              have hpub_prev : ∀ w ∈ h,
                  match w with
                  | (⟨Sum.inr Bidirectional.Port.forward, x⟩,
                      ⟨Sum.inr Bidirectional.Port.forward, y⟩) =>
                    (x, y) ∈ toPairs (recordForwardEdge table0 u v)
                  | (⟨Sum.inr Bidirectional.Port.inverse, y⟩,
                      ⟨Sum.inr Bidirectional.Port.inverse, x⟩) =>
                    (x, y) ∈ toPairs (recordForwardEdge table0 u v)
                  | (⟨Sum.inl Evaluation.Port.eval, m⟩,
                      ⟨Sum.inl Evaluation.Port.eval, d⟩) =>
                    ro0.lookup m = some d
                  | _ => False := by
                intro w hw
                have hr0 := inv0.pubRecorded w hw
                rcases w with ⟨⟨ow, uw⟩, ⟨ow', vw⟩⟩
                rcases ow with ow | ow <;> rcases ow' with ow' | ow'
                · cases ow; cases ow'; exact hr0
                · cases ow; cases ow' <;> exact False.elim hr0
                · cases ow <;> cases ow' <;> exact False.elim hr0
                · cases ow <;> cases ow'
                  · dsimp only at hr0 ⊢; rw [hrec, toPairs, List.map_append]
                    exact List.mem_append_left _ hr0
                  · exact False.elim hr0
                  · exact False.elim hr0
                  · dsimp only at hr0 ⊢; rw [hrec, toPairs, List.map_append]
                    exact List.mem_append_left _ hr0
              cases hcm : completingMessage p encode table0 u with
              | some m =>
                simp only [hcm] at hrep
                cases hro : ro0.lookup m with
                | some d =>
                  simp only [hro] at hrep
                  split_ifs at hrep with hdig
                  rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
                  refine ⟨hadm', hpb', hcf', inv0.roNodup, hlen', ?_, ?_, ?_⟩
                  · intro m' s hs
                    cases h0 : evalAbsorption p table0 (zeroState p.stateBytes)
                        (paddedBlocks p (encode m')) with
                    | some s0 =>
                      have hmono : evalAbsorption p (recordForwardEdge table0 u v)
                          (zeroState p.stateBytes) (paddedBlocks p (encode m')) = some s0 := by
                        rw [hrec]; exact evalAbsorption_mono p h0
                      have hEq : s0 = s := Option.some.inj (hmono.symm.trans hs)
                      subst hEq
                      exact inv0.completedInRO m' s0 h0
                    | none =>
                      by_cases hmm : m' = m
                      · subst hmm
                        have hmc := evalAbsorption_recordForwardEdge_of_completing p M hp
                          encode henc table0 inv0.partialBij inv0.capFree hlu hcap hcm
                        have hEq : v = s := Option.some.inj (hmc.symm.trans hs)
                        subst hEq
                        rw [hdig]; exact hro
                      · have hne_cm : completingMessage p encode table0 u ≠ some m' := by
                          rw [hcm]; intro he; exact hmm (Option.some.inj he).symm
                        rw [evalAbsorption_recordForwardEdge_other_none p M hp encode henc
                          table0 inv0.partialBij inv0.capFree hcap h0 hne_cm] at hs
                        cases hs
                  · intro md hmd
                    simp only [uncompletedRO, List.mem_filter] at hmd
                    have hnone0 : (evalAbsorption p table0 (zeroState p.stateBytes)
                        (paddedBlocks p (encode md.1))).isNone = true := by
                      cases h0 : evalAbsorption p table0 (zeroState p.stateBytes)
                          (paddedBlocks p (encode md.1)) with
                      | none => rfl
                      | some s0 =>
                        have hmono : evalAbsorption p (recordForwardEdge table0 u v)
                            (zeroState p.stateBytes) (paddedBlocks p (encode md.1)) = some s0 := by
                          rw [hrec]; exact evalAbsorption_mono p h0
                        rw [hmono] at hmd
                        simp only [Option.isNone_some, Bool.false_eq_true] at hmd
                        exact False.elim hmd.2
                    have hm0 := inv0.uncompHonest md
                      (List.mem_filter.mpr ⟨hmd.1, hnone0⟩)
                    simp only [honestMessages, List.filterMap_append, List.mem_append]
                    exact Or.inl hm0
                  · intro w hw
                    rcases List.mem_append.mp hw with hw | hw
                    · exact hpub_prev w hw
                    · rw [List.mem_singleton.mp hw]
                      dsimp only
                      rw [hrec, toPairs, List.map_append, List.map_singleton]
                      exact List.mem_append_right _ (List.mem_singleton_self _)
                | none =>
                  simp only [hro] at hrep
                  rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
                  refine ⟨hadm', hpb', hcf',
                    nodup_append_singleton_of_lookup_none inv0.roNodup (digestPart p v) hro,
                    hlen', ?_, ?_, ?_⟩
                  · intro m' s hs
                    cases h0 : evalAbsorption p table0 (zeroState p.stateBytes)
                        (paddedBlocks p (encode m')) with
                    | some s0 =>
                      have hmono : evalAbsorption p (recordForwardEdge table0 u v)
                          (zeroState p.stateBytes) (paddedBlocks p (encode m')) = some s0 := by
                        rw [hrec]; exact evalAbsorption_mono p h0
                      have hEq : s0 = s := Option.some.inj (hmono.symm.trans hs)
                      subst hEq
                      have hlu0 := inv0.completedInRO m' s0 h0
                      have hne : m' ≠ m := by
                        intro he; subst he; rw [hlu0] at hro; cases hro
                      rw [lookup_append_singleton_of_none ro0 m (digestPart p v) hro m',
                        ite_eq_right hne]
                      exact hlu0
                    | none =>
                      by_cases hmm : m' = m
                      · subst m'
                        have hmc := evalAbsorption_recordForwardEdge_of_completing p M hp
                          encode henc table0 inv0.partialBij inv0.capFree hlu hcap hcm
                        have hEq : v = s := Option.some.inj (hmc.symm.trans hs)
                        subst hEq
                        rw [lookup_append_singleton_of_none ro0 m (digestPart p v) hro m,
                          ite_eq_left rfl]
                      · have hne_cm : completingMessage p encode table0 u ≠ some m' := by
                          rw [hcm]; intro he; exact hmm (Option.some.inj he).symm
                        rw [evalAbsorption_recordForwardEdge_other_none p M hp encode henc
                          table0 inv0.partialBij inv0.capFree hcap h0 hne_cm] at hs
                        cases hs
                  · intro md hmd
                    simp only [uncompletedRO, List.mem_filter, List.mem_append,
                      List.mem_singleton] at hmd
                    rcases hmd.1 with hmd0 | hmd_eq
                    · have hnone0 : (evalAbsorption p table0 (zeroState p.stateBytes)
                          (paddedBlocks p (encode md.1))).isNone = true := by
                        cases h0 : evalAbsorption p table0 (zeroState p.stateBytes)
                            (paddedBlocks p (encode md.1)) with
                        | none => rfl
                        | some s0 =>
                          have hmono : evalAbsorption p (recordForwardEdge table0 u v)
                              (zeroState p.stateBytes) (paddedBlocks p (encode md.1)) =
                                some s0 := by
                            rw [hrec]; exact evalAbsorption_mono p h0
                          rw [hmono] at hmd
                          simp only [Option.isNone_some, Bool.false_eq_true] at hmd
                          exact False.elim hmd.2
                      have hm0 := inv0.uncompHonest md (List.mem_filter.mpr ⟨hmd0, hnone0⟩)
                      simp only [honestMessages, List.filterMap_append, List.mem_append]
                      exact Or.inl hm0
                    · rw [hmd_eq] at hmd
                      have hmc := evalAbsorption_recordForwardEdge_of_completing p M hp
                        encode henc table0 inv0.partialBij inv0.capFree hlu hcap hcm
                      rw [hmc] at hmd
                      simp only [Option.isNone_some, Bool.false_eq_true] at hmd
                      exact False.elim hmd.2
                  · intro w hw
                    rcases List.mem_append.mp hw with hw | hw
                    · have hr := hpub_prev w hw
                      rcases w with ⟨⟨ow, uw⟩, ⟨ow', vw⟩⟩
                      rcases ow with ow | ow <;> rcases ow' with ow' | ow'
                      · cases ow; cases ow'
                        dsimp only at hr ⊢
                        have hne : uw ≠ m := by
                          intro he; subst he; rw [hr] at hro; cases hro
                        rw [lookup_append_singleton_of_none ro0 m (digestPart p v) hro uw,
                          ite_eq_right hne]
                        exact hr
                      · cases ow; cases ow' <;> exact False.elim hr
                      · cases ow <;> cases ow' <;> exact False.elim hr
                      · cases ow <;> cases ow' <;> exact hr
                    · rw [List.mem_singleton.mp hw]
                      dsimp only
                      rw [hrec, toPairs, List.map_append, List.map_singleton]
                      exact List.mem_append_right _ (List.mem_singleton_self _)
              | none =>
                simp only [hcm] at hrep
                rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
                refine ⟨hadm', hpb', hcf', inv0.roNodup, hlen', ?_, ?_, ?_⟩
                · intro m' s hs
                  cases h0 : evalAbsorption p table0 (zeroState p.stateBytes)
                      (paddedBlocks p (encode m')) with
                  | some s0 =>
                    have hmono : evalAbsorption p (recordForwardEdge table0 u v)
                        (zeroState p.stateBytes) (paddedBlocks p (encode m')) = some s0 := by
                      rw [hrec]; exact evalAbsorption_mono p h0
                    have hEq : s0 = s := Option.some.inj (hmono.symm.trans hs)
                    subst hEq
                    exact inv0.completedInRO m' s0 h0
                  | none =>
                    have hne_cm : completingMessage p encode table0 u ≠ some m' := by
                      rw [hcm]; intro h'; cases h'
                    rw [evalAbsorption_recordForwardEdge_other_none p M hp encode henc
                      table0 inv0.partialBij inv0.capFree hcap h0 hne_cm] at hs
                    cases hs
                · intro md hmd
                  have hsame := uncompletedRO_append_edge_of_no_new_completion p M encode
                    table0 ro0 ⟨u, v, false⟩
                    (fun m' h0 => by
                      rw [← hrec]
                      exact evalAbsorption_recordForwardEdge_other_none p M hp encode henc
                        table0 inv0.partialBij inv0.capFree hcap h0
                        (by rw [hcm]; intro h'; cases h'))
                  rw [hrec, hsame] at hmd
                  simp only [honestMessages, List.filterMap_append, List.mem_append]
                  exact Or.inl (inv0.uncompHonest md hmd)
                · intro w hw
                  rcases List.mem_append.mp hw with hw | hw
                  · exact hpub_prev w hw
                  · rw [List.mem_singleton.mp hw]
                    dsimp only
                    rw [hrec, toPairs, List.map_append, List.map_singleton]
                    exact List.mem_append_right _ (List.mem_singleton_self _)
          · cases hrep
          · cases hrep
          · cases hlu : lookupInverseEdge table0 u with
            | some x' =>
              simp only [hlu] at hrep
              split_ifs at hrep with hvx
              subst hvx
              rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
              refine ⟨hadm', inv0.partialBij, inv0.capFree, inv0.roNodup, ?_,
                inv0.completedInRO, ?_, ?_⟩
              · rw [publicQueryCount_snoc]
                exact inv0.tableLenLe.trans (Nat.le_add_right _ _)
              · intro md hmd
                simp only [honestMessages, List.filterMap_append, List.mem_append]
                exact Or.inl (inv0.uncompHonest md hmd)
              · intro w hw
                rcases List.mem_append.mp hw with hw | hw
                · exact inv0.pubRecorded w hw
                · rw [List.mem_singleton.mp hw]
                  dsimp only
                  rcases lookupInverseEdge_eq_some_mem hlu with ⟨e, he, hin, hout⟩
                  exact List.mem_map.mpr ⟨e, he, Prod.ext hin hout⟩
            | none =>
              simp only [hlu] at hrep
              split_ifs at hrep with hcap
              rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
              have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes)
                  table0 ⟨v, u, true⟩ := hcap
              have hx_not : v ∉ (toPairs table0).map Prod.fst := by
                have hnf := input_not_mem_of_avoidsOccupied (capacityPart p)
                  (zeroState p.capacityBytes) table0 (x := v) (y := u) hf
                simpa only [toPairs, List.map_map, Function.comp_def] using hnf
              have hy_not : u ∉ (toPairs table0).map Prod.snd := by
                have hnf := (lookupInverseEdge_eq_none_iff table0 u).mp hlu
                intro hmem
                rcases List.mem_map.mp hmem with ⟨⟨a, b⟩, hab, rfl⟩
                rcases List.mem_map.mp hab with ⟨e, he, hpe⟩
                exact hnf e he (congrArg Prod.snd hpe)
              have hrec : recordInverseEdge table0 v u = table0 ++ [⟨v, u, true⟩] :=
                recordInverseEdge_eq_append_of_avoids p table0 hcap
              refine ⟨hadm', ?_, ?_, inv0.roNodup, ?_, ?_, ?_, ?_⟩
              · rw [hrec, toPairs, List.map_append, List.map_singleton]
                exact isPartialBijection_append inv0.partialBij hx_not hy_not
              · rw [hrec]
                exact capacityCollisionFree_append (capacityPart p)
                  (zeroState p.capacityBytes) table0 inv0.capFree ⟨v, u, true⟩ hf
              · rw [hrec, List.length_append, List.length_singleton,
                  publicQueryCount_snoc]
                simp only [Sum.isRight_inr, ↓reduceIte]
                exact Nat.add_le_add_right inv0.tableLenLe 1
              · intro m' s hs
                cases h0 : evalAbsorption p table0 (zeroState p.stateBytes)
                    (paddedBlocks p (encode m')) with
                | some s0 =>
                  have hmono : evalAbsorption p (recordInverseEdge table0 v u)
                      (zeroState p.stateBytes) (paddedBlocks p (encode m')) = some s0 := by
                    rw [hrec]; exact evalAbsorption_mono p h0
                  have hEq : s0 = s := Option.some.inj (hmono.symm.trans hs)
                  subst hEq
                  exact inv0.completedInRO m' s0 h0
                | none =>
                  rw [evalAbsorption_recordInverseEdge_none p M hp encode table0 hcap m' h0] at hs
                  cases hs
              · intro md hmd
                have hsame := uncompletedRO_append_edge_of_no_new_completion p M encode
                  table0 ro0 ⟨v, u, true⟩
                  (fun m' h0 => by
                    rw [← hrec]
                    exact evalAbsorption_recordInverseEdge_none p M hp encode table0 hcap m' h0)
                rw [hrec, hsame] at hmd
                simp only [honestMessages, List.filterMap_append, List.mem_append]
                exact Or.inl (inv0.uncompHonest md hmd)
              · intro w hw
                rcases List.mem_append.mp hw with hw | hw
                · have hr0 := inv0.pubRecorded w hw
                  rcases w with ⟨⟨ow, uw⟩, ⟨ow', vw⟩⟩
                  rcases ow with ow | ow <;> rcases ow' with ow' | ow'
                  · cases ow; cases ow'; exact hr0
                  · cases ow; cases ow' <;> exact False.elim hr0
                  · cases ow <;> cases ow' <;> exact False.elim hr0
                  · cases ow <;> cases ow'
                    · dsimp only at hr0 ⊢; rw [hrec, toPairs, List.map_append]
                      exact List.mem_append_left _ hr0
                    · exact False.elim hr0
                    · exact False.elim hr0
                    · dsimp only at hr0 ⊢; rw [hrec, toPairs, List.map_append]
                      exact List.mem_append_left _ hr0
                · rw [List.mem_singleton.mp hw]
                  dsimp only
                  rw [hrec, toPairs, List.map_append, List.map_singleton]
                  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Uncompleted RO entries carry total padded block work at most `w`. -/
lemma uncompletedRO_work_le (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    {table : List (PermutationEdge (ByteState p.stateBytes))}
    {ro : List (M × ByteState p.outputBytes)}
    (hrep : replayGoodIdeal p M spec q_pub h = some (table, ro)) :
    ((uncompletedRO p M encode table ro).map fun md =>
      paddedBlockCount p (encode md.1).length).sum ≤ w := by
  have inv := replayGoodIdeal_inv p M hp henc spec q_pub h hrep
  have hnodup : ((uncompletedRO p M encode table ro).map Prod.fst).Nodup := by
    have hsub : ((uncompletedRO p M encode table ro).map Prod.fst).Sublist (ro.map Prod.fst) :=
      List.Sublist.map Prod.fst (List.filter_sublist)
    exact inv.roNodup.sublist hsub
  have hsub_fin : ((uncompletedRO p M encode table ro).map Prod.fst).toFinset ⊆
      (honestMessages p M spec q_pub h).toFinset := by
    intro m hm
    rw [List.mem_toFinset] at hm ⊢
    rcases List.mem_map.mp hm with ⟨md, hmd, rfl⟩
    exact inv.uncompHonest md hmd
  have hsum_eq : ((uncompletedRO p M encode table ro).map fun md =>
        paddedBlockCount p (encode md.1).length).sum =
      ∑ m ∈ ((uncompletedRO p M encode table ro).map Prod.fst).toFinset,
        paddedBlockCount p (encode m).length := by
    rw [List.sum_toFinset _ hnodup, List.map_map]
    rfl
  have hsum_le_hon :
      ∑ m ∈ (honestMessages p M spec q_pub h).toFinset, paddedBlockCount p (encode m).length ≤
        ((honestMessages p M spec q_pub h).map fun m => paddedBlockCount p (encode m).length).sum :=
          by
    induction honestMessages p M spec q_pub h with
    | nil => simp only [List.toFinset_nil, Finset.sum_empty, List.map_nil, List.sum_nil, le_refl]
    | cons m rest ih =>
      simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
      by_cases hm : m ∈ rest.toFinset
      · rw [Finset.insert_eq_of_mem hm]
        exact ih.trans (Nat.le_add_left _ _)
      · rw [Finset.sum_insert hm]
        exact Nat.add_le_add_left ih _
  calc ((uncompletedRO p M encode table ro).map fun md =>
          paddedBlockCount p (encode md.1).length).sum
      = ∑ m ∈ ((uncompletedRO p M encode table ro).map Prod.fst).toFinset,
          paddedBlockCount p (encode m).length := hsum_eq
    _ ≤ ∑ m ∈ (honestMessages p M spec q_pub h).toFinset,
          paddedBlockCount p (encode m).length := Finset.sum_le_sum_of_subset hsub_fin
    _ ≤ ((honestMessages p M spec q_pub h).map fun m =>
          paddedBlockCount p (encode m).length).sum := hsum_le_hon
    _ ≤ w := honestMessages_work_le p M spec q_pub h inv.admitted

omit [Fintype M] in
lemma uncompletedRO_length_recordForwardEdge_completing_some (hp : p.Valid)
    (encode : M → List (BitVec 8)) (henc : Function.Injective encode)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (ro : List (M × ByteState p.outputBytes))
    (hpb : IsPartialBijection (toPairs table))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    (hnodup : (ro.map Prod.fst).Nodup)
    {x y : ByteState p.stateBytes} (hlu : lookupForwardEdge table x = none)
    (hcap : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table)
    {m : M} (hcm : completingMessage p encode table x = some m)
    {d : ByteState p.outputBytes} (hro : ro.lookup m = some d) :
    (uncompletedRO p M encode (recordForwardEdge table x y) ro).length + 1 =
      (uncompletedRO p M encode table ro).length := by
  have hnone_m := evalAbsorption_none_of_completing p M hp encode henc table hpb hg hlu hcm
  have hmd_mem : (m, d) ∈ uncompletedRO p M encode table ro := by
    rw [uncompletedRO, List.mem_filter]
    refine ⟨(lookup_mem_of_nodup hnodup).mp hro, ?_⟩
    rw [hnone_m]; rfl
  have hfilt : uncompletedRO p M encode (recordForwardEdge table x y) ro =
      (uncompletedRO p M encode table ro).filter (fun md => md.1 != m) := by
    unfold uncompletedRO
    rw [List.filter_filter]
    apply List.filter_congr
    intro md _
    by_cases hmeq : md.1 = m
    · subst hmeq
      have hmc := evalAbsorption_recordForwardEdge_of_completing p M hp encode henc
        table hpb hg hlu hcap hcm
      simp only [hmc, Option.isNone_some, bne_self_eq_false, Bool.false_and]
    · have hbne : (md.1 != m) = true := bne_iff_ne.mpr hmeq
      rw [hbne, Bool.true_and]
      cases h0 : evalAbsorption p table (zeroState p.stateBytes)
          (paddedBlocks p (encode md.1)) with
      | none =>
        have hne_cm : completingMessage p encode table x ≠ some md.1 := by
          rw [hcm]; intro he; exact hmeq (Option.some.inj he).symm
        rw [evalAbsorption_recordForwardEdge_other_none p M hp encode henc table hpb hg
          hcap h0 hne_cm]
      | some s =>
        rw [recordForwardEdge_eq_append_of_avoids p table hcap, evalAbsorption_mono p h0]
  rw [hfilt]
  have hnodup_u : ((uncompletedRO p M encode table ro).map Prod.fst).Nodup :=
    hnodup.sublist (List.Sublist.map Prod.fst List.filter_sublist)
  generalize hu : uncompletedRO p M encode table ro = u at hmd_mem hnodup_u ⊢
  clear hu
  induction u with
  | nil => cases hmd_mem
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup_u
    simp only [List.filter_cons, List.length_cons]
    rcases List.mem_cons.mp hmd_mem with rfl | htl
    · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have hall : tl.filter (fun md => md.1 != m) = tl := by
        apply List.filter_eq_self.mpr
        intro z hz
        simp only [bne_iff_ne, ne_eq]
        intro hzm
        exact hnodup_u.1 (List.mem_map.mpr ⟨z, hz, hzm⟩)
      rw [hall]
    · have hne : hd.1 ≠ m := by
        intro hEq
        exact hnodup_u.1 (List.mem_map.mpr ⟨(m, d), htl, hEq.symm⟩)
      simp only [bne_iff_ne, ne_eq, hne, not_false_eq_true, ↓reduceIte, List.length_cons]
      have hih := ih htl hnodup_u.2
      omega

omit [Fintype M] in
lemma uncompletedRO_recordForwardEdge_completing_none (hp : p.Valid)
    (encode : M → List (BitVec 8)) (henc : Function.Injective encode)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (ro : List (M × ByteState p.outputBytes))
    (hpb : IsPartialBijection (toPairs table))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    {x y : ByteState p.stateBytes} (hlu : lookupForwardEdge table x = none)
    (hcap : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table)
    {m : M} (hcm : completingMessage p encode table x = some m)
    (hro : ro.lookup m = none) :
    uncompletedRO p M encode (recordForwardEdge table x y) (ro ++ [(m, digestPart p y)]) =
      uncompletedRO p M encode table ro := by
  unfold uncompletedRO
  rw [List.filter_append, List.filter_cons, List.filter_nil]
  have hmc := evalAbsorption_recordForwardEdge_of_completing p M hp encode henc
    table hpb hg hlu hcap hcm
  simp only [hmc, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  apply List.filter_congr
  intro md hmd
  have hne : md.1 ≠ m := by
    intro hEq
    subst hEq
    rcases lookup_isSome_of_mem_map_fst (List.mem_map.mpr ⟨md, hmd, rfl⟩) with ⟨c, hc⟩
    rw [hc] at hro
    cases hro
  cases h0 : evalAbsorption p table (zeroState p.stateBytes)
      (paddedBlocks p (encode md.1)) with
  | none =>
    have hne_cm : completingMessage p encode table x ≠ some md.1 := by
      rw [hcm]; intro he; exact hne (Option.some.inj he).symm
    rw [evalAbsorption_recordForwardEdge_other_none p M hp encode henc table hpb hg
      hcap h0 hne_cm]
  | some s =>
    rw [recordForwardEdge_eq_append_of_avoids p table hcap, evalAbsorption_mono p h0]

omit [Fintype M] [DecidableEq M] in
open Classical in
lemma uniform_map_transition_eq {A : Interface} {S α : Type} [Fintype α] [Nonempty α]
    (c : ℝ) (o : A.I) (u : A.X o) (v : A.Y o) (snext : α → S) (out : α → A.Y o) (a₀ : α)
    (hiff : ∀ a : α, out a = v ↔ a = a₀) :
    c • fTransform Prod.fst
      ((fTransform (ProbStep.tagged (Y := A.Y) ⟨o, u⟩)
        ((𝒰[α]).map fun a => (snext a, out a)).1).restrict
          fun sy => sy.2 = (⟨o, v⟩ : Σ i, A.Y i)) =
    (c * (1 / (Fintype.card α : ℝ))) • Finsupp.single (snext a₀) 1 := by
  rw [ProbDist.map_val, fTransform_fTransform, Distribution.restrict_fTransform,
    fTransform_fTransform]
  have hpred : ∀ a : α,
      ((ProbStep.tagged (Y := A.Y) ⟨o, u⟩ (snext a, out a)).2 =
        (⟨o, v⟩ : Σ i, A.Y i)) ↔ a = a₀ := by
    intro a
    simp only [ProbStep.tagged, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    exact hiff a
  have hrest :
      ((uniform α).restrict fun a =>
        (ProbStep.tagged (Y := A.Y) ⟨o, u⟩ (snext a, out a)).2 =
          (⟨o, v⟩ : Σ i, A.Y i)) =
      (1 / (Fintype.card α : ℝ)) • Finsupp.single a₀ 1 := by
    rw [Distribution.restrict_congr _ hpred]
    apply Finsupp.ext
    intro a
    simp only [Distribution.restrict, Finsupp.filter_apply, uniform_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases ha : a = a₀
    · subst ha; simp only [↓reduceIte]
    · simp only [ite_eq_right ha, ite_eq_right (Ne.symm ha)]
  have hres :
      fTransform (Prod.fst ∘ (ProbStep.tagged (Y := A.Y) ⟨o, u⟩ ∘ fun a => (snext a, out a)))
        ((uniform α).restrict fun a =>
          (ProbStep.tagged (Y := A.Y) ⟨o, u⟩ (snext a, out a)).2 =
            (⟨o, v⟩ : Σ i, A.Y i)) =
      (1 / (Fintype.card α : ℝ)) • Finsupp.single (snext a₀) 1 := by
    rw [hrest, fTransform_smul, fTransform_single]
    rfl
  exact (congrArg (c • ·) hres).trans (smul_smul _ _ _)

open Classical in
/-- Exact belief of `idealLazyStep` on every good transcript `h`: point mass on `(table, ro)`
with weight `1 / (|S|^{|table|} * |D|^{|uncompletedRO|})`. -/
theorem idealLazyStep_belief_of_replayGood (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    {table : List (PermutationEdge (ByteState p.stateBytes))}
    {ro : List (M × ByteState p.outputBytes)}
    (hrep : replayGoodIdeal p M spec q_pub h = some (table, ro)) :
    (idealLazyStep p M spec q_pub).belief
        (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain
        (ProbDist.single ([], [])).1 h =
      (1 / ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
        (Fintype.card (ByteState p.outputBytes) : ℝ) ^
          (uncompletedRO p M encode table ro).length)) •
        Finsupp.single (table, ro) 1 := by
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  have hS_ne : (Fintype.card (ByteState p.stateBytes) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ByteState p.stateBytes))
  have hD_ne : (Fintype.card (ByteState p.outputBytes) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ByteState p.outputBytes))
  have hT_ne : (Fintype.card (ByteState (tailBytes p)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ByteState (tailBytes p)))
  have hSDT : (Fintype.card (ByteState p.stateBytes) : ℝ) =
      (Fintype.card (ByteState p.outputBytes) : ℝ) *
        (Fintype.card (ByteState (tailBytes p)) : ℝ) := by
    exact_mod_cast card_state_eq_digest_mul_tail p (hp.2.2.2.1.trans hp.2.1.le)
  induction h using List.reverseRecOn generalizing table ro with
  | nil =>
    rw [replayGoodIdeal_nil] at hrep
    rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
    simp only [ProbStep.belief, ProbStep.beliefRev, List.reverse_nil, ProbDist.single,
      List.length_nil, uncompletedRO, List.filter_nil, pow_zero, mul_one, div_one, one_smul]
  | append_singleton h z ih =>
    rcases z with ⟨xq, yq⟩
    rw [replayGoodIdeal_snoc] at hrep
    split_ifs at hrep with hadm
    cases hpre : replayGoodIdeal p M spec q_pub h with
    | none => rw [hpre] at hrep; cases hrep
    | some st =>
      rcases st with ⟨table0, ro0⟩
      rw [hpre] at hrep
      have inv0 := replayGoodIdeal_inv p M hp henc spec q_pub h hpre
      rw [ProbStep.belief_snoc, ite_eq_left hadm, ih hpre]
      simp only [ProbStep.transition, ProbStep.outcome]
      rw [Finsupp.smul_single, smul_eq_mul, mul_one, bindK_single]
      unfold replayGoodStep at hrep
      rcases xq with ⟨o, u⟩; rcases yq with ⟨o', v⟩
      rcases o with o | o <;> rcases o' with o' | o'
      · cases o; cases o'
        simp only [idealLazyStep]
        cases hlu : ro0.lookup u with
        | some d' =>
          simp only [hlu] at hrep
          split_ifs at hrep with hvd
          subst hvd
          rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
          simp only [ProbDist.single, fTransform_single, ProbStep.tagged,
            Distribution.single_restrict, ↓reduceIte]
        | none =>
          simp only [hlu] at hrep
          rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
          have hnot_comp : evalAbsorption p table0 (zeroState p.stateBytes)
              (paddedBlocks p (encode u)) = none := by
            cases h0 : evalAbsorption p table0 (zeroState p.stateBytes)
                (paddedBlocks p (encode u)) with
            | none => rfl
            | some s0 =>
              have hc := inv0.completedInRO u s0 h0
              rw [hc] at hlu; cases hlu
          have huncomp_len :
              (uncompletedRO p M encode table0 (ro0 ++ [(u, v)])).length =
                (uncompletedRO p M encode table0 ro0).length + 1 := by
            simp only [uncompletedRO, List.filter_append, List.filter_cons, List.filter_nil,
              hnot_comp, Option.isNone_none, ↓reduceIte, List.length_append, List.length_singleton]
          dsimp only
          refine (uniform_map_transition_eq (A := A) (α := ByteState p.outputBytes) _
            (Sum.inl Evaluation.Port.eval) u v
            (fun d => (table0, ro0 ++ [(u, d)])) (fun d => d) v (fun _ => Iff.rfl)).trans ?_
          rw [huncomp_len, pow_succ]
          congr 1
          field_simp [hS_ne, hD_ne]
      · cases o; cases o' <;> cases hrep
      · cases o <;> cases o' <;> cases hrep
      · cases o <;> cases o'
        · simp only [idealLazyStep]
          cases hlu : lookupForwardEdge table0 u with
          | some y' =>
            simp only [hlu] at hrep
            split_ifs at hrep with hvy
            subst hvy
            rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
            simp only [ProbDist.single, fTransform_single, ProbStep.tagged,
              Distribution.single_restrict, ↓reduceIte]
          | none =>
            simp only [hlu] at hrep
            split_ifs at hrep with hcap
            have hrec : recordForwardEdge table0 u v = table0 ++ [⟨u, v, false⟩] :=
              recordForwardEdge_eq_append_of_avoids p table0 hcap
            cases hcm : completingMessage p encode table0 u with
            | some m =>
              simp only [hcm] at hrep
              cases hro : ro0.lookup m with
              | some d =>
                simp only [hro] at hrep
                split_ifs at hrep with hdig
                rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
                have huncomp := uncompletedRO_length_recordForwardEdge_completing_some p M
                  hp encode henc table0 ro0 inv0.partialBij inv0.capFree inv0.roNodup
                  hlu hcap hcm hro
                have hreasm : assembleState p d (tailPart p v) = v := by
                  rw [← hdig, assembleState_digestPart_tailPart p (hp.2.2.2.1.trans hp.2.1.le)]
                simp only [hro]
                refine (uniform_map_transition_eq (A := A) (α := ByteState (tailBytes p)) _
                  (Sum.inr Bidirectional.Port.forward) u v
                  (fun t : ByteState (tailBytes p) =>
                    (recordForwardEdge table0 u (assembleState p d t), ro0))
                  (fun t => assembleState p d t) (tailPart p v)
                  (fun t => ⟨fun hEq => by
                    have htp := congrArg (tailPart p) hEq
                    rwa [tailPart_assembleState p (hp.2.2.2.1.trans hp.2.1.le)] at htp,
                    fun ht => by
                      rw [ht, hreasm]⟩)).trans ?_
                rw [hreasm, ← huncomp, hrec, List.length_append,
                  List.length_singleton, pow_succ, pow_succ]
                congr 1
                rw [hSDT]
                field_simp [hD_ne, hT_ne]
              | none =>
                simp only [hro] at hrep
                rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
                have huncomp := uncompletedRO_recordForwardEdge_completing_none p M hp
                  encode henc table0 ro0 inv0.partialBij inv0.capFree hlu hcap hcm hro
                simp only [hro]
                refine (uniform_map_transition_eq (A := A) (α := ByteState p.stateBytes) _
                  (Sum.inr Bidirectional.Port.forward) u v
                  (fun y => (recordForwardEdge table0 u y, ro0 ++ [(m, digestPart p y)]))
                  (fun y => y) v (fun _ => Iff.rfl)).trans ?_
                rw [huncomp, hrec, List.length_append, List.length_singleton, pow_succ]
                congr 1
                field_simp [hS_ne, hD_ne]
            | none =>
              simp only [hcm] at hrep
              rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
              have huncomp := uncompletedRO_append_edge_of_no_new_completion p M encode
                table0 ro0 ⟨u, v, false⟩
                (fun m' h0 => by
                  rw [← hrec]
                  exact evalAbsorption_recordForwardEdge_other_none p M hp encode henc
                    table0 inv0.partialBij inv0.capFree hcap h0
                    (by rw [hcm]; intro h'; cases h'))
              dsimp only
              refine (uniform_map_transition_eq (A := A) (α := ByteState p.stateBytes) _
                (Sum.inr Bidirectional.Port.forward) u v
                (fun y => (recordForwardEdge table0 u y, ro0))
                (fun y => y) v (fun _ => Iff.rfl)).trans ?_
              rw [hrec, huncomp, List.length_append, List.length_singleton, pow_succ]
              congr 1
              field_simp [hS_ne, hD_ne]
        · cases hrep
        · cases hrep
        · simp only [idealLazyStep]
          cases hlu : lookupInverseEdge table0 u with
          | some x' =>
            simp only [hlu] at hrep
            split_ifs at hrep with hvx
            subst hvx
            rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
            simp only [ProbDist.single, fTransform_single, ProbStep.tagged,
              Distribution.single_restrict, ↓reduceIte]
          | none =>
            simp only [hlu] at hrep
            split_ifs at hrep with hcap
            rcases Prod.mk.inj (Option.some.inj hrep) with ⟨rfl, rfl⟩
            have hrec : recordInverseEdge table0 v u = table0 ++ [⟨v, u, true⟩] :=
              recordInverseEdge_eq_append_of_avoids p table0 hcap
            have huncomp := uncompletedRO_append_edge_of_no_new_completion p M encode
              table0 ro0 ⟨v, u, true⟩
              (fun m' h0 => by
                rw [← hrec]
                exact evalAbsorption_recordInverseEdge_none p M hp encode table0 hcap m' h0)
            dsimp only
            refine (uniform_map_transition_eq (A := A) (α := ByteState p.stateBytes) _
              (Sum.inr Bidirectional.Port.inverse) u v
              (fun x => (recordInverseEdge table0 x u, ro0))
              (fun x => x) v (fun _ => Iff.rfl)).trans ?_
            rw [hrec, huncomp, List.length_append, List.length_singleton, pow_succ]
            congr 1
            field_simp [hS_ne, hD_ne]

/-- Exact ideal transcript probability on every good transcript `h`. -/
theorem idealSponge_mass_of_replayGood (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    {table : List (PermutationEdge (ByteState p.stateBytes))}
    {ro : List (M × ByteState p.outputBytes)}
    (hrep : replayGoodIdeal p M spec q_pub h = some (table, ro)) :
    ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub).1 h =
      1 / ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
        (Fintype.card (ByteState p.outputBytes) : ℝ) ^
          (uncompletedRO p M encode table ro).length) := by
  rw [idealSponge_eq_lazy p M hp spec q_pub, TypedSystem.ofProbAutomaton_mass,
    idealLazyStep_belief_of_replayGood p M hp henc spec q_pub h hrep,
    Distribution.weight_smul, Distribution.weight_single, mul_one]

/-- Good submass function for `RatioCost`: retains the ideal mass on `replayGoodIdeal`-good
transcripts and zeroes out transcripts with a capacity collision. -/
noncomputable def goodIdealMass {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o))) : ℝ :=
  if (replayGoodIdeal p M spec q_pub h).isSome then
    ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
      sharedIdealRO p M spec q_pub).1 h
  else 0

/-- Step cost function paying `(2 * publicQueryCount h + 1) / |C|` on each public query. -/
noncomputable def spongeStepCost {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) : ℝ :=
  if xq.1.isRight then
    ((2 * publicQueryCount h + 1 : ℕ) : ℝ) /
      (Fintype.card (ByteState p.capacityBytes) : ℝ)
  else 0

/-- One-step good-mass loss bound for `goodIdealMass` against `spongeStepCost`. -/
lemma goodIdealMass_step_loss_le (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o)
    (hadm : (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain h xq) :
    goodIdealMass p M spec q_pub h -
        ∑ yq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o,
          goodIdealMass p M spec q_pub (h ++ [(xq, yq)]) ≤
      spongeStepCost p M spec q_pub h xq *
        ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
          sharedIdealRO p M spec q_pub).1 h := by
  classical
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  let Sid := (spec.toInterface ◁ spongeSimulator p M encode q_pub) •
    sharedIdealRO p M spec q_pub
  have hS_nonneg : 0 ≤ Sid.1 h := Sid.1.2.2.1 h
  have hcost_nonneg : 0 ≤ spongeStepCost p M spec q_pub h xq := by
    unfold spongeStepCost
    split_ifs
    · positivity
    · exact le_rfl
  cases hpre : replayGoodIdeal p M spec q_pub h with
  | none =>
    have h0 : goodIdealMass p M spec q_pub h = 0 := by
      simp only [goodIdealMass, hpre, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hsum0 : ∑ yq : Σ o, A.Y o, goodIdealMass p M spec q_pub (h ++ [(xq, yq)]) = 0 := by
      apply Finset.sum_eq_zero
      intro yq _
      unfold goodIdealMass
      rw [replayGoodIdeal_snoc, ite_eq_left hadm, hpre]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [h0, hsum0, sub_zero]
    exact mul_nonneg hcost_nonneg hS_nonneg
  | some st =>
    rcases st with ⟨table, ro⟩
    have inv := replayGoodIdeal_inv p M hp henc spec q_pub h hpre
    have hbel := idealLazyStep_belief_of_replayGood p M hp henc spec q_pub h hpre
    have hSh := idealSponge_mass_of_replayGood p M hp henc spec q_pub h hpre
    have hgh : goodIdealMass p M spec q_pub h = Sid.1 h := by
      simp only [goodIdealMass, hpre, Option.isSome_some, ↓reduceIte, Sid]
    have hsum_all : ∑ yq : Σ o, A.Y o, Sid.1 (h ++ [(xq, yq)]) = Sid.1 h := by
      rcases Sid.1.2.2.2 h xq with ⟨μ, hμ, hw⟩
      rw [ite_eq_left hadm] at hw
      rw [← hw, Distribution.weight_eq_sum_of_support_subset μ (Finset.subset_univ _)]
      exact Finset.sum_congr rfl fun yq _ => (hμ yq).symm
    have hdiff : goodIdealMass p M spec q_pub h -
        ∑ yq : Σ o, A.Y o, goodIdealMass p M spec q_pub (h ++ [(xq, yq)]) =
        ∑ yq : Σ o, A.Y o,
          if (replayGoodIdeal p M spec q_pub (h ++ [(xq, yq)])).isSome then 0
          else Sid.1 (h ++ [(xq, yq)]) := by
      rw [hgh, ← hsum_all, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro yq _
      simp only [goodIdealMass, Sid]
      split_ifs <;> ring
    rw [hdiff]
    have hstep_val : ∀ yq : Σ o, A.Y o,
        Sid.1 (h ++ [(xq, yq)]) =
          Sid.1 h * ((idealLazyStep p M spec q_pub (table, ro) xq.1 xq.2).1.mass
            fun sy => (⟨xq.1, sy.2⟩ : Σ o, A.Y o) = yq) := by
      intro yq
      have hSid : Sid = TypedSystem.ofProbAutomaton A (idealLazyStep p M spec q_pub)
          (ProbDist.single ([], [])) := idealSponge_eq_lazy p M hp spec q_pub
      have hSh' : Sid.1 h =
          1 / ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
            (Fintype.card (ByteState p.outputBytes) : ℝ) ^
              (uncompletedRO p M encode table ro).length) := hSh
      rw [hSh', hSid, TypedSystem.ofProbAutomaton_mass, ProbStep.belief_snoc, ite_eq_left hadm,
        hbel]
      simp only [ProbStep.transition, ProbStep.outcome, Finsupp.smul_single, smul_eq_mul,
        mul_one, bindK_single,
        Distribution.weight_smul, Distribution.weight_fTransform, Distribution.weight_restrict]
      congr 1
      rw [Distribution.mass_fTransform]
      rfl
    have hbad_le : ∀ (P : A.Y xq.1 → Prop),
        (∀ y : A.Y xq.1, ¬ P y →
          (replayGoodStep p M spec q_pub table ro xq ⟨xq.1, y⟩).isSome = true) →
        (∑ yq : Σ o, A.Y o,
          if (replayGoodIdeal p M spec q_pub (h ++ [(xq, yq)])).isSome then 0
          else Sid.1 (h ++ [(xq, yq)])) ≤
          Sid.1 h * ((idealLazyStep p M spec q_pub (table, ro) xq.1 xq.2).1.mass
            fun sy => P sy.2) := by
      intro P hgood
      have hterm : ∀ yq : Σ o, A.Y o,
          (if (replayGoodIdeal p M spec q_pub (h ++ [(xq, yq)])).isSome then 0
            else Sid.1 (h ++ [(xq, yq)])) ≤
          Sid.1 h * ((idealLazyStep p M spec q_pub (table, ro) xq.1 xq.2).1.mass
            fun sy => P sy.2 ∧ (⟨xq.1, sy.2⟩ : Σ o, A.Y o) = yq) := by
        intro yq
        rw [hstep_val yq]
        split_ifs with hsome
        · exact mul_nonneg hS_nonneg
            ((idealLazyStep p M spec q_pub (table, ro) xq.1 xq.2).2.1.mass_nonneg _)
        · apply mul_le_mul_of_nonneg_left _ hS_nonneg
          apply Distribution.mass_mono
            (idealLazyStep p M spec q_pub (table, ro) xq.1 xq.2).2.1
          intro sy heq
          refine ⟨?_, heq⟩
          by_contra hnp
          have hok := hgood sy.2 hnp
          have hsome' : (replayGoodIdeal p M spec q_pub (h ++ [(xq, yq)])).isSome = true := by
            rw [← heq, replayGoodIdeal_snoc, ite_eq_left hadm, hpre]
            exact hok
          exact hsome hsome'
      calc ∑ yq : Σ o, A.Y o,
            (if (replayGoodIdeal p M spec q_pub (h ++ [(xq, yq)])).isSome then 0
              else Sid.1 (h ++ [(xq, yq)]))
          ≤ ∑ yq : Σ o, A.Y o,
              Sid.1 h * ((idealLazyStep p M spec q_pub (table, ro) xq.1 xq.2).1.mass
                fun sy => P sy.2 ∧ (⟨xq.1, sy.2⟩ : Σ o, A.Y o) = yq) :=
            Finset.sum_le_sum fun yq _ => hterm yq
        _ = Sid.1 h * ∑ yq : Σ o, A.Y o,
              (idealLazyStep p M spec q_pub (table, ro) xq.1 xq.2).1.mass
                fun sy => P sy.2 ∧ (⟨xq.1, sy.2⟩ : Σ o, A.Y o) = yq := by
            rw [← Finset.mul_sum]
        _ = Sid.1 h * ((idealLazyStep p M spec q_pub (table, ro) xq.1 xq.2).1.mass
              fun sy => P sy.2) := by
            congr 1
            simp only [Distribution.mass, Finsupp.sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro sy _
            by_cases hP : P sy.2
            · simp only [hP, true_and, ↓reduceIte, Finset.sum_ite_eq, Finset.mem_univ]
            · simp only [hP, false_and, ↓reduceIte, Finset.sum_const_zero]
    have hcap_le : ((occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table).card :
      ℝ) /
          (Fintype.card (ByteState p.capacityBytes) : ℝ) ≤
        ((2 * publicQueryCount h + 1 : ℕ) : ℝ) /
          (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have hcard := occupiedCapacities_card_le (capacityPart p) (zeroState p.capacityBytes) table
      have hlen := inv.tableLenLe
      exact_mod_cast (hcard.trans (by omega : 2 * table.length + 1 ≤ 2 * publicQueryCount h + 1))
    rcases xq with ⟨o, u⟩
    rcases o with o | o
    · cases o
      have hcost0 : spongeStepCost p M spec q_pub h ⟨Sum.inl Evaluation.Port.eval, u⟩ = 0 := by
        simp only [spongeStepCost, Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte]
      rw [hcost0, zero_mul]
      cases hlu : ro.lookup u with
      | some d' =>
        refine (hbad_le (fun y => y ≠ d') (by
          intro y hnp
          have hy : y = d' := not_not.mp hnp
          simp only [replayGoodStep, hlu, hy, ↓reduceIte, Option.isSome_some])).trans ?_
        simp only [idealLazyStep, hlu, ProbDist.single, Distribution.mass, Finsupp.sum_single_index,
          ne_eq, not_true_eq_false, ↓reduceIte, mul_zero, le_refl]
      | none =>
        refine (hbad_le (fun _ => False) (by
          intro y _
          simp only [replayGoodStep, hlu, Option.isSome_some])).trans ?_
        rw [Distribution.mass_eq_zero_of_forall_not _ (fun _ h => h), mul_zero]
    · have hcostR : spongeStepCost p M spec q_pub h ⟨Sum.inr o, u⟩ =
          ((2 * publicQueryCount h + 1 : ℕ) : ℝ) /
            (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
        simp only [spongeStepCost, Sum.isRight_inr, ↓reduceIte]
      rw [hcostR, mul_comm]
      cases o with
      | forward =>
        cases hlu : lookupForwardEdge table u with
        | some y' =>
          refine (hbad_le (fun y => y ≠ y') (by
            intro y hnp
            have hy : y = y' := not_not.mp hnp
            simp only [replayGoodStep, hlu, hy, ↓reduceIte, Option.isSome_some])).trans ?_
          simp only [idealLazyStep, hlu, ProbDist.single, Distribution.mass,
            Finsupp.sum_single_index, ne_eq, not_true_eq_false, ↓reduceIte, mul_zero]
          exact mul_nonneg hS_nonneg (by positivity)
        | none =>
          cases hcm : completingMessage p encode table u with
          | some m =>
            cases hro : ro.lookup m with
            | some d =>
              refine (hbad_le (fun y =>
                capacityPart p y ∈ occupiedCapacities (capacityPart p)
                  (zeroState p.capacityBytes) table ∨ digestPart p y ≠ d) (by
                intro y hnp
                rw [not_or, not_ne_iff] at hnp
                simp only [replayGoodStep, hlu, hnp.1, not_false_eq_true, ↓reduceIte,
                  hcm, hro, hnp.2, Option.isSome_some])).trans ?_
              apply mul_le_mul_of_nonneg_left _ hS_nonneg
              simp only [idealLazyStep, hlu, hcm, hro, ProbDist.map_val,
                Distribution.mass_fTransform]
              have hcong :
                  (uniform (ByteState (tailBytes p))).mass (fun t =>
                    capacityPart p (assembleState p d t) ∈
                      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table ∨
                    digestPart p (assembleState p d t) ≠ d) =
                  (uniform (ByteState (tailBytes p))).mass (fun t =>
                    capacityPart p (assembleState p d t) ∈
                      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table) := by
                apply Distribution.mass_congr
                intro t
                rw [digestPart_assembleState p (hp.2.2.2.1.trans hp.2.1.le) d t]
                simp only [ne_eq, not_true_eq_false, or_false]
              change (uniform (ByteState (tailBytes p))).mass _ ≤ _
              rw [hcong, uniform_tail_mass_cap_mem p hp d]
              exact hcap_le
            | none =>
              refine (hbad_le (fun y =>
                capacityPart p y ∈ occupiedCapacities (capacityPart p)
                  (zeroState p.capacityBytes) table) (by
                intro y hnp
                simp only [replayGoodStep, hlu, hnp, not_false_eq_true, ↓reduceIte,
                  hcm, hro, Option.isSome_some])).trans ?_
              apply mul_le_mul_of_nonneg_left _ hS_nonneg
              simp only [idealLazyStep, hlu, hcm, hro, ProbDist.map_val,
                Distribution.mass_fTransform]
              change (uniform (ByteState p.stateBytes)).mass _ ≤ _
              rw [uniform_mass_cap_mem p hp]
              exact hcap_le
          | none =>
            refine (hbad_le (fun y =>
              capacityPart p y ∈ occupiedCapacities (capacityPart p)
                (zeroState p.capacityBytes) table) (by
              intro y hnp
              simp only [replayGoodStep, hlu, hnp, not_false_eq_true, ↓reduceIte,
                hcm, Option.isSome_some])).trans ?_
            apply mul_le_mul_of_nonneg_left _ hS_nonneg
            simp only [idealLazyStep, hlu, hcm, ProbDist.map_val, Distribution.mass_fTransform]
            change (uniform (ByteState p.stateBytes)).mass _ ≤ _
            rw [uniform_mass_cap_mem p hp]
            exact hcap_le
      | inverse =>
        cases hlu : lookupInverseEdge table u with
        | some x' =>
          refine (hbad_le (fun x => x ≠ x') (by
            intro x hnp
            have hx : x = x' := not_not.mp hnp
            simp only [replayGoodStep, hlu, hx, ↓reduceIte, Option.isSome_some])).trans ?_
          simp only [idealLazyStep, hlu, ProbDist.single, Distribution.mass,
            Finsupp.sum_single_index, ne_eq, not_true_eq_false, ↓reduceIte, mul_zero]
          exact mul_nonneg hS_nonneg (by positivity)
        | none =>
          refine (hbad_le (fun x =>
            capacityPart p x ∈ occupiedCapacities (capacityPart p)
              (zeroState p.capacityBytes) table) (by
            intro x hnp
            simp only [replayGoodStep, hlu, hnp, not_false_eq_true, ↓reduceIte,
              Option.isSome_some])).trans ?_
          apply mul_le_mul_of_nonneg_left _ hS_nonneg
          simp only [idealLazyStep, hlu, ProbDist.map_val, Distribution.mass_fTransform]
          change (uniform (ByteState p.stateBytes)).mass _ ≤ _
          rw [uniform_mass_cap_mem p hp]
          exact hcap_le

omit [DecidableEq M] in
/-- Exact closed form for the accumulated step cost: `(publicQueryCount h)^2 / |C|`. -/
lemma transcriptCost_spongeStepCost_eq {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o))) :
    SystemAlgebra.transcriptCost (spongeStepCost p M spec q_pub) h =
      ((publicQueryCount h : ℝ) ^ 2) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [SystemAlgebra.transcriptCost, publicQueryCount_nil, Nat.cast_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
  | append_singleton h z ih =>
    rcases z with ⟨xq, yq⟩
    rw [SystemAlgebra.transcriptCost_snoc, ih, publicQueryCount_snoc]
    unfold spongeStepCost
    cases xq.1 with
    | inl _ =>
      simp only [Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, add_zero]
    | inr _ =>
      simp only [Sum.isRight_inr, ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_one]
      ring

/-- Every admitted ideal transcript incurs total good-mass loss cost at most `q_pub^2 / |C|`. -/
lemma transcriptCost_spongeStepCost_le {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (hne : ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub).1 h ≠ 0) :
    SystemAlgebra.transcriptCost (spongeStepCost p M spec q_pub) h ≤
      ((q_pub : ℝ) ^ 2) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
  let Sid := (spec.toInterface ◁ spongeSimulator p M encode q_pub) •
    sharedIdealRO p M spec q_pub
  have hadm : h = [] ∨
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain (h.map Prod.fst) := by
    cases h with
    | nil => exact Or.inl rfl
    | cons z rest =>
      right
      by_contra hnd
      have h0 : Sid.1 (z :: rest) = 0 := by
        cases hrev : z :: rest using List.reverseRecOn with
        | nil => cases hrev
        | append_singleton pre last =>
          rw [hrev] at hnd
          have hnd' : ¬ (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain pre last.1 := by
            intro hd
            have hd' : (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain
                (pre.map Prod.fst ++ [last.1]) := hd
            exact hnd (by simpa only [List.map_append, List.map_singleton] using hd')
          rcases Sid.1.2.2.2 pre last.1 with ⟨μ, hμ, hw⟩
          rw [ite_eq_right hnd'] at hw
          have hnn : ∀ y, 0 ≤ μ y := fun y => by rw [hμ y]; exact Sid.1.2.2.1 _
          have hsum0 : ∑ y : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o, μ y = 0 := by
            rw [← Distribution.weight_eq_sum_of_support_subset μ (Finset.subset_univ _), hw]
          have hle0 : μ last.2 ≤ 0 := by
            calc μ last.2
                ≤ ∑ y : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o, μ y :=
                  Finset.single_le_sum (fun y _ => hnn y) (Finset.mem_univ last.2)
              _ = 0 := hsum0
          have hEq0 : μ last.2 = 0 := le_antisymm hle0 (hnn last.2)
          rw [← hμ last.2]
          exact hEq0
      exact hne h0
  rw [transcriptCost_spongeStepCost_eq]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hle : (publicQueryCount h : ℝ) ≤ (q_pub : ℝ) :=
    Nat.cast_le.mpr (publicQueryCount_le_bound p h hadm)
  nlinarith

/-! #### Real-mass extension lower bound on good transcripts -/

/-- Number of remaining blocks in `blocks` starting from `state` that are not yet covered by
forward edges in `table`. -/
def uncoveredBlockCount (table : List (PermutationEdge (ByteState p.stateBytes))) :
    ByteState p.stateBytes → List (ByteState p.rateBytes) → ℕ
  | _, [] => 0
  | state, b :: rest =>
    match lookupForwardEdge table (absorbBlock p state b) with
    | some next => uncoveredBlockCount table next rest
    | none => rest.length + 1

omit [Fintype M] [DecidableEq M] in
lemma uncoveredBlockCount_le_length (table : List (PermutationEdge (ByteState p.stateBytes)))
    (state : ByteState p.stateBytes) (blocks : List (ByteState p.rateBytes)) :
    uncoveredBlockCount p table state blocks ≤ blocks.length := by
  induction blocks generalizing state with
  | nil => exact le_rfl
  | cons b rest ih =>
    simp only [uncoveredBlockCount, List.length_cons]
    cases lookupForwardEdge table (absorbBlock p state b) with
    | none => exact le_rfl
    | some next => exact (ih next).trans (Nat.le_succ _)

omit [Fintype M] [DecidableEq M] in
lemma uncoveredBlockCount_mono (table ext : List (PermutationEdge (ByteState p.stateBytes)))
    (state : ByteState p.stateBytes) (blocks : List (ByteState p.rateBytes)) :
    uncoveredBlockCount p (table ++ ext) state blocks ≤
      uncoveredBlockCount p table state blocks := by
  induction blocks generalizing state with
  | nil => exact le_rfl
  | cons b rest ih =>
    simp only [uncoveredBlockCount]
    cases hl : lookupForwardEdge table (absorbBlock p state b) with
    | some next =>
      rw [lookupForwardEdge_append_of_some hl]
      exact ih next
    | none =>
      cases lookupForwardEdge (table ++ ext) (absorbBlock p state b) with
      | none => exact le_rfl
      | some next => exact (uncoveredBlockCount_le_length p (table ++
        ext) next rest).trans (Nat.le_succ _)

omit [Fintype M] [DecidableEq M] in
lemma splitUncovered_of_evalAbsorption_none
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (state : ByteState p.stateBytes) (blocks : List (ByteState p.rateBytes))
    (hnone : evalAbsorption p table state blocks = none) :
    ∃ (pref : List (ByteState p.rateBytes)) (b : ByteState p.rateBytes)
      (tail : List (ByteState p.rateBytes)) (s_cur : ByteState p.stateBytes),
      blocks = pref ++ b :: tail ∧
      evalAbsorption p table state pref = some s_cur ∧
      lookupForwardEdge table (absorbBlock p s_cur b) = none ∧
      uncoveredBlockCount p table state blocks = tail.length + 1 := by
  induction blocks generalizing state with
  | nil =>
    simp only [evalAbsorption, reduceCtorEq] at hnone
  | cons b rest ih =>
    simp only [evalAbsorption] at hnone
    cases hl : lookupForwardEdge table (absorbBlock p state b) with
    | none =>
      exact ⟨[], b, rest, state, rfl, rfl, hl, by simp only [uncoveredBlockCount, hl]⟩
    | some next =>
      rw [hl] at hnone
      rcases ih next hnone with ⟨pref, b', tail, s_cur, hbl, hev, hlu, hcnt⟩
      refine ⟨b :: pref, b', tail, s_cur, by rw [List.cons_append, ← hbl], ?_, hlu, ?_⟩
      · simp only [evalAbsorption, hl, hev]
      · simp only [uncoveredBlockCount, hl, hcnt]


omit [Fintype M] [DecidableEq M] in
lemma uncoveredBlockCount_step_nonfinal
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (pref : List (ByteState p.rateBytes)) (b b' : ByteState p.rateBytes)
    (tail' : List (ByteState p.rateBytes)) {s_cur y : ByteState p.stateBytes}
    (hev : evalAbsorption p table (zeroState p.stateBytes) pref = some s_cur)
    (hlu : lookupForwardEdge table (absorbBlock p s_cur b) = none)
    (hy : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table) :
    let table' := table ++ [⟨absorbBlock p s_cur b, y, false⟩]
    evalAbsorption p table' (zeroState p.stateBytes) (pref ++ b :: b' :: tail') = none ∧
      uncoveredBlockCount p table' (zeroState p.stateBytes) (pref ++ b :: b' :: tail') =
        tail'.length + 1 := by
  intro table'
  have hnext_none : lookupForwardEdge table' (absorbBlock p y b') = none := by
    rw [lookupForwardEdge_eq_none_iff]
    intro e he hEq
    have hcap_y : capacityPart p (absorbBlock p y b') = capacityPart p y :=
      capacityPart_absorbBlock p y b'
    rcases List.mem_append.mp he with he0 | he1
    · have hocc : capacityPart p e.input ∈
          occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table :=
        occupiedCapacities_input (capacityPart p) (zeroState p.capacityBytes) table he0
      rw [hEq, hcap_y] at hocc
      exact hy hocc
    · rw [List.mem_singleton.mp he1] at hEq
      have hcap_x : capacityPart p (absorbBlock p s_cur b) = capacityPart p s_cur :=
        capacityPart_absorbBlock p s_cur b
      have hcap_eq : capacityPart p s_cur = capacityPart p y := by
        rw [← hcap_x, ← hcap_y]
        exact congrArg (capacityPart p) hEq
      have hocc := capacityPart_mem_occupied_of_evalAbsorption p table pref hev
      rw [hcap_eq] at hocc
      exact hy hocc
  have hstep_lu : lookupForwardEdge table' (absorbBlock p s_cur b) = some y := by
    simp only [table', lookupForwardEdge_append_of_none hlu, lookupForwardEdge, ↓reduceIte]
  have hev_pref : evalAbsorption p table' (zeroState p.stateBytes) pref = some s_cur :=
    evalAbsorption_mono p hev
  constructor
  · rw [evalAbsorption_append, hev_pref]
    simp only [Option.bind_some, evalAbsorption, hstep_lu, hnext_none]
  · have haux : ∀ (st : ByteState p.stateBytes) (pr : List (ByteState p.rateBytes)),
        evalAbsorption p table' st pr = some s_cur →
        uncoveredBlockCount p table' st (pr ++ b :: b' :: tail') = tail'.length + 1 := by
      intro st pr hpr
      induction pr generalizing st with
      | nil =>
        simp only [evalAbsorption, Option.some.injEq] at hpr
        subst hpr
        simp only [List.nil_append, uncoveredBlockCount, hstep_lu, hnext_none]
      | cons c cs ih =>
        simp only [evalAbsorption] at hpr
        cases hc : lookupForwardEdge table' (absorbBlock p st c) with
        | none => rw [hc] at hpr; cases hpr
        | some mid =>
          rw [hc] at hpr
          simp only [List.cons_append, uncoveredBlockCount, hc]
          exact ih mid hpr
    exact haux (zeroState p.stateBytes) pref hev_pref

omit [Fintype M] [DecidableEq M] in
lemma evalAbsorption_step_final
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (pref : List (ByteState p.rateBytes)) (b : ByteState p.rateBytes)
    {s_cur y : ByteState p.stateBytes}
    (hev : evalAbsorption p table (zeroState p.stateBytes) pref = some s_cur)
    (hlu : lookupForwardEdge table (absorbBlock p s_cur b) = none) :
    evalAbsorption p (table ++ [⟨absorbBlock p s_cur b, y, false⟩])
      (zeroState p.stateBytes) (pref ++ [b]) = some y := by
  rw [evalAbsorption_append, evalAbsorption_mono p hev]
  simp only [Option.bind_some, evalAbsorption, lookupForwardEdge_append_of_none hlu,
    lookupForwardEdge, ↓reduceIte]

omit [Fintype M] [DecidableEq M] in
lemma other_still_uncompleted_of_step (hp : p.Valid)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs table))
    (hcf : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    (pref : List (ByteState p.rateBytes)) (b : ByteState p.rateBytes)
    (tail : List (ByteState p.rateBytes)) {s_cur y : ByteState p.stateBytes}
    (hev : evalAbsorption p table (zeroState p.stateBytes) pref = some s_cur)
    (hy : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table)
    (blocks' : List (ByteState p.rateBytes)) (hne : blocks' ≠ [])
    (hnone' : evalAbsorption p table (zeroState p.stateBytes) blocks' = none)
    (hord : (pref ++ b :: tail).length < blocks'.length ∨
      ((pref ++ b :: tail).length = blocks'.length ∧ blocks' ≠ pref ++ b :: tail)) :
    evalAbsorption p (table ++ [⟨absorbBlock p s_cur b, y, false⟩])
      (zeroState p.stateBytes) blocks' = none := by
  by_contra hsome
  cases hnew : evalAbsorption p (table ++ [⟨absorbBlock p s_cur b, y, false⟩])
      (zeroState p.stateBytes) blocks' with
  | none => exact hsome hnew
  | some out =>
    have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes) table
        ⟨absorbBlock p s_cur b, y, false⟩ := hy
    rcases no_preexisting_extension p table ⟨absorbBlock p s_cur b, y, false⟩ hf
        blocks' hne hnew hnone' with
      ⟨_, par', last', hsplit', hpar', habs', _⟩
    have hpar_eq : par' = s_cur ∧ last' = b := by
      have hcap_eq : capacityPart p par' = capacityPart p s_cur := by
        have h1 := capacityPart_absorbBlock p par' last'
        have h2 := capacityPart_absorbBlock p s_cur b
        rw [← h1, ← h2]
        exact congrArg (capacityPart p) habs'
      have hpar_eq' : par' = s_cur := by
        cases hdl : blocks'.dropLast with
        | nil =>
          rw [hdl] at hpar'
          simp only [evalAbsorption, Option.some.injEq] at hpar'
          subst hpar'
          cases pref with
          | nil =>
            simp only [evalAbsorption, Option.some.injEq] at hev
            exact hev
          | cons c cs =>
            have hmem := evalAbsorption_mem_forwardOutputs p table hcf (zeroState p.stateBytes)
              (Or.inl (capacityPart_zeroState p)) (c :: cs) (List.cons_ne_nil c cs) hev
            have hnz := hcf.2.1 s_cur hmem
            rw [← hcap_eq, capacityPart_zeroState] at hnz
            exact False.elim (hnz rfl)
        | cons c1 cs1 =>
          rw [hdl] at hpar'
          have hmem1 := evalAbsorption_mem_forwardOutputs p table hcf (zeroState p.stateBytes)
            (Or.inl (capacityPart_zeroState p)) (c1 :: cs1) (List.cons_ne_nil c1 cs1) hpar'
          cases pref with
          | nil =>
            simp only [evalAbsorption, Option.some.injEq] at hev
            subst hev
            have hnz := hcf.2.1 par' hmem1
            rw [hcap_eq, capacityPart_zeroState] at hnz
            exact False.elim (hnz rfl)
          | cons c2 cs2 =>
            have hmem2 := evalAbsorption_mem_forwardOutputs p table hcf (zeroState p.stateBytes)
              (Or.inl (capacityPart_zeroState p)) (c2 :: cs2) (List.cons_ne_nil c2 cs2) hev
            exact hcf.1 hmem1 hmem2 hcap_eq
      subst hpar_eq'
      exact ⟨rfl, absorbBlock_injective p hp.2.1.le par' habs'⟩
    rcases hpar_eq with ⟨rfl, rfl⟩
    have hpref_eq : blocks'.dropLast = pref :=
      blocks_eq_of_evalAbsorption_eq p hp table hpb hcf hpar' hev
    rw [hpref_eq] at hsplit'
    have hlen' : blocks'.length = pref.length + 1 := by
      rw [hsplit', List.length_append, List.length_singleton]
    rcases hord with hlt | ⟨heq_len, hne_bl⟩
    · simp only [List.length_append, List.length_cons] at hlt
      omega
    · simp only [List.length_append, List.length_cons] at heq_len
      have htail0 : tail.length = 0 := by omega
      have htail_nil : tail = [] := List.eq_nil_of_length_eq_zero htail0
      subst htail_nil
      exact hne_bl hsplit'

omit [Fintype M] [DecidableEq M] in
/-- Disjoint-choice mass sum bound for a single fresh permutation input `x`. -/
lemma mass_sum_disjoint_perm {S : Type} [Fintype S] [DecidableEq S]
    (x : S) (Y : Finset S) (P : S → Equiv.Perm S → Prop) (Q : Equiv.Perm S → Prop)
    (himp : ∀ y ∈ Y, ∀ π : Equiv.Perm S, P y π → π x = y ∧ Q π) :
    (∑ y ∈ Y, (uniform (Equiv.Perm S)).mass (P y)) ≤
      (uniform (Equiv.Perm S)).mass Q := by
  let _ : ∀ y π, Decidable (P y π) := fun _ _ => Classical.propDecidable _
  let _ : ∀ π, Decidable (Q π) := fun _ => Classical.propDecidable _
  simp only [Distribution.mass, Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro π _
  have hnn : 0 ≤ (uniform (Equiv.Perm S)) π := uniform_nonNeg π
  by_cases hQ : Q π
  · rw [ite_eq_left hQ]
    by_cases hex : ∃ y ∈ Y, P y π
    · rcases hex with ⟨y₀, hy₀, hPy₀⟩
      have huniq : ∀ y ∈ Y, y ≠ y₀ → (if P y π then (uniform (Equiv.Perm S)) π else 0) = 0 := by
        intro y hy hne
        have hnp : ¬ P y π := by
          intro hPy
          have h1 := (himp y hy π hPy).1
          have h2 := (himp y₀ hy₀ π hPy₀).1
          exact hne (h1.symm.trans h2)
        exact ite_eq_right hnp
      rw [Finset.sum_eq_single y₀ huniq (fun h => False.elim (h hy₀)), ite_eq_left hPy₀]
    · push Not at hex
      have h0 : ∑ y ∈ Y, (if P y π then (uniform (Equiv.Perm S)) π else 0) = 0 :=
        Finset.sum_eq_zero fun y hy => ite_eq_right (hex y hy)
      rw [h0]
      exact hnn
  · rw [ite_eq_right hQ]
    have h0 : ∑ y ∈ Y, (if P y π then (uniform (Equiv.Perm S)) π else 0) = 0 :=
      Finset.sum_eq_zero fun y hy => ite_eq_right fun hPy => hQ (himp y hy π hPy).2
    rw [h0]

omit [Fintype M] [DecidableEq M] in
/-- Base-case uniform permutation probability lower bound for a partial bijection table:
`1 / |S|^|table| ≤ Pr[π agrees with table]`. -/
lemma uniform_perm_mass_agrees_ge
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs table)) :
    1 / (Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length ≤
      (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (Agrees (toPairs table)) := by
  have hunif : ∀ (h₁ h₂ : Fintype (Equiv.Perm (ByteState p.stateBytes))),
      @uniform (Equiv.Perm (ByteState p.stateBytes)) h₁ _ =
        @uniform (Equiv.Perm (ByteState p.stateBytes)) h₂ _ := fun h₁ h₂ => by
    congr 1; exact Subsingleton.elim h₁ h₂
  have hbase := uniform_perm_mass_agrees_eq hpb
  rw [hunif _ inferInstance] at hbase
  rw [hbase, toPairs, List.length_map]
  have hlen : table.length ≤ Fintype.card (ByteState p.stateBytes) := by
    have h := Finset.card_le_univ ((toPairs table).map Prod.fst).toFinset
    rw [List.toFinset_card_of_nodup hpb.1, List.length_map, toPairs, List.length_map] at h
    exact h
  have hdesc_pos : (0 : ℝ) <
      ((Fintype.card (ByteState p.stateBytes)).descFactorial table.length : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hlen
  have hdesc_le : ((Fintype.card (ByteState p.stateBytes)).descFactorial table.length : ℝ) ≤
      (Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length := by
    exact_mod_cast Nat.descFactorial_le_pow (Fintype.card (ByteState p.stateBytes)) table.length
  exact one_div_le_one_div_of_le hdesc_pos hdesc_le

/-- Total uncovered blocks across all pending uncompleted messages. -/
def totalUncoveredBlocks (encode : M → List (BitVec 8))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (pending : List (M × ByteState p.outputBytes)) : ℕ :=
  (pending.map fun md =>
    uncoveredBlockCount p table (zeroState p.stateBytes) (paddedBlocks p (encode md.1))).sum

/-- Pending messages sorted by ascending padded block count. -/
def PendingSorted (encode : M → List (BitVec 8))
    (pending : List (M × ByteState p.outputBytes)) : Prop :=
  pending.Pairwise fun a b =>
    paddedBlockCount p (encode a.1).length ≤ paddedBlockCount p (encode b.1).length

omit [Fintype M] [DecidableEq M] in
lemma totalUncoveredBlocks_le_work (encode : M → List (BitVec 8))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (pending : List (M × ByteState p.outputBytes)) :
    totalUncoveredBlocks p M encode table pending ≤
      (pending.map fun md => paddedBlockCount p (encode md.1).length).sum := by
  induction pending with
  | nil => exact le_rfl
  | cons md rest ih =>
    simp only [totalUncoveredBlocks, List.map_cons, List.sum_cons] at ih ⊢
    have h1 := uncoveredBlockCount_le_length p table (zeroState p.stateBytes)
      (paddedBlocks p (encode md.1))
    rw [length_paddedBlocks] at h1
    exact Nat.add_le_add h1 ih

omit [Fintype M] [DecidableEq M] in
lemma totalUncoveredBlocks_mono (encode : M → List (BitVec 8))
    (table ext : List (PermutationEdge (ByteState p.stateBytes)))
    (pending : List (M × ByteState p.outputBytes)) :
    totalUncoveredBlocks p M encode (table ++ ext) pending ≤
      totalUncoveredBlocks p M encode table pending := by
  induction pending with
  | nil => exact le_rfl
  | cons md rest ih =>
    simp only [totalUncoveredBlocks, List.map_cons, List.sum_cons] at ih ⊢
    exact Nat.add_le_add (uncoveredBlockCount_mono p table ext _ _) ih

omit [Fintype M] [DecidableEq M] in
/-- Algebraic telescoping step for the real-mass extension lower bound. -/
lemma extension_step_ineq (k N occ C : ℕ) (hC : 0 < C) (hocc : occ ≤ 2 * k + 1)
    (hlt : (((k + (N + 1) : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2) < (C : ℝ)) :
    1 - ((((k + (N + 1) : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2) / (C : ℝ)) ≤
      ((C - occ : ℕ) : ℝ) / (C : ℝ) *
        (1 - ((((k + 1 + N : ℕ) : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) / (C : ℝ))) := by
  have hC_pos : (0 : ℝ) < (C : ℝ) := Nat.cast_pos.mpr hC
  have h2k_le : (2 * k + 1 : ℕ) ≤ (k + (N + 1)) ^ 2 - k ^ 2 := by
    have h1 : (k + 1) ^ 2 ≤ (k + (N + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
    omega
  have hocc_le_C : occ ≤ C := by
    have hlt' : ((k : ℝ) + (N + 1 : ℝ)) ^ 2 - (k : ℝ) ^ 2 < (C : ℝ) := by
      push_cast at hlt
      linarith
    have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hocc_r : (occ : ℝ) < (C : ℝ) := by
      have : (occ : ℝ) ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast hocc
      nlinarith
    exact le_of_lt (Nat.cast_lt.mp hocc_r)
  conv_rhs => rw [Nat.cast_sub hocc_le_C, sub_div, div_self (ne_of_gt hC_pos)]
  set a : ℝ := ((2 * k + 1 : ℕ) : ℝ) / (C : ℝ)
  set b : ℝ := ((((k + 1 + N : ℕ) : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) / (C : ℝ))
  have ha_nn : 0 ≤ a := by positivity
  have hb_nn : 0 ≤ b := by
    apply div_nonneg _ (le_of_lt hC_pos)
    have : ((k + 1 : ℕ) : ℝ) ≤ ((k + 1 + N : ℕ) : ℝ) := by push_cast; linarith
    nlinarith
  have hb_le1 : b ≤ 1 := by
    rw [div_le_one hC_pos]
    have hsum : (((k + 1 + N : ℕ) : ℝ) ^ 2 - ((k + 1 : ℕ) : ℝ) ^ 2) ≤
        (((k + (N + 1) : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2) := by
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      push_cast
      nlinarith
    linarith
  have hocc_le_a : (occ : ℝ) / (C : ℝ) ≤ a :=
    div_le_div_of_nonneg_right (by exact_mod_cast hocc) (le_of_lt hC_pos)
  have htel : a + b = ((((k + (N + 1) : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2) / (C : ℝ)) := by
    simp only [a, b]
    rw [← add_div]
    congr 1
    push_cast
    ring
  calc 1 - ((((k + (N + 1) : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2) / (C : ℝ))
      = 1 - (a + b) := by rw [htel]
    _ ≤ (1 - a) * (1 - b) := by
        nlinarith [mul_nonneg ha_nn hb_nn]
    _ ≤ (1 - (occ : ℝ) / (C : ℝ)) * (1 - b) :=
        mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr hb_le1)

omit [Fintype M] [DecidableEq M] in
/-- Inductive real-mass extension lower bound: extending a capacity-collision-free partial
bijection `table` to agree with ascending-sorted uncompleted pending messages loses at most
`((|table| + N)^2 - |table|^2) / |C|` relative to `1 / (|S|^|table| * |D|^|pending|)`. -/
theorem real_extension_mass_ge (hp : p.Valid) (encode : M → List (BitVec 8))
    (henc : Function.Injective encode) :
    ∀ (N : ℕ) (table : List (PermutationEdge (ByteState p.stateBytes)))
      (pending : List (M × ByteState p.outputBytes)),
      IsPartialBijection (toPairs table) →
      CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table →
      (pending.map Prod.fst).Nodup →
      PendingSorted p M encode pending →
      (∀ md ∈ pending,
        evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode md.1)) = none) →
      totalUncoveredBlocks p M encode table pending ≤ N →
      (1 - ((((table.length + N : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) /
          (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
        ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
          (Fintype.card (ByteState p.outputBytes) : ℝ) ^ pending.length) ≤
      (uniform (Equiv.Perm (ByteState p.stateBytes))).mass fun π =>
        Agrees (toPairs table) π ∧
          ∀ md ∈ pending, spongeHash p π (encode md.1) = md.2 := by
  intro N
  have hS_pos : (0 : ℝ) < (Fintype.card (ByteState p.stateBytes) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hD_pos : (0 : ℝ) < (Fintype.card (ByteState p.outputBytes) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC_pos : 0 < Fintype.card (ByteState p.capacityBytes) := Fintype.card_pos
  have hC_posR : (0 : ℝ) < (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
    Nat.cast_pos.mpr hC_pos
  have hSRC : (Fintype.card (ByteState p.stateBytes) : ℝ) =
      (Fintype.card (ByteState p.rateBytes) : ℝ) *
        (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
    exact_mod_cast card_state_eq_rate_mul_cap p hp
  have hSDMC : (Fintype.card (ByteState p.stateBytes) : ℝ) =
      (Fintype.card (ByteState p.outputBytes) : ℝ) *
        (Fintype.card (ByteState (middleBytes p)) : ℝ) *
        (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
    have h := card_state_eq_three p hp
    have h' : (Fintype.card (ByteState p.stateBytes) : ℝ) =
        (Fintype.card (ByteState p.outputBytes) : ℝ) *
          ((Fintype.card (ByteState (middleBytes p)) : ℝ) *
            (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by exact_mod_cast h
    linarith
  induction N with
  | zero =>
    intro table pending hpb _ _ _ huncomp hN
    cases pending with
    | nil =>
      simp only [List.length_nil, add_zero, sub_self, zero_div, sub_zero, pow_zero, mul_one,
        List.not_mem_nil, false_implies, implies_true, and_true]
      exact uniform_perm_mass_agrees_ge p table hpb
    | cons md rest =>
      have hnone := huncomp md (List.mem_cons_self ..)
      rcases splitUncovered_of_evalAbsorption_none p table (zeroState p.stateBytes)
          (paddedBlocks p (encode md.1)) hnone with ⟨_, _, tail, _, _, _, _, hcnt⟩
      simp only [totalUncoveredBlocks, List.map_cons, List.sum_cons, hcnt] at hN
      omega
  | succ N ih =>
    intro table pending hpb hcf hnodup hsorted huncomp hN
    cases pending with
    | nil =>
      simp only [List.length_nil, pow_zero, mul_one, List.not_mem_nil, false_implies,
        implies_true, and_true]
      refine le_trans ?_ (uniform_perm_mass_agrees_ge p table hpb)
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hnn : 0 ≤ ((((table.length + (N + 1) : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) /
          (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
        apply div_nonneg _ (le_of_lt hC_posR)
        have : (table.length : ℝ) ≤ ((table.length + (N + 1) : ℕ) : ℝ) := by
          push_cast; linarith
        nlinarith
      linarith
    | cons md rest =>
      rcases md with ⟨m, d⟩
      by_cases htriv : (Fintype.card (ByteState p.capacityBytes) : ℝ) ≤
          (((table.length + (N + 1) : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2)
      · have hle0 : (1 - ((((table.length + (N + 1) : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) /
            (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
            ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
              (Fintype.card (ByteState p.outputBytes) : ℝ) ^ ((m, d) :: rest).length) ≤ 0 := by
          apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
          have hge1 : 1 ≤ (((table.length + (N + 1) : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) /
              (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
            (one_le_div hC_posR).mpr htriv
          linarith
        exact hle0.trans (uniform_nonNeg.mass_nonneg _)
      · push Not at htriv
        have hnone_m := huncomp (m, d) (List.mem_cons_self ..)
        rcases splitUncovered_of_evalAbsorption_none p table (zeroState p.stateBytes)
            (paddedBlocks p (encode m)) hnone_m with
          ⟨pref, b, tail, s_cur, hsplit, hpar, hlu, hcnt⟩
        set x : ByteState p.stateBytes := absorbBlock p s_cur b
        have hx_not : x ∉ (toPairs table).map Prod.fst := by
          have hnf := (lookupForwardEdge_eq_none_iff table x).mp hlu
          intro hmem
          rcases List.mem_map.mp hmem with ⟨⟨a, c⟩, hac, rfl⟩
          rcases List.mem_map.mp hac with ⟨e, he, hpe⟩
          exact hnf e he (congrArg Prod.fst hpe)
        simp only [List.map_cons, List.nodup_cons] at hnodup
        simp only [PendingSorted, List.pairwise_cons] at hsorted
        have hocc_le := occupiedCapacities_card_le (capacityPart p)
          (zeroState p.capacityBytes) table
        set occ := occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table
        have hrest_uncomp : ∀ y : ByteState p.stateBytes,
            capacityPart p y ∉ occ →
            ∀ md' ∈ rest,
              evalAbsorption p (table ++ [⟨x, y, false⟩]) (zeroState p.stateBytes)
                (paddedBlocks p (encode md'.1)) = none := by
          intro y hy md' hmd'
          have hnone' := huncomp md' (List.mem_cons_of_mem _ hmd')
          have hlen_le : (pref ++ b :: tail).length ≤ (paddedBlocks p (encode md'.1)).length := by
            rw [← hsplit, length_paddedBlocks, length_paddedBlocks]
            exact hsorted.1 md' hmd'
          have hne_m : md'.1 ≠ m := fun heq =>
            hnodup.1 (List.mem_map.mpr ⟨md', hmd', heq⟩)
          have hne_bl : paddedBlocks p (encode md'.1) ≠ pref ++ b :: tail := by
            rw [← hsplit]
            intro hEq
            exact hne_m (henc (paddedBlocks_injective p hp.1 hp.2.2.2.2.1 hp.2.2.2.2.2 hEq))
          have hord : (pref ++ b :: tail).length < (paddedBlocks p (encode md'.1)).length ∨
              ((pref ++ b :: tail).length = (paddedBlocks p (encode md'.1)).length ∧
                paddedBlocks p (encode md'.1) ≠ pref ++ b :: tail) := by
            rcases lt_or_eq_of_le hlen_le with hlt | heq
            · exact Or.inl hlt
            · exact Or.inr ⟨heq, hne_bl⟩
          exact other_still_uncompleted_of_step p hp table hpb hcf pref b tail hpar hy
            (paddedBlocks p (encode md'.1)) (paddedBlocks_ne_nil p hp.1 (encode md'.1)) hnone' hord
        have hpb_ext : ∀ y : ByteState p.stateBytes, capacityPart p y ∉ occ →
            IsPartialBijection (toPairs (table ++ [⟨x, y, false⟩])) := by
          intro y hy
          have hy_not : y ∉ (toPairs table).map Prod.snd := by
            have hnf := output_not_mem_of_avoidsOccupied (capacityPart p)
              (zeroState p.capacityBytes) table (x := x) (y := y) hy
            simpa only [toPairs, List.map_map, Function.comp_def] using hnf
          rw [toPairs, List.map_append, List.map_singleton]
          exact isPartialBijection_append hpb hx_not hy_not
        have hcf_ext : ∀ y : ByteState p.stateBytes, capacityPart p y ∉ occ →
            CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes)
              (table ++ [⟨x, y, false⟩]) := fun y hy =>
          capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
            table hcf ⟨x, y, false⟩ hy
        cases tail with
        | nil =>
          -- Final block of `m`: constrain `digestPart p y = d` and `capacityPart p y ∉ occ`.
          let Ygood : Finset (ByteState p.stateBytes) :=
            Finset.univ.filter fun y => digestPart p y = d ∧ capacityPart p y ∉ occ
          have hcardY : Ygood.card =
              (Fintype.card (ByteState p.capacityBytes) - occ.card) *
                Fintype.card (ByteState (middleBytes p)) :=
            card_filter_digest_and_avoid_cap p hp d occ
          have hsum_le :
              ∑ y ∈ Ygood,
                (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
                  Agrees (toPairs (table ++ [⟨x, y, false⟩])) π ∧
                    ∀ md' ∈ rest, spongeHash p π (encode md'.1) = md'.2) ≤
              (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
                Agrees (toPairs table) π ∧
                  ∀ md' ∈ (m, d) :: rest, spongeHash p π (encode md'.1) = md'.2) := by
            apply mass_sum_disjoint_perm x Ygood
            intro y hy π ⟨hag, hrest_π⟩
            have hy' := (Finset.mem_filter.mp hy).2
            have hag_xy : π x = y := hag (x, y) (by
              rw [toPairs, List.map_append, List.map_singleton]
              exact List.mem_append_right _ (List.mem_singleton_self _))
            have hag0 : Agrees (toPairs table) π := fun ab hab =>
              hag ab (by rw [toPairs, List.map_append]; exact List.mem_append_left _ hab)
            have hm_hash : spongeHash p π (encode m) = d := by
              have hev_m := evalAbsorption_step_final p table pref b hpar hlu (y := y)
              rw [← hsplit] at hev_m
              have habs_eq := evalAbsorption_eq_absorbBlocks p (table ++ [⟨x, y, false⟩]) π
                (fun e he => hag (e.input, e.output) (List.mem_map.mpr ⟨e, he, rfl⟩))
                (zeroState p.stateBytes) y (paddedBlocks p (encode m)) hev_m
              change digestPart p (absorbBlocks (absorbBlock p) π (zeroState p.stateBytes)
                (paddedBlocks p (encode m))) = d
              rw [habs_eq, hy'.1]
            refine ⟨hag_xy, hag0, fun md' hmd' => ?_⟩
            rcases List.mem_cons.mp hmd' with rfl | htl
            · exact hm_hash
            · exact hrest_π md' htl
          have hih_each : ∀ y ∈ Ygood,
              (1 - ((((table.length + 1 + N : ℕ) : ℝ) ^ 2 - ((table.length + 1 : ℕ) : ℝ) ^ 2) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
                ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ (table.length + 1) *
                  (Fintype.card (ByteState p.outputBytes) : ℝ) ^ rest.length) ≤
              (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
                Agrees (toPairs (table ++ [⟨x, y, false⟩])) π ∧
                  ∀ md' ∈ rest, spongeHash p π (encode md'.1) = md'.2) := by
            intro y hy
            have hcap_y : capacityPart p y ∉ occ := (Finset.mem_filter.mp hy).2.2
            have hN_rest : totalUncoveredBlocks p M encode (table ++ [⟨x, y, false⟩]) rest ≤ N := by
              have hmono := totalUncoveredBlocks_mono p M encode table [⟨x, y, false⟩] rest
              simp only [totalUncoveredBlocks, List.map_cons, List.sum_cons, hcnt,
                List.length_nil] at hN hmono ⊢
              omega
            have hstep := ih (table ++ [⟨x, y, false⟩]) rest (hpb_ext y hcap_y)
              (hcf_ext y hcap_y) hnodup.2 hsorted.2 (hrest_uncomp y hcap_y) hN_rest
            simpa only [List.length_append, List.length_singleton] using hstep
          have htel := extension_step_ineq table.length N occ.card
            (Fintype.card (ByteState p.capacityBytes)) hC_pos hocc_le htriv
          calc (1 - ((((table.length + (N + 1) : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
                ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
                  (Fintype.card (ByteState p.outputBytes) : ℝ) ^ ((m, d) :: rest).length)
              ≤ (((Fintype.card (ByteState p.capacityBytes) - occ.card : ℕ) : ℝ) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ) *
                  (1 - ((((table.length + 1 + N : ℕ) : ℝ) ^ 2 -
                      ((table.length + 1 : ℕ) : ℝ) ^ 2) /
                    (Fintype.card (ByteState p.capacityBytes) : ℝ)))) /
                ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
                  (Fintype.card (ByteState p.outputBytes) : ℝ) ^ ((m, d) :: rest).length) :=
                div_le_div_of_nonneg_right htel (by positivity)
            _ = (Ygood.card : ℝ) *
                  ((1 - ((((table.length + 1 + N : ℕ) : ℝ) ^ 2 -
                      ((table.length + 1 : ℕ) : ℝ) ^ 2) /
                    (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
                  ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ (table.length + 1) *
                    (Fintype.card (ByteState p.outputBytes) : ℝ) ^ rest.length)) := by
                rw [hcardY, Nat.cast_mul, List.length_cons, pow_succ, pow_succ]
                have hS_ne := ne_of_gt hS_pos
                have hD_ne := ne_of_gt hD_pos
                have hC_ne := ne_of_gt hC_posR
                have hM_ne : (Fintype.card (ByteState (middleBytes p)) : ℝ) ≠ 0 :=
                  Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ByteState (middleBytes p)))
                field_simp [hS_ne, hD_ne, hC_ne]
                rw [hSDMC]
                ring
            _ = ∑ _y ∈ Ygood,
                  (1 - ((((table.length + 1 + N : ℕ) : ℝ) ^ 2 -
                      ((table.length + 1 : ℕ) : ℝ) ^ 2) /
                    (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
                  ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ (table.length + 1) *
                    (Fintype.card (ByteState p.outputBytes) : ℝ) ^ rest.length) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ y ∈ Ygood,
                  (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
                    Agrees (toPairs (table ++ [⟨x, y, false⟩])) π ∧
                      ∀ md' ∈ rest, spongeHash p π (encode md'.1) = md'.2) :=
                Finset.sum_le_sum hih_each
            _ ≤ _ := hsum_le
        | cons b' tail' =>
          -- Non-final block of `m`: constrain `capacityPart p y ∉ occ`.
          let Ygood : Finset (ByteState p.stateBytes) :=
            Finset.univ.filter fun y => capacityPart p y ∉ occ
          have hcardY : Ygood.card =
              (Fintype.card (ByteState p.capacityBytes) - occ.card) *
                Fintype.card (ByteState p.rateBytes) :=
            card_filter_avoid_cap p hp occ
          have hsum_le :
              ∑ y ∈ Ygood,
                (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
                  Agrees (toPairs (table ++ [⟨x, y, false⟩])) π ∧
                    ∀ md' ∈ (m, d) :: rest, spongeHash p π (encode md'.1) = md'.2) ≤
              (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
                Agrees (toPairs table) π ∧
                  ∀ md' ∈ (m, d) :: rest, spongeHash p π (encode md'.1) = md'.2) := by
            apply mass_sum_disjoint_perm x Ygood
            intro y _ π ⟨hag, hall_π⟩
            have hag_xy : π x = y := hag (x, y) (by
              rw [toPairs, List.map_append, List.map_singleton]
              exact List.mem_append_right _ (List.mem_singleton_self _))
            have hag0 : Agrees (toPairs table) π := fun ab hab =>
              hag ab (by rw [toPairs, List.map_append]; exact List.mem_append_left _ hab)
            exact ⟨hag_xy, hag0, hall_π⟩
          have hih_each : ∀ y ∈ Ygood,
              (1 - ((((table.length + 1 + N : ℕ) : ℝ) ^ 2 - ((table.length + 1 : ℕ) : ℝ) ^ 2) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
                ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ (table.length + 1) *
                  (Fintype.card (ByteState p.outputBytes) : ℝ) ^ ((m, d) :: rest).length) ≤
              (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
                Agrees (toPairs (table ++ [⟨x, y, false⟩])) π ∧
                  ∀ md' ∈ (m, d) :: rest, spongeHash p π (encode md'.1) = md'.2) := by
            intro y hy
            have hcap_y : capacityPart p y ∉ occ := (Finset.mem_filter.mp hy).2
            have hnf := uncoveredBlockCount_step_nonfinal p table pref b b' tail' hpar hlu hcap_y
            have huncomp' : ∀ md' ∈ (m, d) :: rest,
                evalAbsorption p (table ++ [⟨x, y, false⟩]) (zeroState p.stateBytes)
                  (paddedBlocks p (encode md'.1)) = none := by
              intro md' hmd'
              rcases List.mem_cons.mp hmd' with rfl | htl
              · rw [hsplit]; exact hnf.1
              · exact hrest_uncomp y hcap_y md' htl
            have hN' : totalUncoveredBlocks p M encode (table ++ [⟨x, y, false⟩])
                ((m, d) :: rest) ≤ N := by
              have hmono := totalUncoveredBlocks_mono p M encode table [⟨x, y, false⟩] rest
              simp only [totalUncoveredBlocks, List.map_cons, List.sum_cons] at hN hmono ⊢
              rw [hsplit, hnf.2]
              rw [hcnt, List.length_cons] at hN
              omega
            have hstep := ih (table ++ [⟨x, y, false⟩]) ((m, d) :: rest) (hpb_ext y hcap_y)
              (hcf_ext y hcap_y) (by simp only [List.map_cons, List.nodup_cons]; exact hnodup)
              (by simp only [PendingSorted, List.pairwise_cons]; exact hsorted)
              huncomp' hN'
            simpa only [List.length_append, List.length_singleton] using hstep
          have htel := extension_step_ineq table.length N occ.card
            (Fintype.card (ByteState p.capacityBytes)) hC_pos hocc_le htriv
          calc (1 - ((((table.length + (N + 1) : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
                ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
                  (Fintype.card (ByteState p.outputBytes) : ℝ) ^ ((m, d) :: rest).length)
              ≤ (((Fintype.card (ByteState p.capacityBytes) - occ.card : ℕ) : ℝ) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ) *
                  (1 - ((((table.length + 1 + N : ℕ) : ℝ) ^ 2 -
                      ((table.length + 1 : ℕ) : ℝ) ^ 2) /
                    (Fintype.card (ByteState p.capacityBytes) : ℝ)))) /
                ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
                  (Fintype.card (ByteState p.outputBytes) : ℝ) ^ ((m, d) :: rest).length) :=
                div_le_div_of_nonneg_right htel (by positivity)
            _ = (Ygood.card : ℝ) *
                  ((1 - ((((table.length + 1 + N : ℕ) : ℝ) ^ 2 -
                      ((table.length + 1 : ℕ) : ℝ) ^ 2) /
                    (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
                  ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ (table.length + 1) *
                    (Fintype.card (ByteState p.outputBytes) : ℝ) ^ ((m, d) :: rest).length)) := by
                rw [hcardY, Nat.cast_mul, pow_succ]
                have hS_ne := ne_of_gt hS_pos
                have hD_ne := ne_of_gt hD_pos
                have hC_ne := ne_of_gt hC_posR
                field_simp [hS_ne, hD_ne, hC_ne]
                rw [hSRC]
                ring
            _ = ∑ _y ∈ Ygood,
                  (1 - ((((table.length + 1 + N : ℕ) : ℝ) ^ 2 -
                      ((table.length + 1 : ℕ) : ℝ) ^ 2) /
                    (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
                  ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ (table.length + 1) *
                    (Fintype.card (ByteState p.outputBytes) : ℝ) ^ ((m, d) :: rest).length) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ ∑ y ∈ Ygood,
                  (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
                    Agrees (toPairs (table ++ [⟨x, y, false⟩])) π ∧
                      ∀ md' ∈ (m, d) :: rest, spongeHash p π (encode md'.1) = md'.2) :=
                Finset.sum_le_sum hih_each
            _ ≤ _ := hsum_le

/-- Pointwise real-to-ideal ratio lower bound on every transcript `h`:
`(1 - ((w + q_pub)^2 - q_pub^2) / |C|) * goodIdealMass h ≤ realMass h`. -/
lemma sponge_good_ratio_le (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o))) :
    (1 - ((((w + q_pub : ℕ) : ℝ) ^ 2 - (q_pub : ℝ) ^ 2) /
        (Fintype.card (ByteState p.capacityBytes) : ℝ))) *
      goodIdealMass p M spec q_pub h ≤
    (spongePublic p M spec q_pub •
      StrongURP (ByteState p.stateBytes) (q := w + q_pub)).1 h := by
  let R := spongePublic p M spec q_pub •
    StrongURP (ByteState p.stateBytes) (q := w + q_pub)
  cases hrep : replayGoodIdeal p M spec q_pub h with
  | none =>
    simp only [goodIdealMass, hrep, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, mul_zero]
    exact R.1.2.2.1 h
  | some st =>
    rcases st with ⟨table, ro⟩
    have inv := replayGoodIdeal_inv p M hp henc spec q_pub h hrep
    have hSh := idealSponge_mass_of_replayGood p M hp henc spec q_pub h hrep
    have hgh : goodIdealMass p M spec q_pub h =
        1 / ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
          (Fintype.card (ByteState p.outputBytes) : ℝ) ^
            (uncompletedRO p M encode table ro).length) := by
      simp only [goodIdealMass, hrep, Option.isSome_some, ↓reduceIte]
      exact hSh
    rw [hgh, spongePublic_smul_strongURP_mass p M spec q_pub h inv.admitted]
    let leBlk : M × ByteState p.outputBytes → M × ByteState p.outputBytes → Bool :=
      fun a b => decide (paddedBlockCount p (encode a.1).length ≤
        paddedBlockCount p (encode b.1).length)
    let pending := (uncompletedRO p M encode table ro).mergeSort leBlk
    have hperm : pending.Perm (uncompletedRO p M encode table ro) :=
      List.mergeSort_perm _ _
    have hsorted : PendingSorted p M encode pending := by
      have hp := List.pairwise_mergeSort (le := leBlk)
        (fun a b c hab hbc => decide_eq_true ((of_decide_eq_true hab).trans (of_decide_eq_true
          hbc)))
        (fun a b => by
          simp only [leBlk, Bool.or_eq_true, decide_eq_true_eq]
          exact le_total _ _)
        (uncompletedRO p M encode table ro)
      exact hp.imp fun h => of_decide_eq_true h
    have hnodup_p : (pending.map Prod.fst).Nodup := by
      have hnodup_u : ((uncompletedRO p M encode table ro).map Prod.fst).Nodup :=
        inv.roNodup.sublist (List.Sublist.map Prod.fst List.filter_sublist)
      exact (List.Perm.nodup_iff (hperm.map Prod.fst)).mpr hnodup_u
    have huncomp_p : ∀ md ∈ pending,
        evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode md.1)) = none := by
      intro md hmd
      have hmem := hperm.mem_iff.mp hmd
      have hfilt := (List.mem_filter.mp hmem).2
      exact Option.isNone_iff_eq_none.mp hfilt
    have hwork_p : totalUncoveredBlocks p M encode table pending ≤ w := by
      calc totalUncoveredBlocks p M encode table pending
          ≤ (pending.map fun md => paddedBlockCount p (encode md.1).length).sum :=
            totalUncoveredBlocks_le_work p M encode table pending
        _ = ((uncompletedRO p M encode table ro).map fun md =>
              paddedBlockCount p (encode md.1).length).sum :=
            (hperm.map _).sum_eq
        _ ≤ w := uncompletedRO_work_le p M hp henc spec q_pub h hrep
    have hlen_p : pending.length = (uncompletedRO p M encode table ro).length := hperm.length_eq
    have hext := real_extension_mass_ge p M hp encode henc w table pending inv.partialBij
      inv.capFree hnodup_p hsorted huncomp_p hwork_p
    rw [hlen_p] at hext
    have hmass_le :
        (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
          Agrees (toPairs table) π ∧
            ∀ md ∈ pending, spongeHash p π (encode md.1) = md.2) ≤
        (uniform (Equiv.Perm (ByteState p.stateBytes))).mass (fun π =>
          ∀ z ∈ h, spongeRealAnswer p M spec q_pub π z.1 = z.2) := by
      apply Distribution.mass_mono uniform_nonNeg
      intro π ⟨hag, hpend⟩ z hz
      have hrec := inv.pubRecorded z hz
      rcases z with ⟨⟨o, u⟩, ⟨o', v⟩⟩
      rcases o with o | o <;> rcases o' with o' | o'
      · cases o; cases o'
        dsimp only at hrec
        simp only [spongeRealAnswer, Sigma.mk.inj_iff, heq_eq_eq, true_and]
        cases hev : evalAbsorption p table (zeroState p.stateBytes)
            (paddedBlocks p (encode u)) with
        | some s =>
          have hdig := inv.completedInRO u s hev
          rw [hdig] at hrec
          have hd_eq : digestPart p s = v := Option.some.inj hrec
          have habs := evalAbsorption_eq_absorbBlocks p table π
            (fun e he => hag (e.input, e.output) (List.mem_map.mpr ⟨e, he, rfl⟩))
            (zeroState p.stateBytes) s (paddedBlocks p (encode u)) hev
          change digestPart p (absorbBlocks (absorbBlock p) π (zeroState p.stateBytes)
            (paddedBlocks p (encode u))) = v
          rw [habs, hd_eq]
        | none =>
          have hmem_ro : (u, v) ∈ ro := (lookup_mem_of_nodup inv.roNodup).mp hrec
          have hmem_u : (u, v) ∈ uncompletedRO p M encode table ro :=
            List.mem_filter.mpr ⟨hmem_ro, by rw [hev]; rfl⟩
          exact hpend (u, v) (hperm.mem_iff.mpr hmem_u)
      · cases o; cases o' <;> exact False.elim hrec
      · cases o <;> cases o' <;> exact False.elim hrec
      · cases o <;> cases o'
        · dsimp only at hrec
          simp only [spongeRealAnswer, Sigma.mk.inj_iff, heq_eq_eq, true_and]
          exact hag (u, v) hrec
        · exact False.elim hrec
        · exact False.elim hrec
        · dsimp only at hrec
          simp only [spongeRealAnswer, Sigma.mk.inj_iff, heq_eq_eq, true_and]
          have hxy : π v = u := hag (v, u) hrec
          rw [← hxy, Equiv.symm_apply_apply]
    have htbl_le : table.length ≤ q_pub :=
      inv.tableLenLe.trans (publicQueryCount_le_bound p h inv.admitted)
    have herr_le : (((table.length + w : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) ≤
        (((w + q_pub : ℕ) : ℝ) ^ 2 - (q_pub : ℝ) ^ 2) := by
      have hkq : (table.length : ℝ) ≤ (q_pub : ℝ) := Nat.cast_le.mpr htbl_le
      have hw_nn : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
      push_cast
      nlinarith
    have hC_nn : (0 : ℝ) ≤ (Fintype.card (ByteState p.capacityBytes) : ℝ) := Nat.cast_nonneg _
    have h1_le :
        (1 - ((((w + q_pub : ℕ) : ℝ) ^ 2 - (q_pub : ℝ) ^ 2) /
            (Fintype.card (ByteState p.capacityBytes) : ℝ))) ≤
        (1 - ((((table.length + w : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) /
            (Fintype.card (ByteState p.capacityBytes) : ℝ))) := by
      have hdiv := div_le_div_of_nonneg_right herr_le hC_nn
      linarith
    calc (1 - ((((w + q_pub : ℕ) : ℝ) ^ 2 - (q_pub : ℝ) ^ 2) /
            (Fintype.card (ByteState p.capacityBytes) : ℝ))) *
          (1 / ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
            (Fintype.card (ByteState p.outputBytes) : ℝ) ^
              (uncompletedRO p M encode table ro).length))
        = (1 - ((((w + q_pub : ℕ) : ℝ) ^ 2 - (q_pub : ℝ) ^ 2) /
            (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
          ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
            (Fintype.card (ByteState p.outputBytes) : ℝ) ^
              (uncompletedRO p M encode table ro).length) := by ring
      _ ≤ (1 - ((((table.length + w : ℕ) : ℝ) ^ 2 - (table.length : ℝ) ^ 2) /
            (Fintype.card (ByteState p.capacityBytes) : ℝ))) /
          ((Fintype.card (ByteState p.stateBytes) : ℝ) ^ table.length *
            (Fintype.card (ByteState p.outputBytes) : ℝ) ^
              (uncompletedRO p M encode table ro).length) :=
          div_le_div_of_nonneg_right h1_le (by positivity)
      _ ≤ _ := hext.trans hmass_le

/-- **Path B (Direct 1-hop H-coefficient theorem via `RatioCost`)**:
the single-squeeze sponge [1, §2] over `StrongURP` is statistically indifferentiable from the
shared random oracle `sharedIdealRO` via `spongeSimulator`, with exact capacity-collision error
`Q^2 / |C|` (where `Q = w + q_pub`). -/
theorem sponge_indifferentiability_hCoefficient_tight (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      ENNReal.ofReal (((w + q_pub : ℕ) : ℝ) ^ 2 /
        (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
  let R := spongePublic p M spec q_pub •
    StrongURP (ByteState p.stateBytes) (q := w + q_pub)
  let Sid := (spec.toInterface ◁ spongeSimulator p M encode q_pub) •
    sharedIdealRO p M spec q_pub
  have herr1_nn : 0 ≤ ((((w + q_pub : ℕ) : ℝ) ^ 2 - (q_pub : ℝ) ^ 2) /
      (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    have : (q_pub : ℝ) ≤ ((w + q_pub : ℕ) : ℝ) := by push_cast; linarith
    nlinarith
  have herr2_nn : 0 ≤ ((q_pub : ℝ) ^ 2 /
      (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by positivity
  let e1 : NNReal := ⟨_, herr1_nn⟩
  let e2 : NNReal := ⟨_, herr2_nn⟩
  have hdist := RandomSystem.transcriptDistance_le_add_of_ratio_and_transcriptCost
    R.2 Sid.2 (g := goodIdealMass p M spec q_pub) (error₁ := e1) (error₂ := e2)
    (fun h => by
      unfold goodIdealMass
      split_ifs
      · exact Sid.1.2.2.1 h
      · exact le_rfl)
    (fun h => by
      unfold goodIdealMass
      split_ifs
      · exact le_rfl
      · exact Sid.1.2.2.1 h)
    (by
      simp only [goodIdealMass, replayGoodIdeal_nil, Option.isSome_some, ↓reduceIte]
      exact Sid.1.2.1)
    (fun h => sponge_good_ratio_le p M hp henc spec q_pub h)
    (cost := spongeStepCost p M spec q_pub)
    (fun h x _ hadm => goodIdealMass_step_loss_le p M hp henc spec q_pub h x hadm)
    (fun h hne => transcriptCost_spongeStepCost_le p M spec q_pub h hne)
  have hsum_eq : (e1 : ENNReal) + (e2 : ENNReal) =
      ENNReal.ofReal (((w + q_pub : ℕ) : ℝ) ^ 2 /
        (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
    rw [← ENNReal.coe_add, ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    congr 1
    apply NNReal.eq
    change (((w + q_pub : ℕ) : ℝ) ^ 2 - (q_pub : ℝ) ^ 2) /
        (Fintype.card (ByteState p.capacityBytes) : ℝ) +
      (q_pub : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ) =
      ((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ)
    ring
  rw [← hsum_eq]
  exact hdist

/-- **Path B (Unified CC indifferentiability bound via H-coefficient)**:
matches the exact unified bound `Q^2 / |C| + C(Q, 2) / |S|` shared with the 2-hop `≡g` engine. -/
theorem sponge_indifferentiability_of_hCoefficient (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      ENNReal.ofReal
        (((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ) +
          (((w + q_pub).choose 2 : ℕ) : ℝ) / (Fintype.card (ByteState p.stateBytes) : ℝ)) := by
  refine (sponge_indifferentiability_hCoefficient_tight p M hp henc spec q_pub).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact le_add_of_nonneg_right (by positivity)

end HCoefficientProof

end Commons.Sponge
