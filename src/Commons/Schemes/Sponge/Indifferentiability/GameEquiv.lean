module

public import Commons.Schemes.Sponge.Indifferentiability.IdealGame

/-!
# Sponge indifferentiability via 2-hop `≡g` game equivalence and bidirectional switching

Proves `sponge_indifferentiability_of_gameEquivalent` in two hops [1, §4], [2, §4]:

1. **Hop 1 (`BidirectionalSwitching`)**: switches `StrongURP` to `LazyBidirectionalRF` within
   `C(w + q_pub, 2) / |S|` via `strongURP_attach_dist_lazyBidirectionalRF_le`.
2. **Hop 2 (`≡g` game equivalence)**: couples `realSpongeGame` and `idealSpongeGame` through the
   intermediate `lazyPathGame` (`realSpongeGame_gameEquivalent_idealSpongeGame`), bounding the
   visible distance by `(w + q_pub)^2 / |C|` (`lazyBidirectionalRF_sponge_dist_ideal_le`).

## References

1. G. Bertoni, J. Daemen, M. Peeters, and G. Van Assche. *On the Indifferentiability of the Sponge
   Construction*. In *Advances in Cryptology — EUROCRYPT 2008*, LNCS 4965, pp. 181–197, 2008.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Commons.Sponge

open CategoryTheory ConstructiveCryptography SystemAlgebra
open Probability Probability.Distribution Commons.BidirectionalSwitching
open scoped BigOperators NNReal SystemAlgebra ConstructiveCryptography MonoidalCategory

section GameEquivalenceProof

variable (p : Parameters) (M : Type) [Fintype M] [DecidableEq M]

/-! #### Lazy path game (`lazyPathGame`) and `lazyPathGame ≡g idealSpongeGame` -/

/-- Structural good invariant maintained on `(T_pub, hid)` while `bad = false`. -/
structure LazyGoodInv (p : Parameters)
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) : Prop where
  partialBij : IsPartialBijection (toPairs T_pub)
  capFree : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) T_pub
  keysNodup : (hid.map Prod.fst).Nodup
  keysNonempty : ∀ entry ∈ hid, entry.1 ≠ []
  keysUncovered : ∀ entry ∈ hid,
    evalAbsorption p T_pub (zeroState p.stateBytes) entry.1 = none
  prefixClosed : ∀ entry ∈ hid,
    (evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast).isSome ∨
      entry.1.dropLast ∈ hid.map Prod.fst
  capsDisjoint : ∀ c ∈ hiddenCapsList p hid, c ∉ occupiedCapsList p T_pub
  capsNodup : (hiddenCapsList p hid).Nodup

omit [Fintype M] [DecidableEq M] in
lemma lazyGoodInv_nil : LazyGoodInv p [] [] where
  partialBij := isPartialBijection_nil
  capFree := capacityCollisionFree_nil (capacityPart p) (zeroState p.capacityBytes)
  keysNodup := List.nodup_nil
  keysNonempty := fun _ h => by cases h
  keysUncovered := fun _ h => by cases h
  prefixClosed := fun _ h => by cases h
  capsDisjoint := fun _ h => by cases h
  capsNodup := List.nodup_nil

omit [Fintype M] [DecidableEq M] in
lemma rootedPrefix_spec (encode : M → List (BitVec 8))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    {x : ByteState p.stateBytes} {bs : List (ByteState p.rateBytes)}
    (hrp : rootedPrefix p M encode T_pub x = some bs) :
    ∃ (pref : List (ByteState p.rateBytes)) (parent : ByteState p.stateBytes)
      (last : ByteState p.rateBytes),
      bs = pref ++ [last] ∧
      evalAbsorption p T_pub (zeroState p.stateBytes) pref = some parent ∧
      absorbBlock p parent last = x := by
  unfold rootedPrefix at hrp
  cases hcm : completingMessage p encode T_pub x with
  | some m =>
    rw [hcm] at hrp
    obtain ⟨rfl⟩ := Option.some.inj hrp
    unfold completingMessage at hcm
    split_ifs at hcm with hex
    · obtain ⟨rfl⟩ := Option.some.inj hcm
      obtain ⟨parent, last, hsplit, hpar, habs⟩ := Classical.choose_spec hex
      exact ⟨(paddedBlocks p (encode (Classical.choose hex))).dropLast, parent, last,
        hsplit, hpar, habs⟩
  | none =>
    rw [hcm] at hrp
    split_ifs at hrp with hex
    · obtain ⟨rfl⟩ := Option.some.inj hrp
      have hspec := Classical.choose_spec (Classical.choose_spec hex).choose_spec
      exact ⟨Classical.choose hex, Classical.choose (Classical.choose_spec hex),
        Classical.choose (Classical.choose_spec hex).choose_spec, rfl, hspec.1, hspec.2⟩

omit [Fintype M] [DecidableEq M] in
lemma rootedPrefix_eq_some_of_path (hp : p.Valid) (encode : M → List (BitVec 8))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs T_pub))
    (hcf : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) T_pub)
    {x : ByteState p.stateBytes} {pref : List (ByteState p.rateBytes)}
    {parent : ByteState p.stateBytes} {last : ByteState p.rateBytes}
    (hpar : evalAbsorption p T_pub (zeroState p.stateBytes) pref = some parent)
    (habs : absorbBlock p parent last = x) :
    rootedPrefix p M encode T_pub x = some (pref ++ [last]) := by
  have hex : ∃ bs, rootedPrefix p M encode T_pub x = some bs := by
    unfold rootedPrefix
    cases hcm : completingMessage p encode T_pub x with
    | some m => exact ⟨paddedBlocks p (encode m), rfl⟩
    | none =>
      have hwit : ∃ (pref' : List (ByteState p.rateBytes)) (s : ByteState p.stateBytes)
          (b : ByteState p.rateBytes),
          evalAbsorption p T_pub (zeroState p.stateBytes) pref' = some s ∧
          absorbBlock p s b = x := ⟨pref, parent, last, hpar, habs⟩
      rw [dite_eq_left hwit]
      exact ⟨_, rfl⟩
  rcases hex with ⟨bs, hrp⟩
  obtain ⟨pref', parent', last', rfl, hpar', habs'⟩ := rootedPrefix_spec p M encode T_pub hrp
  have hcapEq : capacityPart p parent' = capacityPart p parent := by
    have hc := congrArg (capacityPart p) (habs'.trans habs.symm)
    simpa only [capacityPart_absorbBlock] using hc
  have hparEq : parent' = parent :=
    reached_capacity_injective (capacityPart p) (zeroState p.capacityBytes)
      (zeroState p.stateBytes) (capacityPart_zeroState p) T_pub hcf
      (evalAbsorption_reached p T_pub hcf _ hpar')
      (evalAbsorption_reached p T_pub hcf _ hpar) hcapEq
  subst hparEq
  have hlastEq : last' = last := absorbBlock_injective p hp.2.1.le parent' (habs'.trans habs.symm)
  have hprefEq : pref' = pref := blocks_eq_of_evalAbsorption_eq p hp T_pub hpb hcf hpar' hpar
  rw [hprefEq, hlastEq] at hrp
  exact hrp

omit [Fintype M] [DecidableEq M] in
lemma rootedPrefix_cap_mem_occupied (encode : M → List (BitVec 8))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hcf : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) T_pub)
    {x : ByteState p.stateBytes} {bs : List (ByteState p.rateBytes)}
    (hrp : rootedPrefix p M encode T_pub x = some bs) :
    capacityPart p x ∈ occupiedCapsList p T_pub := by
  obtain ⟨pref, parent, last, _, hpar, habs⟩ := rootedPrefix_spec p M encode T_pub hrp
  rw [← habs, capacityPart_absorbBlock, mem_occupiedCapsList_iff]
  rcases Set.mem_insert_iff.mp (evalAbsorption_reached p T_pub hcf pref hpar) with rfl | hfor
  · rw [capacityPart_zeroState]
    exact Finset.mem_insert_self _ _
  · rcases hfor with ⟨e, he, _, rfl⟩
    simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union, List.mem_toFinset]
    exact Or.inr (Or.inr (List.mem_map_of_mem he))

omit [Fintype M] [DecidableEq M] in
lemma evalAbsorption_recordForwardEdge_of_rootedPrefix (hp : p.Valid)
    (encode : M → List (BitVec 8))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs T_pub))
    (hcf : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) T_pub)
    {x y : ByteState p.stateBytes} (hlu : lookupForwardEdge T_pub x = none)
    (hy : capacityPart p y ∉ occupiedCapsList p T_pub)
    {bs : List (ByteState p.rateBytes)} (hrp : rootedPrefix p M encode T_pub x = some bs) :
    evalAbsorption p (recordForwardEdge T_pub x y) (zeroState p.stateBytes) bs = some y ∧
      ∀ bs' : List (ByteState p.rateBytes), bs' ≠ [] → bs' ≠ bs →
        evalAbsorption p T_pub (zeroState p.stateBytes) bs' = none →
        evalAbsorption p (recordForwardEdge T_pub x y) (zeroState p.stateBytes) bs' = none := by
  have hy_occ : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
    rwa [← mem_occupiedCapsList_iff]
  constructor
  · obtain ⟨pref, parent, last, rfl, hpar, habs⟩ := rootedPrefix_spec p M encode T_pub hrp
    rw [recordForwardEdge_eq_append_of_avoids p T_pub hy_occ, evalAbsorption_append,
      evalAbsorption_mono p hpar]
    simp only [Option.bind_some, evalAbsorption, habs, lookupForwardEdge_append_of_none hlu,
      lookupForwardEdge, ↓reduceIte]
  · intro bs' hne_nil hne_bs hnone
    by_contra hsome
    cases hnew : evalAbsorption p (recordForwardEdge T_pub x y) (zeroState p.stateBytes) bs' with
    | none => exact hsome hnew
    | some out =>
      rw [recordForwardEdge_eq_append_of_avoids p T_pub hy_occ] at hnew
      have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes) T_pub
          ⟨x, y, false⟩ := hy_occ
      obtain ⟨_, parent', last', hsplit', hpar', habs', _⟩ :=
        no_preexisting_extension p T_pub ⟨x, y, false⟩ hf bs' hne_nil hnew hnone
      have hrp' := rootedPrefix_eq_some_of_path p M hp encode T_pub hpb hcf hpar' habs'
      rw [hrp] at hrp'
      exact hne_bs (hsplit'.trans (Option.some.inj hrp').symm)

omit [Fintype M] [DecidableEq M] in
lemma evalAbsorption_recordForwardEdge_of_rootedPrefix_none (hp : p.Valid)
    (encode : M → List (BitVec 8))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs T_pub))
    (hcf : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) T_pub)
    {x y : ByteState p.stateBytes}
    (hy : capacityPart p y ∉ occupiedCapsList p T_pub)
    (hrp : rootedPrefix p M encode T_pub x = none) :
    ∀ bs' : List (ByteState p.rateBytes), bs' ≠ [] →
      evalAbsorption p T_pub (zeroState p.stateBytes) bs' = none →
      evalAbsorption p (recordForwardEdge T_pub x y) (zeroState p.stateBytes) bs' = none := by
  have hy_occ : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
    rwa [← mem_occupiedCapsList_iff]
  intro bs' hne_nil hnone
  by_contra hsome
  cases hnew : evalAbsorption p (recordForwardEdge T_pub x y) (zeroState p.stateBytes) bs' with
  | none => exact hsome hnew
  | some out =>
    rw [recordForwardEdge_eq_append_of_avoids p T_pub hy_occ] at hnew
    have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes) T_pub
        ⟨x, y, false⟩ := hy_occ
    obtain ⟨_, parent', last', _, hpar', habs', _⟩ :=
      no_preexisting_extension p T_pub ⟨x, y, false⟩ hf bs' hne_nil hnew hnone
    have hrp' := rootedPrefix_eq_some_of_path p M hp encode T_pub hpb hcf hpar' habs'
    rw [hrp] at hrp'
    cases hrp'

omit [Fintype M] [DecidableEq M] in
lemma lookup_eraseHiddenKey_of_ne
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    {bs bs' : List (ByteState p.rateBytes)} (hne : bs' ≠ bs) :
    (eraseHiddenKey p hid bs).lookup bs' = hid.lookup bs' := by
  induction hid with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k0, v0⟩
    unfold eraseHiddenKey
    rw [List.filter_cons]
    by_cases heq : k0 = bs
    · subst heq
      have hf : decide (k0 ≠ k0) = false := decide_eq_false (not_not.mpr rfl)
      rw [ite_eq_right (by rw [hf]; exact Bool.false_ne_true)]
      have hbeq : (bs' == k0) = false := beq_false_of_ne hne
      simp only [List.lookup_cons, hbeq]
      exact ih
    · have hdec : decide (k0 ≠ bs) = true := decide_eq_true heq
      rw [ite_eq_left hdec]
      simp only [List.lookup_cons]
      cases bs' == k0
      · exact ih
      · rfl

omit [Fintype M] [DecidableEq M] in
lemma lookup_append_singleton_of_not_mem
    {α β : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] (l : List (α × β)) (k : α) (v : β)
    (hnot : k ∉ l.map Prod.fst) (k' : α) :
    (l ++ [(k, v)]).lookup k' = if k' = k then some v else l.lookup k' := by
  induction l with
  | nil =>
    simp only [List.nil_append, List.lookup_cons, List.lookup_nil]
    by_cases hk : k' = k
    · subst hk; simp only [beq_self_eq_true, ↓reduceIte]
    · simp only [beq_false_of_ne hk, hk, ↓reduceIte]
  | cons hd tl ih =>
    rcases hd with ⟨k0, v0⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [List.cons_append, List.lookup_cons]
    by_cases h1 : k' = k0
    · subst h1
      have hne : k' ≠ k := Ne.symm hnot.1
      simp only [beq_self_eq_true, hne, ↓reduceIte]
    · simp only [beq_false_of_ne h1]
      exact ih hnot.2

omit [Fintype M] [DecidableEq M] in
lemma lookup_eq_some_of_mem_map_fst
    {α β : Type*} [BEq α] [LawfulBEq α] (l : List (α × β)) {k : α}
    (hmem : k ∈ l.map Prod.fst) :
    ∃ v, l.lookup k = some v ∧ (k, v) ∈ l := by
  induction l with
  | nil => simp only [List.map_nil, List.not_mem_nil] at hmem
  | cons hd tl ih =>
    rcases hd with ⟨k0, v0⟩
    simp only [List.map_cons, List.mem_cons] at hmem
    by_cases heq : k = k0
    · subst heq
      exact ⟨v0, by simp only [List.lookup_cons, beq_self_eq_true], List.mem_cons_self⟩
    · rcases hmem with rfl | htl
      · exact False.elim (heq rfl)
      · obtain ⟨v, hlu, hm⟩ := ih htl
        exact ⟨v, by simp only [List.lookup_cons, beq_false_of_ne heq, hlu],
          List.mem_cons_of_mem _ hm⟩

omit [Fintype M] [DecidableEq M] in
lemma mem_of_lookup_eq_some {α β : Type*} [BEq α] [LawfulBEq α]
    {l : List (α × β)} {k : α} {v : β} (hlu : l.lookup k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => cases hlu
  | cons hd tl ih =>
    rcases hd with ⟨k0, v0⟩
    simp only [List.lookup_cons] at hlu
    by_cases heq : k = k0
    · subst heq
      simp only [beq_self_eq_true, Option.some.injEq] at hlu
      subst hlu
      exact List.mem_cons_self
    · simp only [beq_false_of_ne heq] at hlu
      exact List.mem_cons_of_mem _ (ih hlu)

/-- Partial random oracle determined by `(T_pub, hid)`: if `paddedBlocks p (encode m)` is covered
in `T_pub` use its sponge digest; else if it is in `hid` use the hidden node's digest. -/
def roOfState (encode : M → List (BitVec 8))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (m : M) : Option (ByteState p.outputBytes) :=
  match evalAbsorption p T_pub (zeroState p.stateBytes) (paddedBlocks p (encode m)) with
  | some s => some (digestPart p s)
  | none => (hid.lookup (paddedBlocks p (encode m))).map (digestPart p)

/-- Product distribution on `M → ByteState p.outputBytes` fixing coordinates where `Q m = some d`
and drawing fresh uniform digests where `Q m = none`. -/
noncomputable def roLaw (Q : M → Option (ByteState p.outputBytes)) :
    ProbDist (M → ByteState p.outputBytes) :=
  ProbDist.pi fun m : M =>
    match Q m with
    | some d => ProbDist.single d
    | none => 𝒰[ByteState p.outputBytes]

/-- Conditional law of the ideal random oracle `ro` given the lazy path state `(T_pub, hid)`. -/
noncomputable abbrev roCompleteOfState (encode : M → List (BitVec 8))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) :
    ProbDist (M → ByteState p.outputBytes) :=
  roLaw p M (roOfState p M encode T_pub hid)

lemma roLaw_none : roLaw p M (fun _ => none) = 𝒰[M → ByteState p.outputBytes] := by
  apply Subtype.ext
  apply Finsupp.ext
  intro f
  change (∏ _ : M, (uniform (ByteState p.outputBytes)) _) =
    (uniform (M → ByteState p.outputBytes)) f
  simp only [uniform_apply, Fintype.card_fun, Finset.prod_const, Finset.card_univ,
    Nat.cast_pow, one_div_pow]

lemma roLaw_support_eq_of_some (Q : M → Option (ByteState p.outputBytes))
    {m : M} {d : ByteState p.outputBytes} (hQ : Q m = some d)
    {ro : M → ByteState p.outputBytes} (hmem : ro ∈ (roLaw p M Q).1.support) :
    ro m = d := by
  have hcoord := (ProbDist.mem_support_pi_iff _ ro).mp hmem m
  simp only [hQ, ProbDist.single, Finsupp.mem_support_iff, Finsupp.single_apply] at hcoord
  by_contra hne
  exact hcoord (ite_eq_right (Ne.symm hne))

/-- Core disintegration identity: drawing `z ∼ 𝒰[S]` and conditioning `ro m := digestPart p z`
equals drawing `ro` first (with `ro m ∼ 𝒰[D]`) and then `z := assembleState p (ro m) t`. -/
lemma roLaw_disintegrate (hp : p.Valid) (Q : M → Option (ByteState p.outputBytes))
    (m : M) (hnone : Q m = none) :
    ((𝒰[ByteState p.stateBytes]).bind fun z =>
        (roLaw p M (Function.update Q m (some (digestPart p z)))).map fun ro => (ro, z)) =
      (roLaw p M Q).bind fun ro =>
        (𝒰[ByteState (tailBytes p)]).map fun t => (ro, assembleState p (ro m) t) := by
  have hho : p.outputBytes ≤ p.stateBytes := hp.2.2.2.1.trans hp.2.1.le
  have hunifS : 𝒰[ByteState p.stateBytes] =
      (𝒰[ByteState p.outputBytes]).bind fun d =>
        (𝒰[ByteState (tailBytes p)]).map fun t => assembleState p d t := by
    apply Subtype.ext
    change uniform (ByteState p.stateBytes) = _
    rw [← uniform_state_eq_assemble p hho, prod_eq_bindK, fTransform_bindK]
    simp only [ProbDist.bind_val, ProbDist.map_val, fTransform_fTransform]
    rfl
  rw [hunifS, probDist_bind_assoc]
  have hstep1 : ∀ d : ByteState p.outputBytes,
      (((𝒰[ByteState (tailBytes p)]).map fun t => assembleState p d t).bind fun z =>
          (roLaw p M (Function.update Q m (some (digestPart p z)))).map fun ro => (ro, z)) =
        (roLaw p M (Function.update Q m (some d))).bind fun ro =>
          (𝒰[ByteState (tailBytes p)]).map fun t => (ro, assembleState p (ro m) t) := by
    intro d
    rw [probDist_bind_map]
    have hdig : (fun t : ByteState (tailBytes p) =>
        (roLaw p M (Function.update Q m (some (digestPart p (assembleState p d t))))).map
          fun ro => (ro, assembleState p d t)) =
        fun t => (roLaw p M (Function.update Q m (some d))).map
          fun ro => (ro, assembleState p d t) := by
      funext t
      rw [digestPart_assembleState p hho d t]
    rw [hdig]
    simp_rw [probDist_map_eq_bind]
    rw [probDist_bind_comm]
    apply Subtype.ext
    simp only [ProbDist.bind_val]
    apply bindK_congr
    intro ro hro
    have hrom : ro m = d := roLaw_support_eq_of_some p M _ (Function.update_self m _ Q) hro
    rw [hrom]
  simp_rw [hstep1]
  rw [← probDist_bind_assoc]
  congr 1
  apply Subtype.ext
  rw [ProbDist.bind_val, roLaw, ProbDist.pi_val, pi_eq_bindK_update _ m]
  simp only [hnone]
  apply bindK_congr
  intro d _
  rw [roLaw, ProbDist.pi_val]
  congr 1
  funext m'
  by_cases hm : m' = m
  · subst hm
    simp only [Function.update_self, ProbDist.single]
  · simp only [Function.update_of_ne hm]

open Classical in
/-- Monotone-MBO game step of the lazy path game `lazyPathGame` on `(T_pub, hid, bad)`. -/
noncomputable def lazyPathGameStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    ProbStep ((List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool)
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (withMBO (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y)
  | ((T_pub, hid), bad), Sum.inl Evaluation.Port.eval, m =>
    let blocks := paddedBlocks p (encode m)
    let added := newHiddenPrefixes p T_pub (hid.map Prod.fst) blocks
    (sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub hid bad added).map
      fun ⟨hid', bad'⟩ =>
        let s := (evalAbsorption p T_pub (zeroState p.stateBytes) blocks).getD
          ((hid'.lookup blocks).getD (zeroState p.stateBytes))
        (((T_pub, hid'), bad'), (digestPart p s, bad'))
  | ((T_pub, hid), bad), Sum.inr Bidirectional.Port.forward, x =>
    match lookupForwardEdge T_pub x with
    | some y => ProbDist.single (((T_pub, hid), bad), (y, bad))
    | none =>
      match rootedPrefix p M encode T_pub x with
      | some bs =>
        if bs ∈ hid.map Prod.fst then
          let z := (hid.lookup bs).getD (zeroState p.stateBytes)
          ProbDist.single
            (((recordForwardEdge T_pub x z, eraseHiddenKey p hid bs), bad), (z, bad))
        else
          let hitX : Bool := decide (capacityPart p x ∈ hiddenCapsList p hid)
          let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
          (𝒰[ByteState p.stateBytes]).map fun y =>
            let bad' := bad || hitX || decide (capacityPart p y ∈ occ)
            (((recordForwardEdge T_pub x y, hid), bad'), (y, bad'))
      | none =>
        let hitX : Bool := decide (capacityPart p x ∈ hiddenCapsList p hid)
        let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
        (𝒰[ByteState p.stateBytes]).map fun y =>
          let bad' := bad || hitX || decide (capacityPart p y ∈ occ)
          (((recordForwardEdge T_pub x y, hid), bad'), (y, bad'))
  | ((T_pub, hid), bad), Sum.inr Bidirectional.Port.inverse, y =>
    match lookupInverseEdge T_pub y with
    | some x => ProbDist.single (((T_pub, hid), bad), (x, bad))
    | none =>
      let hitY : Bool := decide (capacityPart p y ∈ hiddenCapsList p hid)
      let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
      (𝒰[ByteState p.stateBytes]).map fun x =>
        let bad' := bad || hitY || decide (capacityPart p x ∈ occ)
        (((recordInverseEdge T_pub x y, hid), bad'), (x, bad'))

omit [DecidableEq M] in
lemma lazyPathGameStep_flag {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (s : List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (b : Bool) (i : (spec.toInterface ⊗ PrimitiveInterface p q_pub).I)
    (x : (spec.toInterface ⊗ PrimitiveInterface p q_pub).X i)
    (q : ((List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
      ((spec.toInterface ⊗ PrimitiveInterface p q_pub).Y i × Bool))
    (hq : q ∈ (lazyPathGameStep p M spec q_pub (s, b) i x).1.support) :
    q.2.2 = q.1.2 ∧ (b = true → q.1.2 = true) := by
  rcases s with ⟨T_pub, hid⟩
  have hmap_supp : ∀ {α β : Type} (μ : ProbDist α) (f : α → β) (y : β),
      y ∈ (μ.map f).1.support → ∃ a ∈ μ.1.support, f a = y := by
    intro α β μ f y hy
    obtain ⟨a, ha, hfa⟩ := mem_support_fTransform f μ.1 hy
    exact ⟨a, ha, hfa⟩
  have hsing_supp : ∀ {α : Type} (a y : α),
      y ∈ (ProbDist.single a).1.support → y = a := by
    intro α a y hy
    change y ∈ (Finsupp.single a (1 : ℝ)).support at hy
    rw [Finsupp.mem_support_iff] at hy
    by_contra hne; exact hy (Finsupp.single_eq_of_ne hne)
  rcases i with i | i
  · cases i
    dsimp only [lazyPathGameStep] at hq
    rcases hmap_supp _ _ _ hq with ⟨⟨hid', bad'⟩, hmem, rfl⟩
    exact ⟨rfl, sampleHiddenPrefixesWithBad_monotone p _ T_pub hid b _ _ hmem⟩
  · cases i with
    | forward =>
      dsimp only [lazyPathGameStep] at hq
      cases hlu : lookupForwardEdge T_pub x with
      | some y =>
        rw [hlu] at hq
        rcases hsing_supp _ _ hq with rfl; exact ⟨rfl, fun h => h⟩
      | none =>
        rw [hlu] at hq
        cases hrp : rootedPrefix p M encode T_pub x with
        | some bs =>
          rw [hrp] at hq
          by_cases hmem : bs ∈ hid.map Prod.fst
          · simp only [hmem, ↓reduceIte] at hq
            rcases hsing_supp _ _ hq with rfl; exact ⟨rfl, fun h => h⟩
          · simp only [hmem, ↓reduceIte] at hq
            rcases hmap_supp _ _ _ hq with ⟨y, _, rfl⟩
            exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩
        | none =>
          rw [hrp] at hq
          rcases hmap_supp _ _ _ hq with ⟨y, _, rfl⟩
          exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩
    | inverse =>
      dsimp only [lazyPathGameStep] at hq
      cases hlu : lookupInverseEdge T_pub x with
      | some x' =>
        rw [hlu] at hq
        rcases hsing_supp _ _ hq with rfl; exact ⟨rfl, fun h => h⟩
      | none =>
        rw [hlu] at hq
        rcases hmap_supp _ _ _ hq with ⟨x', _, rfl⟩
        exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩

/-- Intermediate lazy path game mediating between `realSpongeGame` and `idealSpongeGame`. -/
noncomputable def lazyPathGame {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    TypedGame (spec.toInterface ⊗ PrimitiveInterface p q_pub) :=
  TypedGame.ofProbAutomaton (lazyPathGameStep p M spec q_pub) (ProbDist.single ([], []))
    (lazyPathGameStep_flag p M spec q_pub)

/-- Inductive coupling of `sampleHiddenPrefixesWithBad` between `lazyPathGame` (uniform draws)
and `idealSpongeGame` (`nodeLaw ro` draws) under `roCompleteOfState`. -/
lemma sampleHiddenPrefixesWithBad_sim_ro (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode)
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (added : List (List (ByteState p.rateBytes)))
    (hadd_nd : added.Nodup)
    (hadd_unc : ∀ bs ∈ added,
      evalAbsorption p T_pub (zeroState p.stateBytes) bs = none ∧ bs ∉ hid.map Prod.fst) :
    ((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub hid false
      added).1.restrict
        fun p' => p'.2 = false).bindK
      (fun p' => ((roCompleteOfState p M encode T_pub p'.1).map fun ro => (ro, p'.1)).1) =
    (roCompleteOfState p M encode T_pub hid).1.bindK fun ro =>
      fTransform (fun p' => (ro, p'.1))
        ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hid false added).1.restrict
          fun p' => p'.2 = false) := by
  induction added generalizing hid with
  | nil =>
    simp only [sampleHiddenPrefixesWithBad]
    have h1 : ((ProbDist.single (hid, false)).1.restrict fun p' => p'.2 = false) =
        (ProbDist.single (hid, false)).1 := by
      ext a
      rw [Distribution.restrict, Finsupp.filter_apply, ProbDist.single, Finsupp.single_apply]
      by_cases ha : (hid, false) = a
      · subst ha; simp only [↓reduceIte]
      · simp only [ha, ↓reduceIte, ite_self]
    rw [h1, ProbDist.single, bindK_single, one_smul]
    simp only [ProbDist.map_val]
    change ((roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
        Finsupp.single (ro, hid) w) =
      (roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
        w • fTransform (fun p' => (ro, p'.1)) (Finsupp.single (hid, false) (1 : ℝ))
    apply Finsupp.sum_congr
    intro ro _
    rw [fTransform_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  | cons bs rest ih =>
    rw [List.nodup_cons] at hadd_nd
    rcases hadd_nd with ⟨hbs_not_rest, hrest_nd⟩
    have hbs_unc : evalAbsorption p T_pub (zeroState p.stateBytes) bs = none ∧
        bs ∉ hid.map Prod.fst := hadd_unc bs List.mem_cons_self
    have hrest_unc : ∀ z : ByteState p.stateBytes, ∀ bs' ∈ rest,
        evalAbsorption p T_pub (zeroState p.stateBytes) bs' = none ∧
          bs' ∉ (hid ++ [(bs, z)]).map Prod.fst := by
      intro z bs' hbs'
      have h0 := hadd_unc bs' (List.mem_cons_of_mem _ hbs')
      refine ⟨h0.1, ?_⟩
      simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton, not_or]
      exact ⟨h0.2, fun hEq => hbs_not_rest (hEq ▸ hbs')⟩
    simp only [sampleHiddenPrefixesWithBad, ProbDist.bind_val, Bool.false_or]
    rw [Distribution.restrict_bindK, bindK_bindK]
    have hzero_true : ∀ (draw : List (ByteState p.rateBytes) → ProbDist (ByteState p.stateBytes))
        (hid' : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)),
        ((sampleHiddenPrefixesWithBad p draw T_pub hid' true rest).1.restrict
          fun p' => p'.2 = false) = 0 := by
      intro draw hid'
      ext a
      rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.zero_apply]
      split_ifs with hfalse
      · by_contra hne
        have ht := sampleHiddenPrefixesWithBad_monotone p draw T_pub hid' true rest a
          (Finsupp.mem_support_iff.mpr hne) rfl
        rw [hfalse] at ht; cases ht
      · rfl
    set S := occupiedCapsList p T_pub ++ hiddenCapsList p hid
    have hlhs_step :
        ((𝒰[ByteState p.stateBytes]).1.bindK fun z =>
          ((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub
              (hid ++ [(bs, z)]) (decide (capacityPart p z ∈ S)) rest).1.restrict
              fun p' => p'.2 = false).bindK fun p' =>
            ((roCompleteOfState p M encode T_pub p'.1).map fun ro => (ro, p'.1)).1) =
        ((𝒰[ByteState p.stateBytes]).1.bindK fun z =>
          if capacityPart p z ∈ S then 0
          else
            (roCompleteOfState p M encode T_pub (hid ++ [(bs, z)])).1.bindK fun ro =>
              fTransform (fun p' => (ro, p'.1))
                ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
                  (hid ++ [(bs, z)]) false rest).1.restrict fun p' => p'.2 = false)) := by
      apply bindK_congr
      intro z _
      by_cases hmem : capacityPart p z ∈ S
      · rw [ite_eq_left hmem, decide_eq_true hmem, hzero_true, bindK_zero]
      · rw [ite_eq_right hmem, decide_eq_false hmem]
        exact ih (hid ++ [(bs, z)]) hrest_nd (hrest_unc z)
    rw [hlhs_step]
    have hrhs_step :
        ((roCompleteOfState p M encode T_pub hid).1.bindK fun ro =>
          fTransform (fun p' => (ro, p'.1))
            (((nodeLaw p M encode ro bs).1.bindK fun z =>
              (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
                (hid ++ [(bs, z)]) (decide (capacityPart p z ∈ S)) rest).1).restrict
                fun p' => p'.2 = false)) =
        ((roCompleteOfState p M encode T_pub hid).1.bindK fun ro =>
          (nodeLaw p M encode ro bs).1.bindK fun z =>
            if capacityPart p z ∈ S then 0
            else
              fTransform (fun p' => (ro, p'.1))
                ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
                  (hid ++ [(bs, z)]) false rest).1.restrict fun p' => p'.2 = false)) := by
      apply bindK_congr
      intro ro _
      rw [Distribution.restrict_bindK, fTransform_bindK]
      apply bindK_congr
      intro z _
      by_cases hmem : capacityPart p z ∈ S
      · rw [ite_eq_left hmem, decide_eq_true hmem, hzero_true, fTransform_zero]
      · rw [ite_eq_right hmem, decide_eq_false hmem]
    rw [hrhs_step]
    set F : (M → ByteState p.outputBytes) × ByteState p.stateBytes →
        Distribution ((M → ByteState p.outputBytes) ×
          List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) :=
      fun roz =>
        if capacityPart p roz.2 ∈ S then 0
        else
          fTransform (fun p' => (roz.1, p'.1))
            ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode roz.1) T_pub
              (hid ++ [(bs, roz.2)]) false rest).1.restrict fun p' => p'.2 = false)
    have hlhs_F :
        ((𝒰[ByteState p.stateBytes]).1.bindK fun z =>
          if capacityPart p z ∈ S then 0
          else
            (roCompleteOfState p M encode T_pub (hid ++ [(bs, z)])).1.bindK fun ro =>
              fTransform (fun p' => (ro, p'.1))
                ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
                  (hid ++ [(bs, z)]) false rest).1.restrict fun p' => p'.2 = false)) =
        ((𝒰[ByteState p.stateBytes]).bind fun z =>
          (roCompleteOfState p M encode T_pub (hid ++ [(bs, z)])).map fun ro => (ro,
            z)).1.bindK F := by
      rw [ProbDist.bind_val, bindK_bindK]
      apply bindK_congr
      intro z _
      rw [ProbDist.map_val, bindK_fTransform]
      by_cases hmem : capacityPart p z ∈ S
      · rw [ite_eq_left hmem]
        have hfz : F ∘ (fun ro => (ro, z)) = fun _ => 0 := by
          funext ro; simp only [Function.comp_def, F, hmem, ↓reduceIte]
        rw [hfz, bindK_zero_right]
      · rw [ite_eq_right hmem]
        apply bindK_congr
        intro ro _
        simp only [Function.comp_def, F, hmem, ↓reduceIte]
    have hrhs_F :
        ((roCompleteOfState p M encode T_pub hid).1.bindK fun ro =>
          (nodeLaw p M encode ro bs).1.bindK fun z =>
            if capacityPart p z ∈ S then 0
            else
              fTransform (fun p' => (ro, p'.1))
                ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
                  (hid ++ [(bs, z)]) false rest).1.restrict fun p' => p'.2 = false)) =
        ((roCompleteOfState p M encode T_pub hid).bind fun ro =>
          (nodeLaw p M encode ro bs).map fun z => (ro, z)).1.bindK F := by
      rw [ProbDist.bind_val, bindK_bindK]
      apply bindK_congr
      intro ro _
      rw [ProbDist.map_val, bindK_fTransform]
      rfl
    rw [hlhs_F, hrhs_F]
    congr 1
    apply congrArg Subtype.val
    by_cases hex : ∃ m : M, paddedBlocks p (encode m) = bs
    · rcases hex with ⟨m, rfl⟩
      have hro_none : roOfState p M encode T_pub hid m = none := by
        unfold roOfState
        rw [hbs_unc.1]
        have hlu : hid.lookup (paddedBlocks p (encode m)) = none := by
          by_contra hsome
          cases hl : hid.lookup (paddedBlocks p (encode m)) with
          | none => exact hsome hl
          | some z =>
            exact hbs_unc.2 (List.mem_map_of_mem (f := Prod.fst) (mem_of_lookup_eq_some hl))
        rw [hlu]; rfl
      have hupd : ∀ z : ByteState p.stateBytes,
          roOfState p M encode T_pub (hid ++ [(paddedBlocks p (encode m), z)]) =
            Function.update (roOfState p M encode T_pub hid) m (some (digestPart p z)) := by
        intro z
        funext m'
        by_cases hm : m' = m
        · subst hm
          unfold roOfState
          rw [hbs_unc.1, Function.update_self,
            lookup_append_singleton_of_not_mem hid _ z hbs_unc.2]
          simp only [↓reduceIte, Option.map_some]
        · unfold roOfState
          rw [Function.update_of_ne hm]
          cases evalAbsorption p T_pub (zeroState p.stateBytes) (paddedBlocks p (encode m')) with
          | some s => rfl
          | none =>
            have hne_blk : paddedBlocks p (encode m') ≠ paddedBlocks p (encode m) := fun hEq =>
              hm (henc (paddedBlocks_injective p hp.1 hp.2.2.2.2.1 hp.2.2.2.2.2 hEq))
            rw [lookup_append_singleton_of_not_mem hid _ z hbs_unc.2, ite_eq_right hne_blk]
      have hlaw : ∀ ro, nodeLaw p M encode ro (paddedBlocks p (encode m)) =
          (𝒰[ByteState (tailBytes p)]).map fun t => assembleState p (ro m) t := fun ro =>
        nodeLaw_paddedBlocks p M hp encode henc ro m
      simp_rw [roCompleteOfState, hupd, hlaw, ProbDist.map_map]
      exact roLaw_disintegrate p M hp (roOfState p M encode T_pub hid) m hro_none
    · have hro_eq : ∀ z : ByteState p.stateBytes,
          roOfState p M encode T_pub (hid ++ [(bs, z)]) = roOfState p M encode T_pub hid := by
        intro z
        funext m'
        unfold roOfState
        cases evalAbsorption p T_pub (zeroState p.stateBytes) (paddedBlocks p (encode m')) with
        | some s => rfl
        | none =>
          have hne_blk : paddedBlocks p (encode m') ≠ bs := fun hEq => hex ⟨m', hEq⟩
          rw [lookup_append_singleton_of_not_mem hid _ z hbs_unc.2, ite_eq_right hne_blk]
      have hlaw : ∀ ro, nodeLaw p M encode ro bs = 𝒰[ByteState p.stateBytes] := by
        intro ro; unfold nodeLaw; rw [dite_eq_right hex]
      simp_rw [roCompleteOfState, hro_eq, hlaw, probDist_map_eq_bind]
      exact probDist_bind_comm _ _ _

/-- `lazyPathGame` and `idealSpongeGame` are literally equivalent as games (`≡g`). -/
theorem lazyPathGame_gameEquivalent_idealSpongeGame (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    (lazyPathGame p M spec q_pub).1.1.GameEquivalent
      (idealSpongeGame p M spec q_pub).1.1 := by
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  let K : (List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) →
      ProbDist ((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) :=
    fun st => (roCompleteOfState p M encode st.1 st.2).map fun ro => (ro, st.1, st.2)
  have hinitK : (ProbDist.single ([], [])).bind K = idealGameInit p M := by
    rw [probDist_single_bind]
    simp only [K, idealGameInit, roCompleteOfState]
    have hro0 : roOfState p M encode [] [] = fun _ => none := by
      funext m
      unfold roOfState
      have hne := paddedBlocks_ne_nil p hp.1 (encode m)
      cases hb : paddedBlocks p (encode m) with
      | nil => exact False.elim (hne hb)
      | cons b rest => simp only [evalAbsorption, lookupForwardEdge, List.lookup_nil,
        Option.map_none]
    rw [hro0, roLaw_none]
  have hInv_sample : ∀ (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
      (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
      (inv : LazyGoodInv p T_pub hid)
      (added : List (List (ByteState p.rateBytes)))
      (hadd_nd : added.Nodup)
      (hadd_ne : ∀ bs ∈ added, bs ≠ [])
      (hadd_unc : ∀ bs ∈ added,
        evalAbsorption p T_pub (zeroState p.stateBytes) bs = none ∧ bs ∉ hid.map Prod.fst)
      (hadd_pc : ∀ (i : ℕ) (hi : i < added.length),
        (evalAbsorption p T_pub (zeroState p.stateBytes) (added[i]'hi).dropLast).isSome ∨
          (added[i]'hi).dropLast ∈ hid.map Prod.fst ∨
          ∃ (j : ℕ) (hj : j < i), (added[j]'(lt_trans hj hi)) = (added[i]'hi).dropLast)
      (hid' : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)),
      (hid', false) ∈ (sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes])
        T_pub hid false added).1.support →
      LazyGoodInv p T_pub hid' ∧
        (∀ bs ∈ added, bs ∈ hid'.map Prod.fst) ∧
        (∀ bs ∈ hid.map Prod.fst, bs ∈ hid'.map Prod.fst) := by
    intro T_pub hid inv added
    induction added generalizing hid with
    | nil =>
      intro _ _ _ _ hid' hmem
      change (hid', false) ∈ (Finsupp.single (hid, false) (1 : ℝ)).support at hmem
      rw [Finsupp.mem_support_iff] at hmem
      have hEq : (hid', false) = (hid, false) := by
        by_contra hne; exact hmem (Finsupp.single_eq_of_ne hne)
      have hfst : hid' = hid := congrArg Prod.fst hEq
      subst hfst
      exact ⟨inv, fun _ h => False.elim (List.not_mem_nil h), fun _ h => h⟩
    | cons bs rest ih =>
      intro hadd_nd hadd_ne hadd_unc hadd_pc hid' hmem
      rw [List.nodup_cons] at hadd_nd
      rcases hadd_nd with ⟨hbs_not_rest, hrest_nd⟩
      simp only [sampleHiddenPrefixesWithBad, ProbDist.bind_val, Bool.false_or] at hmem
      rw [Finsupp.mem_support_iff, bindK_apply, Finsupp.sum] at hmem
      have hex : ∃ z ∈ (𝒰[ByteState p.stateBytes]).1.support,
          (sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub
            (hid ++ [(bs, z)])
            (decide (capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid))
            rest).1 (hid', false) ≠ 0 := by
        by_contra hall; push Not at hall; apply hmem
        exact Finset.sum_eq_zero fun z hz => by rw [hall z hz, mul_zero]
      rcases hex with ⟨z, _, hne⟩
      have hz_avoid : capacityPart p z ∉ occupiedCapsList p T_pub ++ hiddenCapsList p hid := by
        intro hhit
        rw [decide_eq_true hhit] at hne
        have ht := sampleHiddenPrefixesWithBad_monotone p _ T_pub (hid ++ [(bs, z)]) true rest
          (hid', false) (Finsupp.mem_support_iff.mpr hne) rfl
        cases ht
      rw [decide_eq_false hz_avoid] at hne
      simp only [List.mem_append, not_or] at hz_avoid
      have hbs_u := hadd_unc bs List.mem_cons_self
      have hbs_pc : (evalAbsorption p T_pub (zeroState p.stateBytes) bs.dropLast).isSome ∨
          bs.dropLast ∈ hid.map Prod.fst := by
        rcases hadd_pc 0 (Nat.zero_lt_succ _) with h1 | h2 | ⟨j, hj, _⟩
        · exact Or.inl h1
        · exact Or.inr h2
        · omega
      have inv1 : LazyGoodInv p T_pub (hid ++ [(bs, z)]) :=
        { partialBij := inv.partialBij
          capFree := inv.capFree
          keysNodup := by
            rw [List.map_append, List.map_singleton, List.nodup_append]
            refine ⟨inv.keysNodup, List.nodup_singleton bs, fun a ha b hb hEq => ?_⟩
            rw [List.mem_singleton.mp hb] at hEq
            dsimp only at hEq
            exact hbs_u.2 (hEq ▸ ha)
          keysNonempty := fun entry he => by
            rcases List.mem_append.mp he with he | he
            · exact inv.keysNonempty entry he
            · rw [List.mem_singleton.mp he]; exact hadd_ne bs List.mem_cons_self
          keysUncovered := fun entry he => by
            rcases List.mem_append.mp he with he | he
            · exact inv.keysUncovered entry he
            · rw [List.mem_singleton.mp he]; exact hbs_u.1
          prefixClosed := fun entry he => by
            rw [List.map_append, List.map_singleton]
            rcases List.mem_append.mp he with he | he
            · rcases inv.prefixClosed entry he with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (List.mem_append_left _ h2)
            · rw [List.mem_singleton.mp he]
              rcases hbs_pc with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (List.mem_append_left _ h2)
          capsDisjoint := fun c hc => by
            simp only [hiddenCapsList, List.map_append, List.map_singleton, List.mem_append,
              List.mem_singleton] at hc
            rcases hc with hc | rfl
            · exact inv.capsDisjoint c hc
            · exact hz_avoid.1
          capsNodup := by
            simp only [hiddenCapsList, List.map_append, List.map_singleton, List.nodup_append]
            refine ⟨inv.capsNodup, List.nodup_singleton _, fun a ha b hb hEq => ?_⟩
            rw [List.mem_singleton.mp hb] at hEq
            exact hz_avoid.2 (hEq ▸ ha) }
      have hrest_unc : ∀ bs' ∈ rest,
          evalAbsorption p T_pub (zeroState p.stateBytes) bs' = none ∧
            bs' ∉ (hid ++ [(bs, z)]).map Prod.fst := by
        intro bs' hbs'
        have h0 := hadd_unc bs' (List.mem_cons_of_mem _ hbs')
        refine ⟨h0.1, ?_⟩
        simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton, not_or]
        exact ⟨h0.2, fun hEq => hbs_not_rest (hEq ▸ hbs')⟩
      have hrest_pc : ∀ (i : ℕ) (hi : i < rest.length),
          (evalAbsorption p T_pub (zeroState p.stateBytes) (rest[i]'hi).dropLast).isSome ∨
            (rest[i]'hi).dropLast ∈ (hid ++ [(bs, z)]).map Prod.fst ∨
            ∃ (j : ℕ) (hj : j < i), (rest[j]'(lt_trans hj hi)) = (rest[i]'hi).dropLast := by
        intro i hi
        have h0 := hadd_pc (i + 1) (Nat.succ_lt_succ hi)
        simp only [List.getElem_cons_succ] at h0
        rcases h0 with h1 | h2 | ⟨j, hj, hEq⟩
        · exact Or.inl h1
        · exact Or.inr (Or.inl (by simp only [List.map_append, List.mem_append]; exact Or.inl h2))
        · cases j with
          | zero =>
            simp only [List.getElem_cons_zero] at hEq
            exact Or.inr (Or.inl (by
              simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
              exact Or.inr hEq.symm))
          | succ j' =>
            simp only [List.getElem_cons_succ] at hEq
            exact Or.inr (Or.inr ⟨j', Nat.lt_of_succ_lt_succ hj, hEq⟩)
      obtain ⟨inv', hrest_in, hhid1_in⟩ :=
        ih (hid ++ [(bs, z)]) inv1 hrest_nd (fun b hb => hadd_ne b (List.mem_cons_of_mem _ hb))
          hrest_unc hrest_pc hid' (Finsupp.mem_support_iff.mpr hne)
      refine ⟨inv', ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hhid1_in b (by simp only [List.map_append, List.map_singleton, List.mem_append,
            List.mem_singleton]; exact Or.inr trivial)
        · exact hrest_in b hb
      · intro b hb
        exact hhid1_in b (by simp only [List.map_append, List.mem_append]; exact Or.inl hb)
  have hnew_pc : ∀ (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
      (keys : List (List (ByteState p.rateBytes))) (blocks : List (ByteState p.rateBytes))
      (i : ℕ) (hi : i < (newHiddenPrefixes p T_pub keys blocks).length),
      (evalAbsorption p T_pub (zeroState p.stateBytes)
          ((newHiddenPrefixes p T_pub keys blocks)[i]'hi).dropLast).isSome ∨
        ((newHiddenPrefixes p T_pub keys blocks)[i]'hi).dropLast ∈ keys ∨
        ∃ (j : ℕ) (hj : j < i),
          ((newHiddenPrefixes p T_pub keys blocks)[j]'(lt_trans hj hi)) =
            ((newHiddenPrefixes p T_pub keys blocks)[i]'hi).dropLast := by
    intro T_pub keys blocks
    have hgen : ∀ (P : List (ByteState p.rateBytes) → Bool) (n : ℕ) (hn : n ≤ blocks.length)
        (i : ℕ) (hi : i < (((List.range n).map fun k => blocks.take (k + 1)).filter P).length),
        let l := ((List.range n).map fun k => blocks.take (k + 1)).filter P
        P (l[i]'hi).dropLast = false ∨ (l[i]'hi).dropLast = [] ∨
          ∃ (j : ℕ) (hj : j < i), (l[j]'(lt_trans hj hi)) = (l[i]'hi).dropLast := by
      intro P n
      induction n with
      | zero =>
        intro _ i hi
        simp only [List.range_zero, List.map_nil, List.filter_nil, List.length_nil] at hi
        omega
      | succ n ih =>
        intro hn i hi
        dsimp only
        set l₀ := ((List.range n).map fun k => blocks.take (k + 1)).filter P
        have hl' : ((List.range (n + 1)).map fun k => blocks.take (k + 1)).filter P =
            l₀ ++ if P (blocks.take (n + 1)) = true then [blocks.take (n + 1)] else [] := by
          rw [List.range_succ, List.map_append, List.map_singleton, List.filter_append,
            List.filter_cons, List.filter_nil]
        by_cases hlt : i < l₀.length
        · have hget : (((List.range (n + 1)).map fun k => blocks.take (k + 1)).filter P)[i]'hi =
              l₀[i]'hlt := by
            simp only [hl', List.getElem_append_left hlt]
          rw [hget]
          rcases ih (Nat.le_of_succ_le hn) i hlt with h1 | h2 | ⟨j, hj, hEq⟩
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · refine Or.inr (Or.inr ⟨j, hj, ?_⟩)
            have hj' : j < l₀.length := lt_trans hj hlt
            simp only [hl', List.getElem_append_left hj']
            exact hEq
        · by_cases hP : P (blocks.take (n + 1)) = true
          · rw [ite_eq_left hP] at hl'
            have hlen : (((List.range (n + 1)).map fun k =>
                blocks.take (k + 1)).filter P).length = l₀.length + 1 := by
              rw [hl', List.length_append, List.length_singleton]
            have hi_eq : i = l₀.length := by omega
            have hget : (((List.range (n + 1)).map fun k => blocks.take (k + 1)).filter P)[i]'hi =
                blocks.take (n + 1) := by
              simp only [hl', hi_eq, List.getElem_append_right le_rfl, Nat.sub_self,
                List.getElem_cons_zero]
            rw [hget]
            have hdrop : (blocks.take (n + 1)).dropLast = blocks.take n := by
              rw [List.take_succ_eq_append_getElem (by omega),
                List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
              simp only [List.dropLast_singleton, List.append_nil]
            rw [hdrop]
            cases n with
            | zero => exact Or.inr (Or.inl (List.take_zero))
            | succ k =>
              by_cases hPk : P (blocks.take (k + 1)) = true
              · have hmem0 : blocks.take (k + 1) ∈ l₀ := by
                  rw [List.mem_filter]
                  exact ⟨List.mem_map.mpr ⟨k, List.mem_range.mpr (Nat.lt_succ_self k), rfl⟩, hPk⟩
                obtain ⟨j, hj, hgetj⟩ := List.getElem_of_mem hmem0
                refine Or.inr (Or.inr ⟨j, by omega, ?_⟩)
                simp only [hl', List.getElem_append_left hj]
                exact hgetj
              · exact Or.inl (Bool.eq_false_iff.mpr hPk)
          · rw [ite_eq_right hP, List.append_nil] at hl'
            have : i < l₀.length := by rw [hl'] at hi; exact hi
            exact False.elim (hlt this)
    intro i hi
    unfold newHiddenPrefixes nonemptyPrefixes at hi ⊢
    rcases hgen (fun bs => (evalAbsorption p T_pub (zeroState p.stateBytes) bs).isNone &&
        !(keys.contains bs)) blocks.length le_rfl i hi with
      hfalse | hnil | hprev
    · by_cases hnone : (evalAbsorption p T_pub (zeroState p.stateBytes)
          ((List.filter (fun bs => (evalAbsorption p T_pub (zeroState p.stateBytes) bs).isNone &&
            !keys.contains bs)
              (List.map (fun k => blocks.take (k +
                1)) (List.range blocks.length)))[i]'hi).dropLast).isNone = true
      · rw [hnone, Bool.true_and, Bool.not_eq_false', List.contains_iff_mem] at hfalse
        exact Or.inr (Or.inl hfalse)
      · rw [Bool.not_eq_true] at hnone
        cases hev : evalAbsorption p T_pub (zeroState p.stateBytes)
            ((List.filter (fun bs => (evalAbsorption p T_pub (zeroState p.stateBytes) bs).isNone &&
              !keys.contains bs)
                (List.map (fun k => blocks.take (k +
                  1)) (List.range blocks.length)))[i]'hi).dropLast with
        | none => rw [hev] at hnone; cases hnone
        | some s => exact Or.inl (by simp only [Option.isSome_some])
    · rw [hnil]; exact Or.inl (by simp only [evalAbsorption, Option.isSome_some])
    · exact Or.inr (Or.inr hprev)
  apply unsetMBOs_eq_of_good_simulation (lazyPathGameStep p M spec q_pub)
    (idealSpongeGameStep p M spec q_pub) (ProbDist.single ([], [])) (idealGameInit p M)
    (lazyPathGameStep_flag p M spec q_pub) (idealSpongeGameStep_flag p M spec q_pub)
    (fun st => LazyGoodInv p st.1 st.2) K
  · intro st hst
    change st ∈ (Finsupp.single ([], []) (1 : ℝ)).support at hst
    rw [Finsupp.mem_support_iff] at hst
    have hEq : st = ([], []) := by
      by_contra hne; exact hst (Finsupp.single_eq_of_ne hne)
    subst hEq
    exact lazyGoodInv_nil p
  · exact hinitK
  · intro ⟨T_pub, hid⟩ o u ⟨T_pub', hid'⟩ y inv hsupp
    have hmap_supp : ∀ {α β : Type} (μ : ProbDist α) (f : α → β) (q : β),
        q ∈ (μ.map f).1.support → ∃ a ∈ μ.1.support, f a = q := by
      intro α β μ f q hq
      obtain ⟨a, ha, hfa⟩ := mem_support_fTransform f μ.1 hq
      exact ⟨a, ha, hfa⟩
    have hsing_supp : ∀ {α : Type} (a q : α),
        q ∈ (ProbDist.single a).1.support → q = a := by
      intro α a q hq
      change q ∈ (Finsupp.single a (1 : ℝ)).support at hq
      rw [Finsupp.mem_support_iff] at hq
      by_contra hne; exact hq (Finsupp.single_eq_of_ne hne)
    rcases o with o | o
    · cases o
      dsimp only [lazyPathGameStep] at hsupp
      rcases hmap_supp _ _ _ hsupp with ⟨⟨hid1, bad1⟩, hmem, hEq⟩
      have h1 := congrArg (fun q => q.1.1.1) hEq
      have h2 := congrArg (fun q => q.1.1.2) hEq
      have h3 := congrArg (fun q => q.1.2) hEq
      dsimp only at h1 h2 h3
      subst h1; subst h2; subst h3
      refine (hInv_sample T_pub hid inv (newHiddenPrefixes p T_pub (hid.map Prod.fst)
          (paddedBlocks p (encode u)))
        ((nonemptyPrefixes_nodup _).filter _)
        (fun bs hbs => mem_nonemptyPrefixes_ne_nil (List.mem_filter.mp hbs).1)
        (fun bs hbs => by
          have hf := (List.mem_filter.mp hbs).2
          rw [Bool.and_eq_true] at hf
          refine ⟨Option.isNone_iff_eq_none.mp hf.1, ?_⟩
          have hnc := hf.2
          intro hmem
          have hc := List.contains_iff_mem.mpr hmem
          rw [hc] at hnc; cases hnc)
        (hnew_pc T_pub (hid.map Prod.fst) (paddedBlocks p (encode u))) hid1 hmem).1
    · cases o with
      | forward =>
        dsimp only [lazyPathGameStep] at hsupp
        cases hlu : lookupForwardEdge T_pub u with
        | some y0 =>
          rw [hlu] at hsupp
          rcases hsing_supp _ _ hsupp with hEq
          have h1 := congrArg (fun q => q.1.1.1) hEq
          have h2 := congrArg (fun q => q.1.1.2) hEq
          dsimp only at h1 h2; subst h1; subst h2
          exact inv
        | none =>
          rw [hlu] at hsupp
          cases hrp : rootedPrefix p M encode T_pub u with
          | some bs =>
            rw [hrp] at hsupp
            by_cases hmem : bs ∈ hid.map Prod.fst
            · simp only [hmem, ↓reduceIte] at hsupp
              rcases hsing_supp _ _ hsupp with hEq
              have h1 := congrArg (fun q => q.1.1.1) hEq
              have h2 := congrArg (fun q => q.1.1.2) hEq
              dsimp only at h1 h2; subst h1; subst h2
              obtain ⟨z, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hmem
              simp only [hz_lu, Option.getD_some]
              have hz_cap : capacityPart p z ∉ occupiedCapsList p T_pub :=
                inv.capsDisjoint (capacityPart p z) (List.mem_map_of_mem hz_mem)
              have hz_occ : capacityPart p z ∉
                  occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
                rwa [← mem_occupiedCapsList_iff]
              have hrec : recordForwardEdge T_pub u z = T_pub ++ [⟨u, z, false⟩] :=
                recordForwardEdge_eq_append_of_avoids p T_pub hz_occ
              have hx_cap : capacityPart p u ∈ occupiedCapsList p T_pub :=
                rootedPrefix_cap_mem_occupied p M encode T_pub inv.capFree hrp
              have hEval := evalAbsorption_recordForwardEdge_of_rootedPrefix p M hp encode T_pub
                inv.partialBij inv.capFree hlu hz_cap hrp
              refine
                { partialBij := by
                    rw [hrec]
                    have htp : toPairs (T_pub ++ [⟨u, z, false⟩]) = toPairs T_pub ++ [(u, z)] := by
                      simp only [toPairs, List.map_append, List.map_singleton]
                    rw [htp]
                    exact isPartialBijection_append inv.partialBij
                      (by
                        rw [← lookupForward_eq_none_iff, ← lookupForwardEdge_eq_lookupForward]
                        exact hlu)
                      (by
                        have := output_not_mem_of_avoidsOccupied (capacityPart p)
                          (zeroState p.capacityBytes) T_pub (x := u) (y := z) hz_occ
                        simpa only [toPairs, List.map_map, Function.comp_def] using this)
                  capFree := by
                    rw [hrec]
                    exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                      T_pub inv.capFree ⟨u, z, false⟩ hz_occ
                  keysNodup := by
                    rw [map_fst_eraseHiddenKey_of_nodup p hid inv.keysNodup bs]
                    exact inv.keysNodup.erase bs
                  keysNonempty := fun entry he =>
                    inv.keysNonempty entry (List.mem_filter.mp he).1
                  keysUncovered := fun entry he => by
                    have hm := List.mem_filter.mp he
                    have hne : entry.1 ≠ bs := decide_eq_true_eq.mp hm.2
                    exact hEval.2 entry.1 (inv.keysNonempty entry hm.1) hne
                      (inv.keysUncovered entry hm.1)
                  prefixClosed := fun entry he => by
                    have hm := List.mem_filter.mp he
                    by_cases hdp : entry.1.dropLast = bs
                    · rw [hdp, hEval.1]
                      exact Or.inl (by simp only [Option.isSome_some])
                    · rcases inv.prefixClosed entry hm.1 with h1 | h2
                      · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast
                          with
                        | none => rw [hev] at h1; cases h1
                        | some s =>
                          rw [hrec, evalAbsorption_mono p hev]
                          exact Or.inl (by simp only [Option.isSome_some])
                      · rw [map_fst_eraseHiddenKey_of_nodup p hid inv.keysNodup bs]
                        exact Or.inr ((List.mem_erase_of_ne hdp).mpr h2)
                  capsDisjoint := fun c hc => by
                    rcases List.mem_map.mp hc with ⟨entry, he, rfl⟩
                    have hm := List.mem_filter.mp he
                    have hne_key : entry.1 ≠ bs := decide_eq_true_eq.mp hm.2
                    rw [hrec]
                    simp only [occupiedCapsList, List.map_append, List.map_cons, List.map_nil,
                      List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
                    rintro (h0 | (h1 | h2) | (h3 | h4))
                    · exact inv.capsDisjoint _ (List.mem_map_of_mem hm.1)
                        (by simp only [occupiedCapsList, List.mem_cons, h0, true_or])
                    · exact inv.capsDisjoint _ (List.mem_map_of_mem hm.1)
                        (by simp only [occupiedCapsList, List.mem_cons, List.mem_append, h1,
                          true_or, or_true])
                    · exact inv.capsDisjoint _ (List.mem_map_of_mem hm.1) (h2 ▸ hx_cap)
                    · exact inv.capsDisjoint _ (List.mem_map_of_mem hm.1)
                        (by simp only [occupiedCapsList, List.mem_cons, List.mem_append, h3,
                          or_true])
                    · have hnd_c := inv.capsNodup
                      obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hm.1
                      obtain ⟨j, hj, hgj⟩ := List.getElem_of_mem hz_mem
                      have hij : i ≠ j := by
                        intro hEq; subst hEq; rw [hgi] at hgj
                        exact hne_key (congrArg Prod.fst hgj)
                      have hcap_eq : (hiddenCapsList p hid)[i]'(by
                          rw [length_hiddenCapsList]; exact hi) =
                        (hiddenCapsList p hid)[j]'(by
                          rw [length_hiddenCapsList]; exact hj) := by
                        simp only [hiddenCapsList, List.getElem_map, hgi, hgj]
                        exact h4
                      exact hij (congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd_c)
                        (a₁ := ⟨i, by rw [length_hiddenCapsList]; exact hi⟩)
                        (a₂ := ⟨j, by rw [length_hiddenCapsList]; exact hj⟩) hcap_eq))
                  capsNodup := by
                    have hsub : (eraseHiddenKey p hid bs).Sublist hid := List.filter_sublist
                    exact inv.capsNodup.sublist (hsub.map _) }
            · simp only [hmem, ↓reduceIte] at hsupp
              rcases hmap_supp _ _ _ hsupp with ⟨y0, _, hEq⟩
              have h1 := congrArg (fun q => q.1.1.1) hEq
              have h2 := congrArg (fun q => q.1.1.2) hEq
              have h3 := congrArg (fun q => q.1.2) hEq
              dsimp only at h1 h2 h3; subst h1; subst h2
              simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
                List.mem_append, not_or] at h3
              rcases h3 with ⟨hx_not_hid, hy_not_occ, hy_not_hid⟩
              have hy_occ : capacityPart p y0 ∉
                  occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
                rwa [← mem_occupiedCapsList_iff]
              have hrec : recordForwardEdge T_pub u y0 = T_pub ++ [⟨u, y0, false⟩] :=
                recordForwardEdge_eq_append_of_avoids p T_pub hy_occ
              have hEval := evalAbsorption_recordForwardEdge_of_rootedPrefix p M hp encode T_pub
                inv.partialBij inv.capFree hlu hy_not_occ hrp
              refine
                { partialBij := by
                    rw [hrec]
                    have htp : toPairs (T_pub ++ [⟨u, y0, false⟩]) = toPairs T_pub ++ [(u,
                      y0)] := by
                      simp only [toPairs, List.map_append, List.map_singleton]
                    rw [htp]
                    exact isPartialBijection_append inv.partialBij
                      (by
                        rw [← lookupForward_eq_none_iff, ← lookupForwardEdge_eq_lookupForward]
                        exact hlu)
                      (by
                        have := output_not_mem_of_avoidsOccupied (capacityPart p)
                          (zeroState p.capacityBytes) T_pub (x := u) (y := y0) hy_occ
                        simpa only [toPairs, List.map_map, Function.comp_def] using this)
                  capFree := by
                    rw [hrec]
                    exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                      T_pub inv.capFree ⟨u, y0, false⟩ hy_occ
                  keysNodup := inv.keysNodup
                  keysNonempty := inv.keysNonempty
                  keysUncovered := fun entry he =>
                    hEval.2 entry.1 (inv.keysNonempty entry he)
                      (fun hEq => hmem (hEq ▸ List.mem_map_of_mem he))
                      (inv.keysUncovered entry he)
                  prefixClosed := fun entry he => by
                    rcases inv.prefixClosed entry he with h1 | h2
                    · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast
                        with
                      | none => rw [hev] at h1; cases h1
                      | some s =>
                        rw [hrec, evalAbsorption_mono p hev]
                        exact Or.inl (by simp only [Option.isSome_some])
                    · exact Or.inr h2
                  capsDisjoint := fun c hc => by
                    rw [hrec]
                    simp only [occupiedCapsList, List.map_append, List.map_cons, List.map_nil,
                      List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
                    rintro (h0 | (h1 | h2) | (h3 | h4))
                    · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                        h0, true_or])
                    · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                        List.mem_append, h1, true_or, or_true])
                    · exact hx_not_hid (h2 ▸ hc)
                    · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                        List.mem_append, h3, or_true])
                    · exact hy_not_hid (h4 ▸ hc)
                  capsNodup := inv.capsNodup }
          | none =>
            rw [hrp] at hsupp
            rcases hmap_supp _ _ _ hsupp with ⟨y0, _, hEq⟩
            have h1 := congrArg (fun q => q.1.1.1) hEq
            have h2 := congrArg (fun q => q.1.1.2) hEq
            have h3 := congrArg (fun q => q.1.2) hEq
            dsimp only at h1 h2 h3; subst h1; subst h2
            simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
              List.mem_append, not_or] at h3
            rcases h3 with ⟨hx_not_hid, hy_not_occ, hy_not_hid⟩
            have hy_occ : capacityPart p y0 ∉
                occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
              rwa [← mem_occupiedCapsList_iff]
            have hrec : recordForwardEdge T_pub u y0 = T_pub ++ [⟨u, y0, false⟩] :=
              recordForwardEdge_eq_append_of_avoids p T_pub hy_occ
            refine
              { partialBij := by
                  rw [hrec]
                  have htp : toPairs (T_pub ++ [⟨u, y0, false⟩]) = toPairs T_pub ++ [(u, y0)] := by
                    simp only [toPairs, List.map_append, List.map_singleton]
                  rw [htp]
                  exact isPartialBijection_append inv.partialBij
                    (by
                      rw [← lookupForward_eq_none_iff, ← lookupForwardEdge_eq_lookupForward]
                      exact hlu)
                    (by
                      have := output_not_mem_of_avoidsOccupied (capacityPart p)
                        (zeroState p.capacityBytes) T_pub (x := u) (y := y0) hy_occ
                      simpa only [toPairs, List.map_map, Function.comp_def] using this)
                capFree := by
                  rw [hrec]
                  exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                    T_pub inv.capFree ⟨u, y0, false⟩ hy_occ
                keysNodup := inv.keysNodup
                keysNonempty := inv.keysNonempty
                keysUncovered := fun entry he =>
                  evalAbsorption_recordForwardEdge_of_rootedPrefix_none p M hp encode T_pub
                    inv.partialBij inv.capFree hy_not_occ hrp entry.1
                    (inv.keysNonempty entry he) (inv.keysUncovered entry he)
                prefixClosed := fun entry he => by
                  rcases inv.prefixClosed entry he with h1 | h2
                  · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast
                      with
                    | none => rw [hev] at h1; cases h1
                    | some s =>
                      rw [hrec, evalAbsorption_mono p hev]
                      exact Or.inl (by simp only [Option.isSome_some])
                  · exact Or.inr h2
                capsDisjoint := fun c hc => by
                  rw [hrec]
                  simp only [occupiedCapsList, List.map_append, List.map_cons, List.map_nil,
                    List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
                  rintro (h0 | (h1 | h2) | (h3 | h4))
                  · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                      h0, true_or])
                  · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                      List.mem_append, h1, true_or, or_true])
                  · exact hx_not_hid (h2 ▸ hc)
                  · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                      List.mem_append, h3, or_true])
                  · exact hy_not_hid (h4 ▸ hc)
                capsNodup := inv.capsNodup }
      | inverse =>
        dsimp only [lazyPathGameStep] at hsupp
        cases hlu : lookupInverseEdge T_pub u with
        | some x0 =>
          rw [hlu] at hsupp
          rcases hsing_supp _ _ hsupp with hEq
          have h1 := congrArg (fun q => q.1.1.1) hEq
          have h2 := congrArg (fun q => q.1.1.2) hEq
          dsimp only at h1 h2; subst h1; subst h2
          exact inv
        | none =>
          rw [hlu] at hsupp
          rcases hmap_supp _ _ _ hsupp with ⟨x0, _, hEq⟩
          have h1 := congrArg (fun q => q.1.1.1) hEq
          have h2 := congrArg (fun q => q.1.1.2) hEq
          have h3 := congrArg (fun q => q.1.2) hEq
          dsimp only at h1 h2 h3; subst h1; subst h2
          simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
            List.mem_append, not_or] at h3
          rcases h3 with ⟨hy_not_hid, hx_not_occ, hx_not_hid⟩
          have hx_occ : capacityPart p x0 ∉
              occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
            rwa [← mem_occupiedCapsList_iff]
          have hrec : recordInverseEdge T_pub x0 u = T_pub ++ [⟨x0, u, true⟩] :=
            recordInverseEdge_eq_append_of_avoids p T_pub hx_occ
          refine
            { partialBij := by
                rw [hrec]
                have htp : toPairs (T_pub ++ [⟨x0, u, true⟩]) = toPairs T_pub ++ [(x0, u)] := by
                  simp only [toPairs, List.map_append, List.map_singleton]
                rw [htp]
                exact isPartialBijection_append inv.partialBij
                  (by
                    have := input_not_mem_of_avoidsOccupied (capacityPart p)
                      (zeroState p.capacityBytes) T_pub (x := x0) (y := u) hx_occ
                    simpa only [toPairs, List.map_map, Function.comp_def] using this)
                  (by
                    rw [← lookupInverse_eq_none_iff, ← lookupInverseEdge_eq_lookupInverse]
                    exact hlu)
              capFree := by
                rw [hrec]
                exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                  T_pub inv.capFree ⟨x0, u, true⟩ hx_occ
              keysNodup := inv.keysNodup
              keysNonempty := inv.keysNonempty
              keysUncovered := fun entry he => by
                by_contra hsome
                cases hnew : evalAbsorption p (recordInverseEdge T_pub x0 u)
                    (zeroState p.stateBytes) entry.1 with
                | none => exact hsome hnew
                | some out =>
                  rw [hrec] at hnew
                  have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes)
                      T_pub ⟨x0, u, true⟩ := hx_occ
                  have hinv_false := (no_preexisting_extension p T_pub ⟨x0, u, true⟩ hf entry.1
                    (inv.keysNonempty entry he) hnew (inv.keysUncovered entry he)).1
                  cases hinv_false
              prefixClosed := fun entry he => by
                rcases inv.prefixClosed entry he with h1 | h2
                · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast with
                  | none => rw [hev] at h1; cases h1
                  | some s =>
                    rw [hrec, evalAbsorption_mono p hev]
                    exact Or.inl (by simp only [Option.isSome_some])
                · exact Or.inr h2
              capsDisjoint := fun c hc => by
                rw [hrec]
                simp only [occupiedCapsList, List.map_append, List.map_cons, List.map_nil,
                  List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
                rintro (h0 | (h1 | h2) | (h3 | h4))
                · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                    h0, true_or])
                · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                    List.mem_append, h1, true_or, or_true])
                · exact hx_not_hid (h2 ▸ hc)
                · exact inv.capsDisjoint c hc (by simp only [occupiedCapsList, List.mem_cons,
                    List.mem_append, h3, or_true])
                · exact hy_not_hid (h4 ▸ hc)
              capsNodup := inv.capsNodup }
  · intro ⟨T_pub, hid⟩ o u v inv
    have hlift_good : ∀ {S₁ S₂ : Type} {fK : S₁ × Bool → Distribution (S₂ × Bool)}
        (μ₁ : ProbDist ((S₁ × Bool) × (A.Y o × Bool)))
        (μ₂ : ProbDist ((S₂ × Bool) × (A.Y o × Bool))),
        (μ₁.1.restrict fun q => q.2 = (v, false)).bindK
          (fun q => fK q.1) =
        fTransform Prod.fst (μ₂.1.restrict fun q => q.2 = (v, false)) →
        (fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩) μ₁.1).restrict
            fun sy => sy.2 = ⟨o, (v, false)⟩)).bindK fK =
          fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o,
            u⟩) μ₂.1).restrict
            fun sy => sy.2 = ⟨o, (v, false)⟩) := by
      intro S₁ S₂ fK μ₁ μ₂ hEq
      have hres : ∀ {S : Type} (μ : ProbDist ((S × Bool) × (A.Y o × Bool))),
          fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩) μ.1).restrict
            fun sy => sy.2 = ⟨o, (v, false)⟩) =
          fTransform Prod.fst (μ.1.restrict fun q => q.2 = (v, false)) := by
        intro S μ
        rw [Distribution.restrict_fTransform, fTransform_fTransform]
        have hpred : ∀ q : (S × Bool) × (A.Y o × Bool),
            ((ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩ q).2 =
              (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i)) ↔ q.2 = (v, false) := fun q => by
          simp only [ProbStep.tagged, Sigma.mk.inj_iff, heq_eq_eq, true_and]
        rw [Distribution.restrict_congr _ hpred]
        rfl
      rw [hres μ₁, hres μ₂, bindK_fTransform]
      exact hEq
    have hlift_good' : ∀ (μ₁ : ProbDist (((List (PermutationEdge (ByteState p.stateBytes)) ×
            List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
          (A.Y o × Bool)))
        (μ₂ : ((M → ByteState p.outputBytes) ×
            List (PermutationEdge (ByteState p.stateBytes)) ×
            List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) →
          ProbDist ((((M → ByteState p.outputBytes) ×
            List (PermutationEdge (ByteState p.stateBytes)) ×
            List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
          (A.Y o × Bool))),
        (μ₁.1.restrict fun q => q.2 = (v, false)).bindK
          (fun q => if q.1.2 = false then ((K q.1.1).map fun s₂ => (s₂, false)).1 else 0) =
        (K (T_pub, hid)).1.bindK (fun s₂ =>
          fTransform Prod.fst ((μ₂ s₂).1.restrict fun q => q.2 = (v, false))) →
        (fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩) μ₁.1).restrict
            fun sy => sy.2 = ⟨o, (v, false)⟩)).bindK
          (fun sb => if sb.2 = false then ((K sb.1).map fun s₂ => (s₂, false)).1 else 0) =
        (K (T_pub, hid)).1.bindK fun s₂ =>
          fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩)
            (μ₂ s₂).1).restrict fun sy => sy.2 = ⟨o, (v, false)⟩) := by
      intro μ₁ μ₂ hEq
      have hres : ∀ {S : Type} (μ : ProbDist ((S × Bool) × (A.Y o × Bool))),
          fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩) μ.1).restrict
            fun sy => sy.2 = ⟨o, (v, false)⟩) =
          fTransform Prod.fst (μ.1.restrict fun q => q.2 = (v, false)) := by
        intro S μ
        rw [Distribution.restrict_fTransform, fTransform_fTransform]
        have hpred : ∀ q : (S × Bool) × (A.Y o × Bool),
            ((ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩ q).2 =
              (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i)) ↔ q.2 = (v, false) := fun q => by
          simp only [ProbStep.tagged, Sigma.mk.inj_iff, heq_eq_eq, true_and]
        rw [Distribution.restrict_congr _ hpred]
        rfl
      rw [hres μ₁, bindK_fTransform]
      simp_rw [hres]
      exact hEq
    apply hlift_good'
    rcases o with o | o
    · cases o
      dsimp only [lazyPathGameStep, idealSpongeGameStep]
      set blocks := paddedBlocks p (encode u)
      set added := newHiddenPrefixes p T_pub (hid.map Prod.fst) blocks
      have hsim_add := sampleHiddenPrefixesWithBad_sim_ro p M hp henc T_pub hid added
        ((nonemptyPrefixes_nodup _).filter _)
        (fun bs hbs => by
          have hf := (List.mem_filter.mp hbs).2
          rw [Bool.and_eq_true] at hf
          refine ⟨Option.isNone_iff_eq_none.mp hf.1, ?_⟩
          have hnc := hf.2
          intro hmem
          have hc := List.contains_iff_mem.mpr hmem
          rw [hc] at hnc; cases hnc)
      have hbl_mem : blocks ∈ nonemptyPrefixes blocks := by
        unfold nonemptyPrefixes
        have hpos : 0 < blocks.length := List.length_pos_of_ne_nil (paddedBlocks_ne_nil p hp.1 _)
        refine List.mem_map.mpr ⟨blocks.length - 1, List.mem_range.mpr (by omega), ?_⟩
        rw [Nat.sub_add_cancel hpos, List.take_length]
      have hdig_eq : ∀ hid' : List (List (ByteState p.rateBytes) × ByteState p.stateBytes),
          (hid', false) ∈ (sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes])
            T_pub hid false added).1.support →
          ∀ ro ∈ (roCompleteOfState p M encode T_pub hid').1.support,
            ro u = digestPart p ((evalAbsorption p T_pub (zeroState p.stateBytes) blocks).getD
              ((hid'.lookup blocks).getD (zeroState p.stateBytes))) := by
        intro hid' hmem ro hro
        have hInv' := hInv_sample T_pub hid inv added
          ((nonemptyPrefixes_nodup _).filter _)
          (fun bs hbs => mem_nonemptyPrefixes_ne_nil (List.mem_filter.mp hbs).1)
          (fun bs hbs => by
            have hf := (List.mem_filter.mp hbs).2
            rw [Bool.and_eq_true] at hf
            refine ⟨Option.isNone_iff_eq_none.mp hf.1, ?_⟩
            have hnc := hf.2
            intro hmem
            have hc := List.contains_iff_mem.mpr hmem
            rw [hc] at hnc; cases hnc)
          (hnew_pc T_pub (hid.map Prod.fst) blocks) hid' hmem
        cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) blocks with
        | some s =>
          simp only [Option.getD_some]
          exact roLaw_support_eq_of_some p M _ (by unfold roOfState; rw [hev]) hro
        | none =>
          have hbl_in : blocks ∈ hid'.map Prod.fst := by
            by_cases hm0 : blocks ∈ hid.map Prod.fst
            · exact hInv'.2.2 blocks hm0
            · refine hInv'.2.1 blocks (List.mem_filter.mpr ⟨hbl_mem, ?_⟩)
              rw [Bool.and_eq_true]
              refine ⟨by rw [hev]; rfl, ?_⟩
              rw [Bool.not_eq_true', Bool.eq_false_iff]
              intro hcon
              exact hm0 (List.contains_iff_mem.mp hcon)
          obtain ⟨z, hz_lu, _⟩ := lookup_eq_some_of_mem_map_fst hid' hbl_in
          simp only [Option.getD_none, hz_lu, Option.getD_some]
          exact roLaw_support_eq_of_some p M _
            (by unfold roOfState; rw [hev, hz_lu]; rfl) hro
      have hres_ro :
          (((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub hid false
              added).1.restrict fun p' => p'.2 = false).bindK fun p' =>
            ((roCompleteOfState p M encode T_pub p'.1).map fun ro => (ro, p'.1)).1).restrict
              (fun rp => rp.1 u = v) =
          ((roCompleteOfState p M encode T_pub hid).1.bindK fun ro =>
            fTransform (fun p' => (ro, p'.1))
              ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hid false
                added).1.restrict fun p' => p'.2 = false)).restrict
              (fun rp => rp.1 u = v) := congrArg (fun d => d.restrict fun rp => rp.1 u = v) hsim_add
      have hmap_lift := congrArg (fTransform fun rp : (M → ByteState p.outputBytes) ×
          List (List (ByteState p.rateBytes) × ByteState p.stateBytes) =>
            ((rp.1, T_pub, rp.2), false)) hres_ro
      rw [Distribution.restrict_bindK, fTransform_bindK] at hmap_lift
      rw [Distribution.restrict_bindK, fTransform_bindK] at hmap_lift
      have hlhs_match :
          (((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub hid false
              added).map fun p' =>
                let s := (evalAbsorption p T_pub (zeroState p.stateBytes) blocks).getD
                  ((p'.1.lookup blocks).getD (zeroState p.stateBytes))
                (((T_pub, p'.1), p'.2), (digestPart p s, p'.2))).1.restrict
                fun q => q.2 = (v, false)).bindK
            (fun q => if q.1.2 = false then ((K q.1.1).map fun s₂ => (s₂, false)).1 else 0) =
          ((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub hid false
              added).1.restrict fun p' => p'.2 = false).bindK fun p' =>
            fTransform (fun rp => ((rp.1, T_pub, rp.2), false))
              (((roCompleteOfState p M encode T_pub p'.1).map fun ro => (ro, p'.1)).1.restrict
                fun rp => rp.1 u = v) := by
        rw [ProbDist.map_val, Distribution.restrict_fTransform, bindK_fTransform]
        ext s₂b
        rw [bindK_apply, bindK_apply]
        simp only [Finsupp.sum]
        have hsub : ((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub hid
            false added).1.restrict fun p' =>
              (digestPart p ((evalAbsorption p T_pub (zeroState p.stateBytes) blocks).getD
                ((p'.1.lookup blocks).getD (zeroState p.stateBytes))), p'.2) = (v, false)).support ⊆
            ((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub hid
              false added).1.restrict fun p' => p'.2 = false).support := by
          intro p' hp'
          rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply] at hp' ⊢
          split_ifs at hp' with h1
          · rw [ite_eq_left (congrArg Prod.snd h1)]
            exact hp'
          · exact False.elim (hp' rfl)
        rw [Finset.sum_subset hsub]
        · apply Finset.sum_congr rfl
          intro p' hp'
          have hp'_mem : p' ∈ (sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes])
              T_pub hid false added).1.support ∧ p'.2 = false := by
            rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply] at hp'
            split_ifs at hp' with h2
            · exact ⟨Finsupp.mem_support_iff.mpr hp', h2⟩
            · exact False.elim (hp' rfl)
          rcases p' with ⟨hid', bad'⟩
          have hb : bad' = false := hp'_mem.2
          subst hb
          by_cases hdv : digestPart p ((evalAbsorption p T_pub (zeroState p.stateBytes)
              blocks).getD ((hid'.lookup blocks).getD (zeroState p.stateBytes))) = v
          · conv_lhs =>
              rw [Distribution.restrict, Finsupp.filter_apply]
              dsimp only
              rw [hdv, ite_eq_left rfl]
            conv_rhs =>
              rw [Distribution.restrict, Finsupp.filter_apply]
              dsimp only
              rw [ite_eq_left rfl]
            congr 1
            dsimp only [Function.comp_def, K]
            rw [ite_eq_left rfl, ProbDist.map_val, ProbDist.map_val, ProbDist.map_val,
              fTransform_fTransform, Distribution.restrict_fTransform, fTransform_fTransform]
            have htr : ∀ ro ∈ (roCompleteOfState p M encode T_pub hid').1.support,
                ro u = v := fun ro hro => (hdig_eq hid' hp'_mem.1 ro hro).trans hdv
            have hreq : ((roCompleteOfState p M encode T_pub hid').1.restrict
                fun ro => ro u = v) = (roCompleteOfState p M encode T_pub hid').1 := by
              ext ro
              rw [Distribution.restrict, Finsupp.filter_apply]
              by_cases hmem : ro ∈ (roCompleteOfState p M encode T_pub hid').1.support
              · rw [ite_eq_left (htr ro hmem)]
              · rw [Finsupp.notMem_support_iff.mp hmem, ite_self]
            rw [hreq]
            rfl
          · conv_lhs =>
              rw [Distribution.restrict, Finsupp.filter_apply]
              dsimp only
              rw [ite_eq_right (fun hEq => hdv (congrArg Prod.fst hEq)), zero_mul]
            conv_rhs =>
              rw [Distribution.restrict, Finsupp.filter_apply]
              dsimp only
              rw [ite_eq_left rfl]
            rw [ProbDist.map_val, Distribution.restrict_fTransform]
            have hfl : ((roCompleteOfState p M encode T_pub hid').1.restrict
                fun ro => ro u = v) = 0 := by
              ext ro
              rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.zero_apply]
              by_cases hmem : ro ∈ (roCompleteOfState p M encode T_pub hid').1.support
              · rw [ite_eq_right (fun hEq => hdv ((hdig_eq hid' hp'_mem.1 ro hmem).symm.trans hEq))]
              · rw [Finsupp.notMem_support_iff.mp hmem, ite_self]
            rw [hfl, fTransform_zero, fTransform_zero, Finsupp.zero_apply, mul_zero]
        · intro p' hp' hnot
          have hneg : ¬ (digestPart p ((evalAbsorption p T_pub (zeroState p.stateBytes)
              blocks).getD ((p'.1.lookup blocks).getD (zeroState p.stateBytes))), p'.2) =
              (v, false) := by
            intro hEq
            apply hnot
            rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply] at hp' ⊢
            split_ifs at hp' with h2
            · rw [ite_eq_left hEq]; exact hp'
            · exact False.elim (hp' rfl)
          rw [Distribution.restrict, Finsupp.filter_apply, ite_eq_right hneg, zero_mul]
      have hrhs_match :
          ((roCompleteOfState p M encode T_pub hid).1.bindK fun ro =>
            fTransform (fun rp => ((rp.1, T_pub, rp.2), false))
              ((fTransform (fun p' => (ro, p'.1))
                ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hid false
                  added).1.restrict fun p' => p'.2 = false)).restrict
                fun rp => rp.1 u = v)) =
          (K (T_pub, hid)).1.bindK fun s₂ =>
            fTransform Prod.fst
              (((sampleHiddenPrefixesWithBad p (nodeLaw p M encode s₂.1) s₂.2.1 s₂.2.2 false
                (newHiddenPrefixes p s₂.2.1 (s₂.2.2.map Prod.fst) blocks)).map
                  fun p' => (((s₂.1, s₂.2.1, p'.1), p'.2), (s₂.1 u, p'.2))).1.restrict
                fun q => q.2 = (v, false)) := by
        simp only [K, ProbDist.map_val, bindK_fTransform, Function.comp_def]
        apply bindK_congr
        intro ro _
        rw [Distribution.restrict_fTransform, fTransform_fTransform,
          Distribution.restrict_fTransform, fTransform_fTransform]
        by_cases hrov : ro u = v
        · have h1 : ∀ p' : List (List (ByteState p.rateBytes) × ByteState p.stateBytes) × Bool,
              ((ro, p'.1).1 u = v) ↔ True := fun _ => iff_true_intro hrov
          have h2 : ∀ p' : List (List (ByteState p.rateBytes) × ByteState p.stateBytes) × Bool,
              ((ro u, p'.2) = (v, false)) ↔ p'.2 = false := fun p' => by
            simp only [Prod.mk.injEq, hrov, true_and]
          have hrt : ∀ μ : Distribution (List (List (ByteState p.rateBytes) ×
              ByteState p.stateBytes) × Bool), μ.restrict (fun _ => True) = μ := fun μ => by
            ext a; rw [Distribution.restrict, Finsupp.filter_apply, ite_eq_left trivial]
          rw [Distribution.restrict_congr _ h1, hrt, Distribution.restrict_congr _ h2]
          ext s₂b
          have hcongr_f : fTransform (fun p' => ((ro, T_pub, p'.1), false))
              ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hid false
                added).1.restrict fun p' => p'.2 = false) =
              fTransform (fun p' => ((ro, T_pub, p'.1), p'.2))
                ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hid false
                  added).1.restrict fun p' => p'.2 = false) := by
            change (Distribution.restrict _ _).sum _ = (Distribution.restrict _ _).sum _
            apply Finsupp.sum_congr
            intro p' hp'
            rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply] at hp'
            split_ifs at hp' with h2'
            · dsimp only; rw [h2']
            · exact False.elim (hp' rfl)
          exact congrArg (fun d => d s₂b) hcongr_f
        · have h1 : ∀ p' : List (List (ByteState p.rateBytes) × ByteState p.stateBytes) × Bool,
              ((ro, p'.1).1 u = v) ↔ False := fun _ => iff_false_intro hrov
          have h2 : ∀ p' : List (List (ByteState p.rateBytes) × ByteState p.stateBytes) × Bool,
              ((ro u, p'.2) = (v, false)) ↔ False := fun _ => by
            simp only [Prod.mk.injEq, hrov, false_and]
          rw [Distribution.restrict_congr _ h1, Distribution.restrict_false,
            Distribution.restrict_congr _ h2, Distribution.restrict_false,
            fTransform_zero, fTransform_zero]
      exact (hlhs_match.trans hmap_lift).trans hrhs_match
    · cases o with
      | forward =>
        dsimp only [lazyPathGameStep, idealSpongeGameStep]
        simp only [K, ProbDist.map_val, bindK_fTransform, Function.comp_def]
        cases hlu : lookupForwardEdge T_pub u with
        | some y0 =>
          dsimp only
          by_cases hyv : y0 = v
          · subst hyv
            have h1 : ∀ {S Y : Type} (s : S) (y : Y),
                ((ProbDist.single ((s, false), (y, false))).1.restrict
                  fun q => q.2 = (y, false)) = (ProbDist.single ((s, false), (y, false))).1 := by
              intro S Y s y
              classical
              ext a
              rw [Distribution.restrict, Finsupp.filter_apply, ProbDist.single,
                Finsupp.single_apply]
              by_cases ha : ((s, false), (y, false)) = a
              · subst ha; simp only [↓reduceIte]
              · simp only [ha, ↓reduceIte, ite_self]
            refine (congrFun (congrArg Distribution.bindK (h1 (T_pub, hid) y0)) _).trans ?_
            refine Eq.trans ?_ (bindK_congr fun ro _ =>
              congrArg (fTransform Prod.fst) (h1 (ro, T_pub, hid) y0).symm)
            rw [ProbDist.single, bindK_single, one_smul, ite_eq_left rfl, fTransform_fTransform]
            change ((roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                Finsupp.single ((ro, T_pub, hid), false) w) =
              (roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                w • fTransform Prod.fst (Finsupp.single (((ro, T_pub, hid), false), (y0,
                  false)) (1 : ℝ))
            apply Finsupp.sum_congr; intro ro _
            rw [fTransform_single, Finsupp.smul_single, smul_eq_mul, mul_one]
          · have h0 : ∀ {S Y : Type} (s : S) (y1 y2 : Y), y1 ≠ y2 →
                ((ProbDist.single ((s, false), (y1, false))).1.restrict
                  fun q => q.2 = (y2, false)) = 0 := by
              intro S Y s y1 y2 hne
              classical
              ext a
              rw [Distribution.restrict, Finsupp.filter_apply, ProbDist.single,
                Finsupp.single_apply,
                Finsupp.zero_apply]
              by_cases ha : ((s, false), (y1, false)) = a
              · subst ha; simp only [Prod.mk.injEq, hne, false_and, ↓reduceIte]
              · simp only [ha, ↓reduceIte, ite_self]
            refine (congrFun (congrArg Distribution.bindK (h0 (T_pub, hid) y0 v hyv)) _).trans ?_
            rw [bindK_zero]
            symm
            exact (bindK_congr fun ro _ =>
              (congrArg (fTransform Prod.fst) (h0 (ro, T_pub, hid) y0 v hyv)).trans
                (fTransform_zero Prod.fst)).trans (bindK_zero_right _)
        | none =>
          dsimp only
          cases hrp : rootedPrefix p M encode T_pub u with
          | some bs =>
            dsimp only
            by_cases hmem : bs ∈ hid.map Prod.fst
            · simp only [hmem, ↓reduceIte]
              obtain ⟨z, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hmem
              simp only [hz_lu, Option.getD_some]
              have hz_cap : capacityPart p z ∉ occupiedCapsList p T_pub :=
                inv.capsDisjoint (capacityPart p z) (List.mem_map_of_mem hz_mem)
              have hEval := evalAbsorption_recordForwardEdge_of_rootedPrefix p M hp encode T_pub
                inv.partialBij inv.capFree hlu hz_cap hrp
              have hro_same : roOfState p M encode (recordForwardEdge T_pub u z)
                  (eraseHiddenKey p hid bs) = roOfState p M encode T_pub hid := by
                funext m
                unfold roOfState
                by_cases hm : paddedBlocks p (encode m) = bs
                · rw [hm, hEval.1, inv.keysUncovered (bs, z) hz_mem, hz_lu]; rfl
                · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes)
                      (paddedBlocks p (encode m)) with
                  | some s =>
                    have hz_occ : capacityPart p z ∉
                        occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
                      rwa [← mem_occupiedCapsList_iff]
                    rw [recordForwardEdge_eq_append_of_avoids p T_pub hz_occ,
                      evalAbsorption_mono p hev]
                  | none =>
                    rw [hEval.2 _ (paddedBlocks_ne_nil p hp.1 _) hm hev,
                      lookup_eraseHiddenKey_of_ne p hid hm]
              by_cases hzv : z = v
              · subst hzv
                have h1 : ∀ {S Y : Type} (s : S) (y : Y),
                    ((ProbDist.single ((s, false), (y, false))).1.restrict
                      fun q => q.2 = (y, false)) = (ProbDist.single ((s, false), (y,
                        false))).1 := by
                  intro S Y s y
                  classical
                  ext a
                  rw [Distribution.restrict, Finsupp.filter_apply, ProbDist.single,
                    Finsupp.single_apply]
                  by_cases ha : ((s, false), (y, false)) = a
                  · subst ha; simp only [↓reduceIte]
                  · simp only [ha, ↓reduceIte, ite_self]
                refine (congrFun (congrArg Distribution.bindK
                  (h1 (recordForwardEdge T_pub u z, eraseHiddenKey p hid bs) z)) _).trans ?_
                refine Eq.trans ?_ (bindK_congr fun ro _ =>
                  congrArg (fTransform Prod.fst)
                    (h1 (ro, recordForwardEdge T_pub u z, eraseHiddenKey p hid bs) z).symm)
                rw [ProbDist.single, bindK_single, one_smul, ite_eq_left rfl,
                  fTransform_fTransform, roCompleteOfState, hro_same]
                change ((roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                    Finsupp.single ((ro, recordForwardEdge T_pub u z,
                      eraseHiddenKey p hid bs), false) w) =
                  (roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                    w • fTransform Prod.fst (Finsupp.single
                      (((ro, recordForwardEdge T_pub u z, eraseHiddenKey p hid bs), false),
                        (z, false)) (1 : ℝ))
                apply Finsupp.sum_congr; intro ro _
                rw [fTransform_single, Finsupp.smul_single, smul_eq_mul, mul_one]
              · have h0 : ∀ {S Y : Type} (s : S) (y1 y2 : Y), y1 ≠ y2 →
                    ((ProbDist.single ((s, false), (y1, false))).1.restrict
                      fun q => q.2 = (y2, false)) = 0 := by
                  intro S Y s y1 y2 hne
                  classical
                  ext a
                  rw [Distribution.restrict, Finsupp.filter_apply, ProbDist.single,
                    Finsupp.single_apply, Finsupp.zero_apply]
                  by_cases ha : ((s, false), (y1, false)) = a
                  · subst ha; simp only [Prod.mk.injEq, hne, false_and, ↓reduceIte]
                  · simp only [ha, ↓reduceIte, ite_self]
                refine (congrFun (congrArg Distribution.bindK
                  (h0 (recordForwardEdge T_pub u z, eraseHiddenKey p hid bs) z v hzv)) _).trans ?_
                rw [bindK_zero]
                symm
                exact (bindK_congr fun ro _ =>
                  (congrArg (fTransform Prod.fst)
                    (h0 (ro, recordForwardEdge T_pub u z, eraseHiddenKey p hid bs) z v hzv)).trans
                    (fTransform_zero Prod.fst)).trans (bindK_zero_right _)
            · simp only [hmem, ↓reduceIte]
              set hitX : Bool := decide (capacityPart p u ∈ hiddenCapsList p hid)
              set occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
              by_cases hbad_v : (false || hitX || decide (capacityPart p v ∈ occ)) = true
              · have hl0 :
                    (((𝒰[ByteState p.stateBytes]).map fun y =>
                      (((recordForwardEdge T_pub u y, hid),
                        false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p y ∈
                            occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                        ((y : A.Y (Sum.inr Bidirectional.Port.forward)),
                          false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                            decide (capacityPart p y ∈
                              occupiedCapsList p T_pub ++ hiddenCapsList p hid)))).1.restrict
                        fun q => q.2 = (v, false)) = 0 := by
                  rw [ProbDist.map_val, Distribution.restrict_fTransform]
                  have hf : ∀ y : ByteState p.stateBytes,
                      (((y : A.Y (Sum.inr Bidirectional.Port.forward)),
                        false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p y ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = (v, false)) ↔
                        False := fun y => by
                    simp only [Prod.mk.injEq, iff_false]
                    rintro ⟨rfl, hfalse⟩
                    rw [hbad_v] at hfalse; cases hfalse
                  rw [Distribution.restrict_congr _ hf, Distribution.restrict_false,
                    fTransform_zero]
                refine (congrFun (congrArg Distribution.bindK hl0) _).trans ?_
                rw [bindK_zero]
                symm
                have hr0 : ∀ ro : M → ByteState p.outputBytes,
                    fTransform Prod.fst ((match completingMessage p encode T_pub u with
                      | some m => (𝒰[ByteState (tailBytes p)]).map fun t =>
                          (((ro, recordForwardEdge T_pub u (assembleState p (ro m) t), hid),
                            false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                              decide (capacityPart p (assembleState p (ro m) t) ∈
                                occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                            (assembleState p (ro m) t,
                              false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                                decide (capacityPart p (assembleState p (ro m) t) ∈
                                  occupiedCapsList p T_pub ++ hiddenCapsList p hid)))
                      | none => (𝒰[ByteState p.stateBytes]).map fun y =>
                          (((ro, recordForwardEdge T_pub u y, hid),
                            false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                              decide (capacityPart p y ∈
                                occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                            (y, false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                              decide (capacityPart p y ∈
                                occupiedCapsList p T_pub ++ hiddenCapsList p hid)))).1.restrict
                      fun q => q.2 = (v, false)) = 0 := by
                  intro ro
                  cases completingMessage p encode T_pub u with
                  | some m =>
                    rw [ProbDist.map_val, Distribution.restrict_fTransform]
                    have hf : ∀ t : ByteState (tailBytes p),
                        ((assembleState p (ro m) t,
                          false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                            decide (capacityPart p (assembleState p (ro m) t) ∈
                              occupiedCapsList p T_pub ++ hiddenCapsList p hid)) =
                            (v, false)) ↔ False := fun t => by
                      simp only [Prod.mk.injEq, iff_false]
                      rintro ⟨hy, hfalse⟩; rw [hy, hbad_v] at hfalse; cases hfalse
                    rw [Distribution.restrict_congr _ hf, Distribution.restrict_false,
                      fTransform_zero, fTransform_zero]
                  | none =>
                    rw [ProbDist.map_val, Distribution.restrict_fTransform]
                    have hf : ∀ y : ByteState p.stateBytes,
                        ((y, false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p y ∈
                            occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = (v, false)) ↔
                          False := fun y => by
                      simp only [Prod.mk.injEq, iff_false]
                      rintro ⟨rfl, hfalse⟩; rw [hbad_v] at hfalse; cases hfalse
                    rw [Distribution.restrict_congr _ hf, Distribution.restrict_false,
                      fTransform_zero, fTransform_zero]
                exact (bindK_congr fun ro _ => hr0 ro).trans (bindK_zero_right _)
              · have hgood_v : (false || hitX || decide (capacityPart p v ∈ occ)) = false :=
                  Bool.eq_false_iff.mpr hbad_v
                have hv_not_occ : capacityPart p v ∉ occupiedCapsList p T_pub := by
                  simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
                    occ, List.mem_append, not_or] at hgood_v
                  exact hgood_v.2.1
                have hv_occ : capacityPart p v ∉
                    occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
                  rwa [← mem_occupiedCapsList_iff]
                cases hcm : completingMessage p encode T_pub u with
                | some m =>
                  have hbs_eq : bs = paddedBlocks p (encode m) := by
                    unfold rootedPrefix at hrp; rw [hcm] at hrp
                    exact (Option.some.inj hrp).symm
                  have hm_none : evalAbsorption p T_pub (zeroState p.stateBytes)
                      (paddedBlocks p (encode m)) = none :=
                    evalAbsorption_none_of_completing p M hp encode henc T_pub inv.partialBij
                      inv.capFree hlu hcm
                  have hm_not_hid : paddedBlocks p (encode m) ∉ hid.map Prod.fst :=
                    hbs_eq ▸ hmem
                  have hro_none : roOfState p M encode T_pub hid m = none := by
                    unfold roOfState; rw [hm_none]
                    have hlu_h : hid.lookup (paddedBlocks p (encode m)) = none := by
                      by_contra hsome
                      cases hl : hid.lookup (paddedBlocks p (encode m)) with
                      | none => exact hsome hl
                      | some z =>
                        exact hm_not_hid (List.mem_map_of_mem (f :=
                          Prod.fst) (mem_of_lookup_eq_some hl))
                    rw [hlu_h]; rfl
                  have hupd : roOfState p M encode (recordForwardEdge T_pub u v) hid =
                      Function.update (roOfState p M encode T_pub hid) m (some (digestPart p v)) :=
                        by
                    funext m'
                    by_cases hm' : m' = m
                    · subst hm'
                      unfold roOfState
                      rw [Function.update_self,
                        evalAbsorption_recordForwardEdge_of_completing p M hp encode henc T_pub
                          inv.partialBij inv.capFree hlu hv_occ hcm]
                    · unfold roOfState
                      rw [Function.update_of_ne hm']
                      cases hev : evalAbsorption p T_pub (zeroState p.stateBytes)
                          (paddedBlocks p (encode m')) with
                      | some s =>
                        rw [recordForwardEdge_eq_append_of_avoids p T_pub hv_occ,
                          evalAbsorption_mono p hev]
                      | none =>
                        have hcm_ne : completingMessage p encode T_pub u ≠ some m' := by
                          rw [hcm]; intro hEq; exact hm' (Option.some.inj hEq).symm
                        rw [evalAbsorption_recordForwardEdge_other_none p M hp encode henc T_pub
                          inv.partialBij inv.capFree hv_occ hev hcm_ne]
                  have hdis :=
                    congrArg (fun d => fTransform (fun rp : (M → ByteState p.outputBytes) ×
                      ByteState p.stateBytes => ((rp.1, recordForwardEdge T_pub u v, hid), false))
                    (d.1.restrict fun rp => rp.2 = v))
                    (roLaw_disintegrate p M hp (roOfState p M encode T_pub hid) m hro_none)
                  simp only [ProbDist.bind_val, ProbDist.map_val, Distribution.restrict_bindK,
                    fTransform_bindK] at hdis
                  have hlhs_dis :
                      (((𝒰[ByteState p.stateBytes]).map fun y =>
                        (((recordForwardEdge T_pub u y, hid),
                          false || hitX || decide (capacityPart p y ∈ occ)),
                          (y, false || hitX || decide (capacityPart p y ∈ occ)))).1.restrict
                          fun q => q.2 = (v, false)).bindK
                        (fun q => if q.1.2 = false then
                          fTransform (fun s₂ => (s₂, false))
                            (fTransform (fun ro => (ro, q.1.1.1, q.1.1.2))
                              (roCompleteOfState p M encode q.1.1.1 q.1.1.2).1) else 0) =
                      ((𝒰[ByteState p.stateBytes]).1.bindK fun z =>
                        fTransform (fun rp => ((rp.1, recordForwardEdge T_pub u v, hid), false))
                          ((fTransform (fun ro => (ro, z))
                            (roLaw p M (Function.update (roOfState p M encode T_pub hid) m
                              (some (digestPart p z)))).1).restrict fun rp => rp.2 = v)) := by
                    rw [ProbDist.map_val, Distribution.restrict_fTransform, bindK_fTransform]
                    have hfilt : ((𝒰[ByteState p.stateBytes]).1.restrict fun y =>
                        (y, false || hitX || decide (capacityPart p y ∈ occ)) = (v, false)) =
                        Finsupp.single v ((𝒰[ByteState p.stateBytes]).1 v) := by
                      ext y
                      rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.single_apply]
                      by_cases hy : y = v
                      · subst hy; simp only [hgood_v, ↓reduceIte]
                      · simp only [Prod.mk.injEq, hy, false_and, ↓reduceIte, Ne.symm hy]
                    rw [hfilt, bindK_single]
                    dsimp only [Function.comp_def]
                    rw [ite_eq_left hgood_v, fTransform_fTransform, roCompleteOfState, hupd]
                    have hrhs_s : ∀ z : ByteState p.stateBytes,
                        fTransform (fun rp => ((rp.1, recordForwardEdge T_pub u v, hid), false))
                          ((fTransform (fun ro => (ro, z))
                            (roLaw p M (Function.update (roOfState p M encode T_pub hid) m
                              (some (digestPart p z)))).1).restrict fun rp => rp.2 = v) =
                        if z = v then
                          fTransform (fun ro => ((ro, recordForwardEdge T_pub u v, hid), false))
                            (roLaw p M (Function.update (roOfState p M encode T_pub hid) m
                              (some (digestPart p v)))).1
                        else 0 := by
                      intro z
                      rw [Distribution.restrict_fTransform, fTransform_fTransform]
                      by_cases hz : z = v
                      · subst hz
                        rw [ite_eq_left rfl]
                        have hrt : (roLaw p M (Function.update (roOfState p M encode T_pub hid) m
                            (some (digestPart p z)))).1.restrict (fun _ => z = z) =
                            (roLaw p M (Function.update (roOfState p M encode T_pub hid) m
                              (some (digestPart p z)))).1 := by
                          ext a; rw [Distribution.restrict, Finsupp.filter_apply, ite_eq_left rfl]
                        rw [hrt]; rfl
                      · rw [ite_eq_right hz]
                        have hf : ∀ ro : M → ByteState p.outputBytes, ((ro, z).2 = v) ↔ False :=
                          fun _ => iff_false_intro hz
                        rw [Distribution.restrict_congr _ hf, Distribution.restrict_false,
                          fTransform_zero]
                    simp_rw [hrhs_s]
                    ext s₂b
                    rw [bindK_apply, Finsupp.sum, Finsupp.smul_apply, smul_eq_mul]
                    symm
                    refine (Finset.sum_eq_single v ?_ ?_).trans ?_
                    · intro z _ hne; rw [ite_eq_right hne, Finsupp.zero_apply, mul_zero]
                    · intro hnot
                      rw [Finsupp.notMem_support_iff.mp hnot, zero_mul]
                    · rw [ite_eq_left rfl]; rfl
                  have hrhs_dis :
                      ((roLaw p M (roOfState p M encode T_pub hid)).1.bindK fun ro =>
                        fTransform (fun rp => ((rp.1, recordForwardEdge T_pub u v, hid), false))
                          ((fTransform (fun t => (ro, assembleState p (ro m) t))
                            (𝒰[ByteState (tailBytes p)]).1).restrict fun rp => rp.2 = v)) =
                      (roCompleteOfState p M encode T_pub hid).1.bindK fun ro =>
                        fTransform Prod.fst
                          (((𝒰[ByteState (tailBytes p)]).map fun t =>
                            (((ro, recordForwardEdge T_pub u (assembleState p (ro m) t), hid),
                              false || hitX || decide (capacityPart p (assembleState p (ro m) t) ∈
                                occ)),
                              (assembleState p (ro m) t,
                                false || hitX || decide (capacityPart p (assembleState p (ro m) t) ∈
                                  occ)))).1.restrict
                            fun q => q.2 = (v, false)) := by
                    simp only [roCompleteOfState]
                    apply bindK_congr
                    intro ro _
                    rw [ProbDist.map_val, Distribution.restrict_fTransform, fTransform_fTransform,
                      Distribution.restrict_fTransform, fTransform_fTransform]
                    have hpred : ∀ t : ByteState (tailBytes p),
                        ((assembleState p (ro m) t,
                          false || hitX || decide (capacityPart p (assembleState p (ro m) t) ∈ occ))
                            =
                            (v, false)) ↔ assembleState p (ro m) t = v := fun t => by
                      constructor
                      · intro hEq; exact congrArg Prod.fst hEq
                      · intro hEq; exact Prod.ext hEq (by rw [hEq]; exact hgood_v)
                    rw [Distribution.restrict_congr _ hpred]
                    change (Distribution.restrict _ _).sum _ = (Distribution.restrict _ _).sum _
                    apply Finsupp.sum_congr
                    intro t ht
                    rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply] at ht
                    split_ifs at ht with heq
                    · dsimp only [Function.comp_def] at heq ⊢
                      rw [heq, hgood_v]
                    · exact False.elim (ht rfl)
                  exact (hlhs_dis.trans hdis).trans hrhs_dis
                | none =>
                  have hro_same : roOfState p M encode (recordForwardEdge T_pub u v) hid =
                      roOfState p M encode T_pub hid := by
                    funext m'
                    unfold roOfState
                    cases hev : evalAbsorption p T_pub (zeroState p.stateBytes)
                        (paddedBlocks p (encode m')) with
                    | some s =>
                      rw [recordForwardEdge_eq_append_of_avoids p T_pub hv_occ,
                        evalAbsorption_mono p hev]
                    | none =>
                      have hcm_ne : completingMessage p encode T_pub u ≠ some m' := by
                        rw [hcm]; intro hEq; cases hEq
                      rw [evalAbsorption_recordForwardEdge_other_none p M hp encode henc T_pub
                        inv.partialBij inv.capFree hv_occ hev hcm_ne]
                  rw [ProbDist.map_val, Distribution.restrict_fTransform, bindK_fTransform]
                  have hfilt : ((𝒰[ByteState p.stateBytes]).1.restrict fun y =>
                      (y, false || hitX || decide (capacityPart p y ∈ occ)) = (v, false)) =
                      Finsupp.single v ((𝒰[ByteState p.stateBytes]).1 v) := by
                    ext y
                    rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.single_apply]
                    by_cases hy : y = v
                    · subst hy; simp only [hgood_v, ↓reduceIte]
                    · simp only [Prod.mk.injEq, hy, false_and, ↓reduceIte, Ne.symm hy]
                  rw [hfilt, bindK_single]
                  dsimp only [Function.comp_def]
                  rw [ite_eq_left hgood_v, fTransform_fTransform, roCompleteOfState, hro_same]
                  have hrhs_s : ∀ ro : M → ByteState p.outputBytes,
                      fTransform Prod.fst (((𝒰[ByteState p.stateBytes]).map fun y =>
                        (((ro, recordForwardEdge T_pub u y, hid),
                          false || hitX || decide (capacityPart p y ∈ occ)),
                          (y, false || hitX || decide (capacityPart p y ∈ occ)))).1.restrict
                        fun q => q.2 = (v, false)) =
                      ((𝒰[ByteState p.stateBytes]).1 v) •
                        Finsupp.single ((ro, recordForwardEdge T_pub u v, hid), false) (1 : ℝ) := by
                    intro ro
                    rw [ProbDist.map_val, Distribution.restrict_fTransform, fTransform_fTransform,
                      hfilt, fTransform_single, Finsupp.smul_single, smul_eq_mul, mul_one]
                    simp only [Function.comp_def, hgood_v]
                  refine Eq.trans ?_ (bindK_congr fun ro _ => (hrhs_s ro).symm)
                  ext s₂b
                  rw [Finsupp.smul_apply, smul_eq_mul, bindK_apply]
                  change ((𝒰[ByteState p.stateBytes]).1 v) *
                      ((roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                        Finsupp.single ((ro, recordForwardEdge T_pub u v, hid), false) w) s₂b =
                    (roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                      w * (((𝒰[ByteState p.stateBytes]).1 v) •
                        Finsupp.single ((ro, recordForwardEdge T_pub u v, hid), false) (1 : ℝ)) s₂b
                  rw [Finsupp.sum_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro ro _
                  classical
                  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Finsupp.single_apply]
                  split_ifs <;> ring
          | none =>
            dsimp only
            set hitX : Bool := decide (capacityPart p u ∈ hiddenCapsList p hid)
            set occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
            have hcm : completingMessage p encode T_pub u = none := by
              unfold rootedPrefix at hrp
              cases hc : completingMessage p encode T_pub u with
              | none => rfl
              | some m => rw [hc] at hrp; cases hrp
            rw [hcm]
            by_cases hbad_v : (false || hitX || decide (capacityPart p v ∈ occ)) = true
            · have hl0 :
                  (((𝒰[ByteState p.stateBytes]).map fun y =>
                    (((recordForwardEdge T_pub u y, hid),
                      false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p y ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                      ((y : A.Y (Sum.inr Bidirectional.Port.forward)),
                        false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p y ∈
                            occupiedCapsList p T_pub ++ hiddenCapsList p hid)))).1.restrict
                      fun q => q.2 = (v, false)) = 0 := by
                rw [ProbDist.map_val, Distribution.restrict_fTransform]
                have hf : ∀ y : ByteState p.stateBytes,
                    (((y : A.Y (Sum.inr Bidirectional.Port.forward)),
                      false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p y ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = (v, false)) ↔
                      False := fun y => by
                  simp only [Prod.mk.injEq, iff_false]
                  rintro ⟨rfl, hfalse⟩; rw [hbad_v] at hfalse; cases hfalse
                rw [Distribution.restrict_congr _ hf, Distribution.restrict_false, fTransform_zero]
              refine (congrFun (congrArg Distribution.bindK hl0) _).trans ?_
              rw [bindK_zero]
              symm
              have hr0 : ∀ ro : M → ByteState p.outputBytes,
                  fTransform Prod.fst (((𝒰[ByteState p.stateBytes]).map fun y =>
                    (((ro, recordForwardEdge T_pub u y, hid),
                      false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p y ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                      (y, false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p y ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid)))).1.restrict
                    fun q => q.2 = (v, false)) = 0 := by
                intro ro
                rw [ProbDist.map_val, Distribution.restrict_fTransform]
                have hf : ∀ y : ByteState p.stateBytes,
                    ((y, false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p y ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = (v, false)) ↔
                      False := fun y => by
                  simp only [Prod.mk.injEq, iff_false]
                  rintro ⟨rfl, hfalse⟩; rw [hbad_v] at hfalse; cases hfalse
                rw [Distribution.restrict_congr _ hf, Distribution.restrict_false,
                  fTransform_zero, fTransform_zero]
              exact (bindK_congr fun ro _ => hr0 ro).trans (bindK_zero_right _)
            · have hgood_v : (false || hitX || decide (capacityPart p v ∈ occ)) = false :=
                Bool.eq_false_iff.mpr hbad_v
              have hv_occ : capacityPart p v ∉
                  occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
                rw [← mem_occupiedCapsList_iff]
                simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
                  occ, List.mem_append, not_or] at hgood_v
                exact hgood_v.2.1
              have hro_same : roOfState p M encode (recordForwardEdge T_pub u v) hid =
                  roOfState p M encode T_pub hid := by
                funext m'
                unfold roOfState
                cases hev : evalAbsorption p T_pub (zeroState p.stateBytes)
                    (paddedBlocks p (encode m')) with
                | some s =>
                  rw [recordForwardEdge_eq_append_of_avoids p T_pub hv_occ,
                    evalAbsorption_mono p hev]
                | none =>
                  have hcm_ne : completingMessage p encode T_pub u ≠ some m' := by
                    rw [hcm]; intro hEq; cases hEq
                  rw [evalAbsorption_recordForwardEdge_other_none p M hp encode henc T_pub
                    inv.partialBij inv.capFree hv_occ hev hcm_ne]
              rw [ProbDist.map_val, Distribution.restrict_fTransform, bindK_fTransform]
              have hfilt : ((𝒰[ByteState p.stateBytes]).1.restrict fun y =>
                  (y, false || hitX || decide (capacityPart p y ∈ occ)) = (v, false)) =
                  Finsupp.single v ((𝒰[ByteState p.stateBytes]).1 v) := by
                ext y
                rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.single_apply]
                by_cases hy : y = v
                · subst hy; simp only [hgood_v, ↓reduceIte]
                · simp only [Prod.mk.injEq, hy, false_and, ↓reduceIte, Ne.symm hy]
              rw [hfilt, bindK_single]
              dsimp only [Function.comp_def]
              rw [ite_eq_left hgood_v, fTransform_fTransform, roCompleteOfState, hro_same]
              have hrhs_s : ∀ ro : M → ByteState p.outputBytes,
                  fTransform Prod.fst (((𝒰[ByteState p.stateBytes]).map fun y =>
                    (((ro, recordForwardEdge T_pub u y, hid),
                      false || hitX || decide (capacityPart p y ∈ occ)),
                      (y, false || hitX || decide (capacityPart p y ∈ occ)))).1.restrict
                    fun q => q.2 = (v, false)) =
                  ((𝒰[ByteState p.stateBytes]).1 v) •
                    Finsupp.single ((ro, recordForwardEdge T_pub u v, hid), false) (1 : ℝ) := by
                intro ro
                rw [ProbDist.map_val, Distribution.restrict_fTransform, fTransform_fTransform,
                  hfilt, fTransform_single, Finsupp.smul_single, smul_eq_mul, mul_one]
                simp only [Function.comp_def, hgood_v]
              refine Eq.trans ?_ (bindK_congr fun ro _ => (hrhs_s ro).symm)
              ext s₂b
              rw [Finsupp.smul_apply, smul_eq_mul, bindK_apply]
              change ((𝒰[ByteState p.stateBytes]).1 v) *
                  ((roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                    Finsupp.single ((ro, recordForwardEdge T_pub u v, hid), false) w) s₂b =
                (roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                  w * (((𝒰[ByteState p.stateBytes]).1 v) •
                    Finsupp.single ((ro, recordForwardEdge T_pub u v, hid), false) (1 : ℝ)) s₂b
              rw [Finsupp.sum_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ro _
              classical
              rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Finsupp.single_apply]
              split_ifs <;> ring
      | inverse =>
        dsimp only [lazyPathGameStep, idealSpongeGameStep]
        simp only [K, ProbDist.map_val, bindK_fTransform, Function.comp_def]
        cases hlu : lookupInverseEdge T_pub u with
        | some x0 =>
          dsimp only
          by_cases hxv : x0 = v
          · subst hxv
            have h1 : ∀ {S Y : Type} (s : S) (y : Y),
                ((ProbDist.single ((s, false), (y, false))).1.restrict
                  fun q => q.2 = (y, false)) = (ProbDist.single ((s, false), (y, false))).1 := by
              intro S Y s y
              classical
              ext a
              rw [Distribution.restrict, Finsupp.filter_apply, ProbDist.single,
                Finsupp.single_apply]
              by_cases ha : ((s, false), (y, false)) = a
              · subst ha; simp only [↓reduceIte]
              · simp only [ha, ↓reduceIte, ite_self]
            refine (congrFun (congrArg Distribution.bindK (h1 (T_pub, hid) x0)) _).trans ?_
            refine Eq.trans ?_ (bindK_congr fun ro _ =>
              congrArg (fTransform Prod.fst) (h1 (ro, T_pub, hid) x0).symm)
            rw [ProbDist.single, bindK_single, one_smul, ite_eq_left rfl, fTransform_fTransform]
            change ((roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                Finsupp.single ((ro, T_pub, hid), false) w) =
              (roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                w • fTransform Prod.fst (Finsupp.single (((ro, T_pub, hid), false), (x0,
                  false)) (1 : ℝ))
            apply Finsupp.sum_congr; intro ro _
            rw [fTransform_single, Finsupp.smul_single, smul_eq_mul, mul_one]
          · have h0 : ∀ {S Y : Type} (s : S) (y1 y2 : Y), y1 ≠ y2 →
                ((ProbDist.single ((s, false), (y1, false))).1.restrict
                  fun q => q.2 = (y2, false)) = 0 := by
              intro S Y s y1 y2 hne
              classical
              ext a
              rw [Distribution.restrict, Finsupp.filter_apply, ProbDist.single,
                Finsupp.single_apply,
                Finsupp.zero_apply]
              by_cases ha : ((s, false), (y1, false)) = a
              · subst ha; simp only [Prod.mk.injEq, hne, false_and, ↓reduceIte]
              · simp only [ha, ↓reduceIte, ite_self]
            refine (congrFun (congrArg Distribution.bindK (h0 (T_pub, hid) x0 v hxv)) _).trans ?_
            rw [bindK_zero]
            symm
            exact (bindK_congr fun ro _ =>
              (congrArg (fTransform Prod.fst) (h0 (ro, T_pub, hid) x0 v hxv)).trans
                (fTransform_zero Prod.fst)).trans (bindK_zero_right _)
        | none =>
          dsimp only
          set hitY : Bool := decide (capacityPart p u ∈ hiddenCapsList p hid)
          set occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
          by_cases hbad_v : (false || hitY || decide (capacityPart p v ∈ occ)) = true
          · have hl0 :
                (((𝒰[ByteState p.stateBytes]).map fun x =>
                  (((recordInverseEdge T_pub x u, hid),
                    false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p x ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                    ((x : A.Y (Sum.inr Bidirectional.Port.inverse)),
                      false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p x ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid)))).1.restrict
                    fun q => q.2 = (v, false)) = 0 := by
              rw [ProbDist.map_val, Distribution.restrict_fTransform]
              have hf : ∀ x : ByteState p.stateBytes,
                  (((x : A.Y (Sum.inr Bidirectional.Port.inverse)),
                    false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                    decide (capacityPart p x ∈
                      occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = (v, false)) ↔
                    False := fun x => by
                simp only [Prod.mk.injEq, iff_false]
                rintro ⟨rfl, hfalse⟩; rw [hbad_v] at hfalse; cases hfalse
              rw [Distribution.restrict_congr _ hf, Distribution.restrict_false, fTransform_zero]
            refine (congrFun (congrArg Distribution.bindK hl0) _).trans ?_
            rw [bindK_zero]
            symm
            have hr0 : ∀ ro : M → ByteState p.outputBytes,
                fTransform Prod.fst (((𝒰[ByteState p.stateBytes]).map fun x =>
                  (((ro, recordInverseEdge T_pub x u, hid),
                    false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p x ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                    (x, false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p x ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)))).1.restrict
                  fun q => q.2 = (v, false)) = 0 := by
              intro ro
              rw [ProbDist.map_val, Distribution.restrict_fTransform]
              have hf : ∀ x : ByteState p.stateBytes,
                  ((x, false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                    decide (capacityPart p x ∈
                      occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = (v, false)) ↔
                    False := fun x => by
                simp only [Prod.mk.injEq, iff_false]
                rintro ⟨rfl, hfalse⟩; rw [hbad_v] at hfalse; cases hfalse
              rw [Distribution.restrict_congr _ hf, Distribution.restrict_false,
                fTransform_zero, fTransform_zero]
            exact (bindK_congr fun ro _ => hr0 ro).trans (bindK_zero_right _)
          · have hgood_v : (false || hitY || decide (capacityPart p v ∈ occ)) = false :=
              Bool.eq_false_iff.mpr hbad_v
            have hv_occ : capacityPart p v ∉
                occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
              rw [← mem_occupiedCapsList_iff]
              simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
                occ, List.mem_append, not_or] at hgood_v
              exact hgood_v.2.1
            have hro_same : roOfState p M encode (recordInverseEdge T_pub v u) hid =
                roOfState p M encode T_pub hid := by
              funext m'
              unfold roOfState
              cases hev : evalAbsorption p T_pub (zeroState p.stateBytes)
                  (paddedBlocks p (encode m')) with
              | some s =>
                rw [recordInverseEdge_eq_append_of_avoids p T_pub hv_occ,
                  evalAbsorption_mono p hev]
              | none =>
                have hnone' : evalAbsorption p (recordInverseEdge T_pub v u)
                    (zeroState p.stateBytes) (paddedBlocks p (encode m')) = none := by
                  by_contra hsome
                  cases hnew : evalAbsorption p (recordInverseEdge T_pub v u)
                      (zeroState p.stateBytes) (paddedBlocks p (encode m')) with
                  | none => exact hsome hnew
                  | some out =>
                    rw [recordInverseEdge_eq_append_of_avoids p T_pub hv_occ] at hnew
                    have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes)
                        T_pub ⟨v, u, true⟩ := hv_occ
                    have hinv_false := (no_preexisting_extension p T_pub ⟨v, u, true⟩ hf _
                      (paddedBlocks_ne_nil p hp.1 _) hnew hev).1
                    cases hinv_false
                rw [hnone']
            rw [ProbDist.map_val, Distribution.restrict_fTransform, bindK_fTransform]
            have hfilt : ((𝒰[ByteState p.stateBytes]).1.restrict fun x =>
                (x, false || hitY || decide (capacityPart p x ∈ occ)) = (v, false)) =
                Finsupp.single v ((𝒰[ByteState p.stateBytes]).1 v) := by
              ext x
              rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.single_apply]
              by_cases hx : x = v
              · subst hx; simp only [hgood_v, ↓reduceIte]
              · simp only [Prod.mk.injEq, hx, false_and, ↓reduceIte, Ne.symm hx]
            rw [hfilt, bindK_single]
            dsimp only [Function.comp_def]
            rw [ite_eq_left hgood_v, fTransform_fTransform, roCompleteOfState, hro_same]
            have hrhs_s : ∀ ro : M → ByteState p.outputBytes,
                fTransform Prod.fst (((𝒰[ByteState p.stateBytes]).map fun x =>
                  (((ro, recordInverseEdge T_pub x u, hid),
                    false || hitY || decide (capacityPart p x ∈ occ)),
                    (x, false || hitY || decide (capacityPart p x ∈ occ)))).1.restrict
                  fun q => q.2 = (v, false)) =
                ((𝒰[ByteState p.stateBytes]).1 v) •
                  Finsupp.single ((ro, recordInverseEdge T_pub v u, hid), false) (1 : ℝ) := by
              intro ro
              rw [ProbDist.map_val, Distribution.restrict_fTransform, fTransform_fTransform,
                hfilt, fTransform_single, Finsupp.smul_single, smul_eq_mul, mul_one]
              simp only [Function.comp_def, hgood_v]
            refine Eq.trans ?_ (bindK_congr fun ro _ => (hrhs_s ro).symm)
            ext s₂b
            rw [Finsupp.smul_apply, smul_eq_mul, bindK_apply]
            change ((𝒰[ByteState p.stateBytes]).1 v) *
                ((roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                  Finsupp.single ((ro, recordInverseEdge T_pub v u, hid), false) w) s₂b =
              (roCompleteOfState p M encode T_pub hid).1.sum fun ro w =>
                w * (((𝒰[ByteState p.stateBytes]).1 v) •
                  Finsupp.single ((ro, recordInverseEdge T_pub v u, hid), false) (1 : ℝ)) s₂b
            rw [Finsupp.sum_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ro _
            classical
            rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Finsupp.single_apply]
            split_ifs <;> ring

/-! #### Real-world sponge game and equivalence with `lazyPathGame` -/

open Classical in
/-- Sequentially absorb `blocks` against `lazyBidirectionalRFStep`, tracking the public table
`T_pub`, hidden prefixes `hid`, and the monotone bad flag `bad`. -/
noncomputable def absorbRealGameBlocks (q : ℕ)
    (T_full : List (ByteState p.stateBytes × ByteState p.stateBytes))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (bad : Bool) (pref : List (ByteState p.rateBytes)) (state : ByteState p.stateBytes) :
    List (ByteState p.rateBytes) →
    ProbDist (((List (ByteState p.stateBytes × ByteState p.stateBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
      ByteState p.stateBytes)
  | [] => ProbDist.single (((T_full, T_pub, hid), bad), state)
  | block :: rest =>
    let bs := pref ++ [block]
    let x := absorbBlock p state block
    (lazyBidirectionalRFStep q T_full Bidirectional.Port.forward x).bind fun p' =>
      let isNew : Bool :=
        (evalAbsorption p T_pub (zeroState p.stateBytes) bs).isNone &&
          !((hid.map Prod.fst).contains bs)
      let bad' : Bool :=
        if isNew then
          bad || decide (capacityPart p p'.2 ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)
        else bad
      let hid' := if isNew then hid ++ [(bs, p'.2)] else hid
      absorbRealGameBlocks q p'.1 T_pub hid' bad' bs p'.2 rest

omit [Fintype M] [DecidableEq M] in
lemma absorbRealGameBlocks_proj_rf (q : ℕ)
    (T_full : List (ByteState p.stateBytes × ByteState p.stateBytes))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (bad : Bool) (pref : List (ByteState p.rateBytes)) (state : ByteState p.stateBytes)
    (blocks : List (ByteState p.rateBytes)) :
    (absorbRealGameBlocks p q T_full T_pub hid bad pref state blocks).map
        (fun r => (r.1.1.1, r.2)) =
      absorbRFBlocks p q T_full state blocks := by
  induction blocks generalizing T_full hid bad pref state with
  | nil =>
    simp only [absorbRealGameBlocks, absorbRFBlocks]
    apply Subtype.ext
    rw [ProbDist.map_val, ProbDist.single, fTransform_single]
    rfl
  | cons block rest ih =>
    simp only [absorbRealGameBlocks, absorbRFBlocks]
    rw [probDist_map_bind]
    congr 1
    funext p'
    exact ih p'.1 _ _ (pref ++ [block]) p'.2

omit [Fintype M] [DecidableEq M] in
lemma absorbRealGameBlocks_monotone (q : ℕ)
    (T_full : List (ByteState p.stateBytes × ByteState p.stateBytes))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (bad : Bool) (pref : List (ByteState p.rateBytes)) (state : ByteState p.stateBytes)
    (blocks : List (ByteState p.rateBytes))
    (r : ((List (ByteState p.stateBytes × ByteState p.stateBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
      ByteState p.stateBytes)
    (hr : r ∈ (absorbRealGameBlocks p q T_full T_pub hid bad pref state blocks).1.support)
    (hb : bad = true) : r.1.2 = true := by
  subst hb
  induction blocks generalizing T_full hid pref state with
  | nil =>
    simp only [absorbRealGameBlocks, ProbDist.single, Finsupp.mem_support_iff] at hr
    by_contra hne
    apply hr
    apply Finsupp.single_eq_of_ne
    intro hEq
    subst hEq
    exact hne rfl
  | cons block rest ih =>
    simp only [absorbRealGameBlocks, ProbDist.bind_val] at hr
    rw [Finsupp.mem_support_iff, bindK_apply, Finsupp.sum] at hr
    obtain ⟨p', _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
    have hmem : r ∈ (absorbRealGameBlocks p q p'.1 T_pub
        (if ((evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block])).isNone &&
              !(hid.map Prod.fst).contains (pref ++ [block])) = true
            then hid ++ [(pref ++ [block], p'.2)] else hid)
        (if ((evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block])).isNone &&
              !(hid.map Prod.fst).contains (pref ++ [block])) = true
            then true || decide (capacityPart p p'.2 ∈
              occupiedCapsList p T_pub ++ hiddenCapsList p hid) else true)
        (pref ++ [block]) p'.2 rest).1.support :=
      Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
    have hbt : (if ((evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block])).isNone &&
          !(hid.map Prod.fst).contains (pref ++ [block])) = true
        then true || decide (capacityPart p p'.2 ∈
          occupiedCapsList p T_pub ++ hiddenCapsList p hid) else true) = true := by
      split_ifs <;> simp only [Bool.true_or]
    rw [hbt] at hmem
    exact ih p'.1 _ (pref ++ [block]) p'.2 hmem

open Classical in
/-- Real-world sponge game step on `spongePublic • LazyBidirectionalRF`, monitoring capacity
collisions and hidden-node queries while keeping the exact `LazyBidirectionalRF` visible law. -/
noncomputable def realSpongeGameStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    ProbStep ((List (ByteState p.stateBytes × ByteState p.stateBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool)
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (withMBO (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y)
  | ((T_full, T_pub, hid), bad), Sum.inl Evaluation.Port.eval, m =>
    (absorbRealGameBlocks p (w + q_pub) T_full T_pub hid bad [] (zeroState p.stateBytes)
      (paddedBlocks p (encode m))).map fun r => (r.1, (digestPart p r.2, r.1.2))
  | ((T_full, T_pub, hid), bad), Sum.inr Bidirectional.Port.forward, x =>
    (lazyBidirectionalRFStep (w + q_pub) T_full Bidirectional.Port.forward x).map fun p' =>
      match lookupForwardEdge T_pub x with
      | some _ => (((p'.1, T_pub, hid), bad), (p'.2, bad))
      | none =>
        match rootedPrefix p M encode T_pub x with
        | some bs =>
          if bs ∈ hid.map Prod.fst then
            (((p'.1, recordForwardEdge T_pub x p'.2, eraseHiddenKey p hid bs), bad), (p'.2, bad))
          else
            let hitX : Bool := decide (capacityPart p x ∈ hiddenCapsList p hid)
            let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
            let bad' := bad || hitX || decide (capacityPart p p'.2 ∈ occ)
            (((p'.1, recordForwardEdge T_pub x p'.2, hid), bad'), (p'.2, bad'))
        | none =>
          let hitX : Bool := decide (capacityPart p x ∈ hiddenCapsList p hid)
          let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
          let bad' := bad || hitX || decide (capacityPart p p'.2 ∈ occ)
          (((p'.1, recordForwardEdge T_pub x p'.2, hid), bad'), (p'.2, bad'))
  | ((T_full, T_pub, hid), bad), Sum.inr Bidirectional.Port.inverse, y =>
    (lazyBidirectionalRFStep (w + q_pub) T_full Bidirectional.Port.inverse y).map fun p' =>
      match lookupInverseEdge T_pub y with
      | some _ => (((p'.1, T_pub, hid), bad), (p'.2, bad))
      | none =>
        let hitY : Bool := decide (capacityPart p y ∈ hiddenCapsList p hid)
        let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
        let bad' := bad || hitY || decide (capacityPart p p'.2 ∈ occ)
        (((p'.1, recordInverseEdge T_pub p'.2 y, hid), bad'), (p'.2, bad'))

omit [DecidableEq M] in
lemma realSpongeGameStep_flag {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (s : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (b : Bool) (i : (spec.toInterface ⊗ PrimitiveInterface p q_pub).I)
    (x : (spec.toInterface ⊗ PrimitiveInterface p q_pub).X i)
    (q : ((List (ByteState p.stateBytes × ByteState p.stateBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
      ((spec.toInterface ⊗ PrimitiveInterface p q_pub).Y i × Bool))
    (hq : q ∈ (realSpongeGameStep p M spec q_pub (s, b) i x).1.support) :
    q.2.2 = q.1.2 ∧ (b = true → q.1.2 = true) := by
  rcases s with ⟨T_full, T_pub, hid⟩
  have hmap_supp : ∀ {α β : Type} (μ : ProbDist α) (f : α → β) (y : β),
      y ∈ (μ.map f).1.support → ∃ a ∈ μ.1.support, f a = y := fun μ f y hy =>
    mem_support_fTransform f μ.1 hy
  rcases i with i | i
  · cases i
    dsimp only [realSpongeGameStep] at hq
    rcases hmap_supp _ _ _ hq with ⟨r, hr, rfl⟩
    exact ⟨rfl, absorbRealGameBlocks_monotone p (w + q_pub) T_full T_pub hid b []
      (zeroState p.stateBytes) (paddedBlocks p (encode x)) r hr⟩
  · cases i with
    | forward =>
      dsimp only [realSpongeGameStep] at hq
      rcases hmap_supp _ _ _ hq with ⟨p', _, rfl⟩
      cases lookupForwardEdge T_pub x with
      | some _ => exact ⟨rfl, fun h => h⟩
      | none =>
        cases rootedPrefix p M encode T_pub x with
        | some bs =>
          by_cases hmem : bs ∈ hid.map Prod.fst
          · simp only [hmem, ↓reduceIte]; exact ⟨trivial, fun h => h⟩
          · simp only [hmem, ↓reduceIte]
            exact ⟨trivial, fun h => by simp only [h, Bool.true_or]⟩
        | none => exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩
    | inverse =>
      dsimp only [realSpongeGameStep] at hq
      rcases hmap_supp _ _ _ hq with ⟨p', _, rfl⟩
      cases lookupInverseEdge T_pub x with
      | some _ => exact ⟨rfl, fun h => h⟩
      | none => exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩

/-- Real-world sponge game whose visible system equals `spongePublic • LazyBidirectionalRF`. -/
noncomputable def realSpongeGame {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    TypedGame (spec.toInterface ⊗ PrimitiveInterface p q_pub) :=
  TypedGame.ofProbAutomaton (realSpongeGameStep p M spec q_pub) (ProbDist.single ([], [], []))
    (realSpongeGameStep_flag p M spec q_pub)

omit [DecidableEq M] in
/-- The visible system of `realSpongeGame` is `spongePublic • LazyBidirectionalRF`. -/
theorem realSpongeGame_visible {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    (realSpongeGame p M spec q_pub).visible =
      spongePublic p M spec q_pub •
        LazyBidirectionalRF (ByteState p.stateBytes) (w + q_pub) := by
  rw [spongePublic_smul_lazyBidirectionalRF_eq p M spec q_pub, realSpongeGame,
    TypedGame.visible_ofProbAutomaton]
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  let K : ((List (ByteState p.stateBytes × ByteState p.stateBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) →
      ProbDist (List (ByteState p.stateBytes × ByteState p.stateBytes)) :=
    fun sb => ProbDist.single sb.1.1
  have hsim := TypedSystem.ofProbAutomaton_eq_of_simulation (A := A)
    (ProbStep.forgetMBO (realSpongeGameStep p M spec q_pub)) (realRFStep p M spec q_pub) K
    (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (by
      intro _ ⟨⟨T_full, T_pub, hid⟩, bad⟩ ⟨o, u⟩ _ _
      simp only [ProbStep.SimulatesAt, ProbStep.outcome, K, ProbDist.single, bindK_single,
        one_smul, ProbStep.forgetMBO, ProbDist.map_val, fTransform_fTransform, fTransform_single]
      conv_rhs => rw [bindK_single_comp, fTransform_fTransform]
      rcases o with o | o
      · cases o
        dsimp only [realSpongeGameStep, realRFStep]
        have hproj := congrArg Subtype.val (absorbRealGameBlocks_proj_rf p (w + q_pub) T_full
          T_pub hid bad [] (zeroState p.stateBytes) (paddedBlocks p (encode u)))
        rw [ProbDist.map_val] at hproj
        rw [ProbDist.map_val, ProbDist.map_val, fTransform_fTransform, fTransform_fTransform,
          ← hproj, fTransform_fTransform]
        rfl
      · cases o with
        | forward =>
          dsimp only [realSpongeGameStep, realRFStep]
          rw [ProbDist.map_val, fTransform_fTransform]
          have hfn : ((fun x => (x.1.1.1, x.2)) ∘
              (fun p => (p.1, p.2.1)) ∘
              (fun p' : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
                  ByteState p.stateBytes =>
                match lookupForwardEdge T_pub u with
                | some _ => (((p'.1, T_pub, hid), bad), (p'.2, bad))
                | none =>
                  match rootedPrefix p M encode T_pub u with
                  | some bs =>
                    if bs ∈ hid.map Prod.fst then
                      (((p'.1, recordForwardEdge T_pub u p'.2, eraseHiddenKey p hid bs), bad),
                        (p'.2, bad))
                    else
                      (((p'.1, recordForwardEdge T_pub u p'.2, hid),
                        bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p p'.2 ∈
                            occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                        (p'.2, bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p p'.2 ∈
                            occupiedCapsList p T_pub ++ hiddenCapsList p hid)))
                  | none =>
                    (((p'.1, recordForwardEdge T_pub u p'.2, hid),
                      bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p p'.2 ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                      (p'.2, bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p p'.2 ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid))))) = id := by
            funext p'
            dsimp only [Function.comp_def, id_eq]
            cases lookupForwardEdge T_pub u with
            | some _ => rfl
            | none =>
              cases rootedPrefix p M encode T_pub u with
              | some bs => dsimp only; split_ifs <;> rfl
              | none => rfl
          have hfn' : ((fun p => (p.1.1.1, p.2)) ∘
              ((ProbStep.tagged (X := A.X) (Y := A.Y) ⟨Sum.inr Bidirectional.Port.forward, u⟩ ∘
                fun p => (p.1, p.2.1)) ∘
              (fun p' : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
                  ByteState p.stateBytes =>
                match lookupForwardEdge T_pub u with
                | some _ => (((p'.1, T_pub, hid), bad), (p'.2, bad))
                | none =>
                  match rootedPrefix p M encode T_pub u with
                  | some bs =>
                    if bs ∈ hid.map Prod.fst then
                      (((p'.1, recordForwardEdge T_pub u p'.2, eraseHiddenKey p hid bs), bad),
                        (p'.2, bad))
                    else
                      (((p'.1, recordForwardEdge T_pub u p'.2, hid),
                        bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p p'.2 ∈
                            occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                        (p'.2, bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p p'.2 ∈
                            occupiedCapsList p T_pub ++ hiddenCapsList p hid)))
                  | none =>
                    (((p'.1, recordForwardEdge T_pub u p'.2, hid),
                      bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p p'.2 ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                      (p'.2, bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                        decide (capacityPart p p'.2 ∈
                          occupiedCapsList p T_pub ++ hiddenCapsList p hid)))))) =
              ProbStep.tagged (X := A.X) (Y := A.Y) ⟨Sum.inr Bidirectional.Port.forward, u⟩ := by
            funext p'
            exact congrArg (ProbStep.tagged (X := A.X) (Y := A.Y)
              ⟨Sum.inr Bidirectional.Port.forward, u⟩) (congrFun hfn p')
          exact (congrArg (fun f => fTransform f _) hfn').symm
        | inverse =>
          dsimp only [realSpongeGameStep, realRFStep]
          rw [ProbDist.map_val, fTransform_fTransform]
          have hfn' : ((fun p => (p.1.1.1, p.2)) ∘
              ((ProbStep.tagged (X := A.X) (Y := A.Y) ⟨Sum.inr Bidirectional.Port.inverse, u⟩ ∘
                fun p => (p.1, p.2.1)) ∘
              (fun p' : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
                  ByteState p.stateBytes =>
                match lookupInverseEdge T_pub u with
                | some _ => (((p'.1, T_pub, hid), bad), (p'.2, bad))
                | none =>
                  (((p'.1, recordInverseEdge T_pub p'.2 u, hid),
                    bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p p'.2 ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)),
                    (p'.2, bad || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p p'.2 ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)))))) =
              ProbStep.tagged (X := A.X) (Y := A.Y) ⟨Sum.inr Bidirectional.Port.inverse, u⟩ := by
            funext p'
            dsimp only [Function.comp_def]
            cases lookupInverseEdge T_pub u <;> rfl
          exact (congrArg (fun f => fTransform f _) hfn').symm)
    ((ProbDist.single ([], [], [])).map fun s => (s, false)) (fun _ _ => trivial)
  rw [hsim]
  congr 1
  apply Subtype.ext
  simp only [ProbDist.bind_val, ProbDist.map_val, ProbDist.single, fTransform_single,
    bindK_single, one_smul, K]

/-! #### Invariant `RealGoodInv` and `realSpongeGame ≡g lazyPathGame` -/

/-- State reached along `bs` using `T_pub` first and falling back to `hid`. -/
def evalWithHidden (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (bs : List (ByteState p.rateBytes)) : ByteState p.stateBytes :=
  (evalAbsorption p T_pub (zeroState p.stateBytes) bs).getD
    ((hid.lookup bs).getD (zeroState p.stateBytes))

/-- Permutation input corresponding to a nonempty hidden prefix `bs`. -/
def hiddenInput (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (bs : List (ByteState p.rateBytes)) : ByteState p.stateBytes :=
  absorbBlock p (evalWithHidden p T_pub hid bs.dropLast) (bs.getLastD (zeroState p.rateBytes))

/-- Good-event invariant relating the full real table `T_full` to `(T_pub, hid)`. -/
structure RealGoodInv
    (T_full : List (ByteState p.stateBytes × ByteState p.stateBytes))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) : Prop where
  lazy : LazyGoodInv p T_pub hid
  fullPB : IsPartialBijection T_full
  pubInFull : ∀ e ∈ T_pub, (e.input, e.output) ∈ T_full
  hidInFull : ∀ entry ∈ hid, (hiddenInput p T_pub hid entry.1, entry.2) ∈ T_full
  fullOnly : ∀ xy ∈ T_full,
    (∃ e ∈ T_pub, xy = (e.input, e.output)) ∨
      (∃ entry ∈ hid, xy = (hiddenInput p T_pub hid entry.1, entry.2))

omit [Fintype M] [DecidableEq M] in
lemma realGoodInv_nil : RealGoodInv p [] [] [] where
  lazy := lazyGoodInv_nil p
  fullPB := isPartialBijection_nil
  pubInFull := by intro e he; cases he
  hidInFull := by intro entry he; cases he
  fullOnly := by intro xy hxy; cases hxy

omit [Fintype M] [DecidableEq M] in
lemma getLastD_append_singleton {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getLastD d = a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => exact ih

omit [Fintype M] [DecidableEq M] in
lemma lookupForward_eq_some_of_mem {X : Type} {T : List (X × X)}
    (hpb : IsPartialBijection T) {x y : X} (h : (x, y) ∈ T) :
    lookupForward T x = some y := by
  classical
  cases hl : lookupForward T x with
  | none =>
    exact False.elim ((lookupForward_eq_none_iff T x).mp hl (List.mem_map_of_mem (f := Prod.fst) h))
  | some y' =>
    have hmem' := mem_of_lookupForward_eq_some hl
    have heq : y' = y := by
      have hnd := hpb.1
      clear hl hpb
      induction T with
      | nil => cases h
      | cons hd tl ih =>
        rcases hd with ⟨a, b⟩
        rw [List.map_cons, List.nodup_cons] at hnd
        rcases List.mem_cons.mp h with h1 | h1 <;> rcases List.mem_cons.mp hmem' with h2 | h2
        · exact (Prod.mk.inj (h2.trans h1.symm)).2
        · have hx : a = x := (Prod.mk.inj h1).1.symm
          have hm : a ∈ tl.map Prod.fst := hx ▸ List.mem_map_of_mem (f := Prod.fst) h2
          exact False.elim (hnd.1 hm)
        · have hx : a = x := (Prod.mk.inj h2).1.symm
          have hm : a ∈ tl.map Prod.fst := hx ▸ List.mem_map_of_mem (f := Prod.fst) h1
          exact False.elim (hnd.1 hm)
        · exact ih h1 h2 hnd.2
    rw [heq]

omit [Fintype M] [DecidableEq M] in
lemma lookupInverse_eq_some_of_mem {X : Type} {T : List (X × X)}
    (hpb : IsPartialBijection T) {x y : X} (h : (x, y) ∈ T) :
    lookupInverse T y = some x := by
  classical
  cases hl : lookupInverse T y with
  | none =>
    exact False.elim ((lookupInverse_eq_none_iff T y).mp hl (List.mem_map_of_mem (f := Prod.snd) h))
  | some x' =>
    have hmem' := mem_of_lookupInverse_eq_some hl
    have heq : x' = x := by
      have hnd := hpb.2
      clear hl hpb
      induction T with
      | nil => cases h
      | cons hd tl ih =>
        rcases hd with ⟨a, b⟩
        rw [List.map_cons, List.nodup_cons] at hnd
        rcases List.mem_cons.mp h with h1 | h1 <;> rcases List.mem_cons.mp hmem' with h2 | h2
        · exact (Prod.mk.inj (h2.trans h1.symm)).1
        · have hy : b = y := (Prod.mk.inj h1).2.symm
          have hm : b ∈ tl.map Prod.snd := hy ▸ List.mem_map_of_mem (f := Prod.snd) h2
          exact False.elim (hnd.1 hm)
        · have hy : b = y := (Prod.mk.inj h2).2.symm
          have hm : b ∈ tl.map Prod.snd := hy ▸ List.mem_map_of_mem (f := Prod.snd) h1
          exact False.elim (hnd.1 hm)
        · exact ih h1 h2 hnd.2
    rw [heq]

omit [Fintype M] [DecidableEq M] in
lemma nonemptyPrefixes_cons {α : Type*} (b : α) (rest : List α) :
    nonemptyPrefixes (b :: rest) = [b] :: (nonemptyPrefixes rest).map (b :: ·) := by
  simp only [nonemptyPrefixes, List.length_cons, List.range_succ_eq_map, List.map_cons,
    List.map_map]
  rfl

/-- Suffix-parameterized new hidden prefixes starting from an already-reached prefix `pref`. -/
def newHiddenPrefixesFrom
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (keys : List (List (ByteState p.rateBytes)))
    (pref : List (ByteState p.rateBytes))
    (blocks : List (ByteState p.rateBytes)) : List (List (ByteState p.rateBytes)) :=
  ((nonemptyPrefixes blocks).map (pref ++ ·)).filter fun bs =>
    (evalAbsorption p T_pub (zeroState p.stateBytes) bs).isNone && !(keys.contains bs)

omit [Fintype M] [DecidableEq M] in
lemma newHiddenPrefixesFrom_nil_pref
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (keys : List (List (ByteState p.rateBytes))) (blocks : List (ByteState p.rateBytes)) :
    newHiddenPrefixesFrom p T_pub keys [] blocks = newHiddenPrefixes p T_pub keys blocks := by
  simp only [newHiddenPrefixesFrom, newHiddenPrefixes, List.nil_append, List.map_id']

omit [Fintype M] [DecidableEq M] in
lemma newHiddenPrefixesFrom_nil_blocks
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (keys : List (List (ByteState p.rateBytes))) (pref : List (ByteState p.rateBytes)) :
    newHiddenPrefixesFrom p T_pub keys pref [] = [] := rfl

omit [Fintype M] [DecidableEq M] in
lemma newHiddenPrefixesFrom_cons
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (keys : List (List (ByteState p.rateBytes))) (pref : List (ByteState p.rateBytes))
    (block : ByteState p.rateBytes) (rest : List (ByteState p.rateBytes)) :
    newHiddenPrefixesFrom p T_pub keys pref (block :: rest) =
      let bs := pref ++ [block]
      if ((evalAbsorption p T_pub (zeroState p.stateBytes) bs).isNone &&
          !(keys.contains bs)) = true then
        bs :: newHiddenPrefixesFrom p T_pub (keys ++ [bs]) bs rest
      else
        newHiddenPrefixesFrom p T_pub keys bs rest := by
  dsimp only
  unfold newHiddenPrefixesFrom
  rw [nonemptyPrefixes_cons, List.map_cons, List.map_map, List.filter_cons]
  have hmap : ((nonemptyPrefixes rest).map ((fun x => pref ++ x) ∘ fun x => block :: x)) =
      (nonemptyPrefixes rest).map ((pref ++ [block]) ++ ·) := by
    apply List.map_congr_left
    intro l _
    simp only [Function.comp_def, List.append_assoc, List.singleton_append]
  rw [hmap]
  split_ifs with hnew
  · congr 1
    apply List.filter_congr
    intro x hx
    rcases List.mem_map.mp hx with ⟨l, hl, rfl⟩
    have hne_nil : l ≠ [] := mem_nonemptyPrefixes_ne_nil hl
    have hne : (pref ++ [block]) ++ l ≠ pref ++ [block] := by
      intro hEq
      have hlen := congrArg List.length hEq
      rw [List.length_append] at hlen
      have hpos : 0 < l.length := List.length_pos_of_ne_nil hne_nil
      omega
    have hcont : (keys ++ [pref ++ [block]]).contains ((pref ++ [block]) ++ l) =
        keys.contains ((pref ++ [block]) ++ l) := by
      by_cases hmem : ((pref ++ [block]) ++ l) ∈ keys
      · rw [List.contains_iff_mem.mpr (List.mem_append_left _ hmem),
          List.contains_iff_mem.mpr hmem]
      · have hnot : ((pref ++ [block]) ++ l) ∉ keys ++ [pref ++ [block]] := by
          simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hmem, hne⟩
        rw [Bool.eq_false_iff.mpr (fun hc => hnot (List.contains_iff_mem.mp hc)),
          Bool.eq_false_iff.mpr (fun hc => hmem (List.contains_iff_mem.mp hc))]
    rw [hcont]
  · rfl

omit [Fintype M] [DecidableEq M] in
lemma realGoodInv_not_mem_snd_of_cap_not_mem
    {T_full : List (ByteState p.stateBytes × ByteState p.stateBytes)}
    {T_pub : List (PermutationEdge (ByteState p.stateBytes))}
    {hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)}
    (inv : RealGoodInv p T_full T_pub hid) {y : ByteState p.stateBytes}
    (hy : capacityPart p y ∉ occupiedCapsList p T_pub ++ hiddenCapsList p hid) :
    y ∉ T_full.map Prod.snd := by
  rw [List.mem_append, not_or] at hy
  intro hmem
  rcases List.mem_map.mp hmem with ⟨⟨x, y'⟩, hxy, rfl⟩
  rcases inv.fullOnly (x, y') hxy with ⟨e, he, hEq⟩ | ⟨entry, hentry, hEq⟩
  · have hy' : y' = e.output := (Prod.mk.inj hEq).2
    apply hy.1
    rw [mem_occupiedCapsList_iff]
    simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, hy']
    exact Or.inr (Or.inr (List.mem_map_of_mem he))
  · have hy' : y' = entry.2 := (Prod.mk.inj hEq).2
    apply hy.2
    rw [hy']
    exact List.mem_map_of_mem hentry

omit [Fintype M] [DecidableEq M] in
lemma realGoodInv_not_mem_fst_of_cap_not_mem
    {T_full : List (ByteState p.stateBytes × ByteState p.stateBytes)}
    {T_pub : List (PermutationEdge (ByteState p.stateBytes))}
    {hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)}
    (inv : RealGoodInv p T_full T_pub hid) {x : ByteState p.stateBytes}
    (hx : capacityPart p x ∉ occupiedCapsList p T_pub ++ hiddenCapsList p hid) :
    x ∉ T_full.map Prod.fst := by
  rw [List.mem_append, not_or] at hx
  intro hmem
  rcases List.mem_map.mp hmem with ⟨⟨x', y⟩, hxy, rfl⟩
  rcases inv.fullOnly (x', y) hxy with ⟨e, he, hEq⟩ | ⟨entry, hentry, hEq⟩
  · have hx' : x' = e.input := (Prod.mk.inj hEq).1
    apply hx.1
    rw [mem_occupiedCapsList_iff]
    simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union, List.mem_toFinset, hx']
    exact Or.inr (Or.inl (List.mem_map_of_mem he))
  · have hx' : x' = hiddenInput p T_pub hid entry.1 := (Prod.mk.inj hEq).1
    have hcap : capacityPart p x' =
      capacityPart p (evalWithHidden p T_pub hid entry.1.dropLast) := by
      rw [hx', hiddenInput, capacityPart_absorbBlock]
    rcases inv.lazy.prefixClosed entry hentry with hcov | hhid
    · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast with
      | none => rw [hev] at hcov; cases hcov
      | some s =>
        apply hx.1
        rw [hcap, evalWithHidden, hev, Option.getD_some, mem_occupiedCapsList_iff]
        exact capacityPart_mem_occupied_of_evalAbsorption p T_pub entry.1.dropLast hev
    · obtain ⟨z, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhid
      have hnone := inv.lazy.keysUncovered (entry.1.dropLast, z) hz_mem
      apply hx.2
      rw [hcap, evalWithHidden, hnone, Option.getD_none, hz_lu, Option.getD_some]
      exact List.mem_map_of_mem hz_mem

omit [Fintype M] [DecidableEq M] in
lemma realGoodInv_not_mem_fst_of_new_prefix (hp : p.Valid)
    {T_full : List (ByteState p.stateBytes × ByteState p.stateBytes)}
    {T_pub : List (PermutationEdge (ByteState p.stateBytes))}
    {hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)}
    (inv : RealGoodInv p T_full T_pub hid)
    {pref : List (ByteState p.rateBytes)} {block : ByteState p.rateBytes}
    (hreach : (evalAbsorption p T_pub (zeroState p.stateBytes) pref).isSome ∨
      pref ∈ hid.map Prod.fst)
    (hunc : evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block]) = none)
    (hnothid : pref ++ [block] ∉ hid.map Prod.fst) :
    absorbBlock p (evalWithHidden p T_pub hid pref) block ∉ T_full.map Prod.fst := by
  intro hmem
  rcases List.mem_map.mp hmem with ⟨⟨x, y⟩, hxy, hx_eq⟩
  dsimp only at hx_eq
  rcases inv.fullOnly (x, y) hxy with ⟨e, he, hEq⟩ | ⟨entry, hentry, hEq⟩
  · have hx_in : x = e.input := (Prod.mk.inj hEq).1
    rcases hreach with hcov | hhid
    · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) pref with
      | none => rw [hev] at hcov; cases hcov
      | some s =>
        have hx_abs : absorbBlock p s block = e.input := by
          rw [← hx_in, hx_eq, evalWithHidden, hev, Option.getD_some]
        rw [evalAbsorption_append, hev] at hunc
        simp only [Option.bind_some, evalAbsorption] at hunc
        cases hl : lookupForwardEdge T_pub (absorbBlock p s block) with
        | none =>
          exact (lookupForwardEdge_eq_none_iff T_pub _).mp hl e he hx_abs.symm
        | some out =>
          rw [hl] at hunc; cases hunc
    · obtain ⟨z, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhid
      have hnone := inv.lazy.keysUncovered (pref, z) hz_mem
      have hcap_hid : capacityPart p x ∈ hiddenCapsList p hid := by
        rw [hx_eq, capacityPart_absorbBlock, evalWithHidden, hnone, Option.getD_none, hz_lu,
          Option.getD_some]
        exact List.mem_map_of_mem hz_mem
      have hcap_occ : capacityPart p x ∈ occupiedCapsList p T_pub := by
        rw [hx_in, mem_occupiedCapsList_iff]
        simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union, List.mem_toFinset]
        exact Or.inr (Or.inl (List.mem_map_of_mem he))
      exact inv.lazy.capsDisjoint (capacityPart p x) hcap_hid hcap_occ
  · have hx_hid : absorbBlock p (evalWithHidden p T_pub hid pref) block =
        hiddenInput p T_pub hid entry.1 := hx_eq.symm.trans (Prod.mk.inj hEq).1
    have hcap_eq : capacityPart p (evalWithHidden p T_pub hid pref) =
        capacityPart p (evalWithHidden p T_pub hid entry.1.dropLast) := by
      have hc := congrArg (capacityPart p) hx_hid
      simpa only [hiddenInput, capacityPart_absorbBlock] using hc
    have hsplit_entry : entry.1.dropLast ++ [entry.1.getLastD (zeroState p.rateBytes)] =
      entry.1 := by
      have hne := inv.lazy.keysNonempty entry hentry
      cases h : entry.1.reverse with
      | nil => exact False.elim (hne (List.reverse_eq_nil_iff.mp h))
      | cons last rev =>
        have heq : entry.1 = rev.reverse ++ [last] := by
          have := congrArg List.reverse h
          simpa only [List.reverse_reverse, List.reverse_cons] using this
        rw [heq, List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _), List.dropLast_singleton,
          List.append_nil, getLastD_append_singleton]
    rcases hreach with hcov1 | hhid1 <;>
      rcases inv.lazy.prefixClosed entry hentry with hcov2 | hhid2
    · cases hev1 : evalAbsorption p T_pub (zeroState p.stateBytes) pref with
      | none => rw [hev1] at hcov1; cases hcov1
      | some s1 =>
        cases hev2 : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast with
        | none => rw [hev2] at hcov2; cases hcov2
        | some s2 =>
          rw [evalWithHidden, hev1, Option.getD_some, evalWithHidden, hev2,
            Option.getD_some] at hcap_eq
          have hs_eq : s1 = s2 :=
            reached_capacity_injective (capacityPart p) (zeroState p.capacityBytes)
              (zeroState p.stateBytes) (capacityPart_zeroState p) T_pub inv.lazy.capFree
              (evalAbsorption_reached p T_pub inv.lazy.capFree pref hev1)
              (evalAbsorption_reached p T_pub inv.lazy.capFree entry.1.dropLast hev2) hcap_eq
          have hpref_eq : pref = entry.1.dropLast :=
            blocks_eq_of_evalAbsorption_eq p hp T_pub inv.lazy.partialBij inv.lazy.capFree
              hev1 (hs_eq ▸ hev2)
          rw [evalWithHidden, hev1, Option.getD_some, hiddenInput, evalWithHidden, hev2,
            Option.getD_some, hs_eq] at hx_hid
          have hb_eq : block = entry.1.getLastD (zeroState p.rateBytes) :=
            absorbBlock_injective p hp.2.1.le s2 hx_hid
          apply hnothid
          rw [hpref_eq, hb_eq, hsplit_entry]
          exact List.mem_map_of_mem hentry
    · cases hev1 : evalAbsorption p T_pub (zeroState p.stateBytes) pref with
      | none => rw [hev1] at hcov1; cases hcov1
      | some s1 =>
        obtain ⟨z2, hz2_lu, hz2_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhid2
        have hnone2 := inv.lazy.keysUncovered (entry.1.dropLast, z2) hz2_mem
        rw [evalWithHidden, hev1, Option.getD_some, evalWithHidden, hnone2, Option.getD_none,
          hz2_lu, Option.getD_some] at hcap_eq
        have hocc1 : capacityPart p s1 ∈ occupiedCapsList p T_pub := by
          rw [mem_occupiedCapsList_iff]
          exact capacityPart_mem_occupied_of_evalAbsorption p T_pub pref hev1
        exact inv.lazy.capsDisjoint (capacityPart p z2) (List.mem_map_of_mem hz2_mem)
          (hcap_eq ▸ hocc1)
    · obtain ⟨z1, hz1_lu, hz1_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhid1
      have hnone1 := inv.lazy.keysUncovered (pref, z1) hz1_mem
      cases hev2 : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast with
      | none => rw [hev2] at hcov2; cases hcov2
      | some s2 =>
        rw [evalWithHidden, hnone1, Option.getD_none, hz1_lu, Option.getD_some,
          evalWithHidden, hev2, Option.getD_some] at hcap_eq
        have hocc2 : capacityPart p s2 ∈ occupiedCapsList p T_pub := by
          rw [mem_occupiedCapsList_iff]
          exact capacityPart_mem_occupied_of_evalAbsorption p T_pub entry.1.dropLast hev2
        exact inv.lazy.capsDisjoint (capacityPart p z1) (List.mem_map_of_mem hz1_mem)
          (hcap_eq.symm ▸ hocc2)
    · obtain ⟨z1, hz1_lu, hz1_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhid1
      obtain ⟨z2, hz2_lu, hz2_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhid2
      have hnone1 := inv.lazy.keysUncovered (pref, z1) hz1_mem
      have hnone2 := inv.lazy.keysUncovered (entry.1.dropLast, z2) hz2_mem
      rw [evalWithHidden, hnone1, Option.getD_none, hz1_lu, Option.getD_some,
        evalWithHidden, hnone2, Option.getD_none, hz2_lu, Option.getD_some] at hcap_eq
      have hpair_eq : (pref, z1) = (entry.1.dropLast, z2) := by
        have hcap_uniq : ∀ (l : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)),
            (hiddenCapsList p l).Nodup →
            ∀ {e₁ e₂ : List (ByteState p.rateBytes) × ByteState p.stateBytes},
              e₁ ∈ l → e₂ ∈ l → capacityPart p e₁.2 = capacityPart p e₂.2 → e₁ = e₂ := by
          intro l hnd e₁ e₂ h1 h2 hc
          induction l with
          | nil => cases h1
          | cons hd tl ih =>
            rw [hiddenCapsList, List.map_cons, List.nodup_cons] at hnd
            rcases List.mem_cons.mp h1 with rfl | h1' <;> rcases List.mem_cons.mp h2 with rfl | h2'
            · rfl
            · exact False.elim (hnd.1 (hc ▸ List.mem_map_of_mem h2'))
            · exact False.elim (hnd.1 (hc.symm ▸ List.mem_map_of_mem h1'))
            · exact ih hnd.2 h1' h2'
        exact hcap_uniq hid inv.lazy.capsNodup hz1_mem hz2_mem hcap_eq
      have hpref_eq : pref = entry.1.dropLast := (Prod.mk.inj hpair_eq).1
      have hz_eq : z1 = z2 := (Prod.mk.inj hpair_eq).2
      rw [evalWithHidden, hnone1, Option.getD_none, hz1_lu, Option.getD_some,
        hiddenInput, evalWithHidden, hnone2, Option.getD_none, hz2_lu, Option.getD_some,
        hz_eq] at hx_hid
      have hb_eq : block = entry.1.getLastD (zeroState p.rateBytes) :=
        absorbBlock_injective p hp.2.1.le z2 hx_hid
      apply hnothid
      rw [hpref_eq, hb_eq, hsplit_entry]
      exact List.mem_map_of_mem hentry

omit [Fintype M] [DecidableEq M] in
lemma realGoodInv_evalWithHidden_step
    {T_full : List (ByteState p.stateBytes × ByteState p.stateBytes)}
    {T_pub : List (PermutationEdge (ByteState p.stateBytes))}
    {hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)}
    (inv : RealGoodInv p T_full T_pub hid)
    {pref : List (ByteState p.rateBytes)} {block : ByteState p.rateBytes}
    (hnotnew : ¬ ((evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block])).isNone &&
      !((hid.map Prod.fst).contains (pref ++ [block]))) = true) :
    lookupForward T_full (absorbBlock p (evalWithHidden p T_pub hid pref) block) =
      some (evalWithHidden p T_pub hid (pref ++ [block])) ∧
      ((evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block])).isSome ∨
        pref ++ [block] ∈ hid.map Prod.fst) := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at hnotnew
  cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block]) with
  | some s_next =>
    have hev_copy := hev
    rw [evalAbsorption_append] at hev_copy
    cases hp_ev : evalAbsorption p T_pub (zeroState p.stateBytes) pref with
    | none => rw [hp_ev] at hev_copy; cases hev_copy
    | some s_pre =>
      rw [hp_ev, Option.bind_some, evalAbsorption] at hev_copy
      cases hlu : lookupForwardEdge T_pub (absorbBlock p s_pre block) with
      | none => rw [hlu] at hev_copy; cases hev_copy
      | some out =>
        rw [hlu] at hev_copy
        simp only [evalAbsorption, Option.some.injEq] at hev_copy
        subst hev_copy
        obtain ⟨e, he_mem, hi, ho⟩ := lookupForwardEdge_eq_some_mem hlu
        have hmem_full : (absorbBlock p s_pre block, out) ∈ T_full := by
          rw [← hi, ← ho]; exact inv.pubInFull e he_mem
        refine ⟨?_, Or.inl rfl⟩
        rw [evalWithHidden, hp_ev, Option.getD_some, evalWithHidden, hev, Option.getD_some]
        exact lookupForward_eq_some_of_mem inv.fullPB hmem_full
  | none =>
    have hcont : (hid.map Prod.fst).contains (pref ++ [block]) = true := by
      rw [hev] at hnotnew
      have h := hnotnew rfl
      exact Bool.eq_true_of_not_eq_false h
    have hmem_hid : pref ++ [block] ∈ hid.map Prod.fst := List.contains_iff_mem.mp hcont
    obtain ⟨z, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hmem_hid
    have hhid_in := inv.hidInFull (pref ++ [block], z) hz_mem
    have hdrop : (pref ++ [block]).dropLast = pref := by
      rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _), List.dropLast_singleton,
        List.append_nil]
    have hlast : (pref ++ [block]).getLastD (zeroState p.rateBytes) = block :=
      getLastD_append_singleton pref block (zeroState p.rateBytes)
    rw [hiddenInput, hdrop, hlast] at hhid_in
    refine ⟨?_, Or.inr hmem_hid⟩
    have hew : evalWithHidden p T_pub hid (pref ++ [block]) = z := by
      rw [evalWithHidden, hev, Option.getD_none, hz_lu, Option.getD_some]
    rw [hew]
    exact lookupForward_eq_some_of_mem inv.fullPB hhid_in

omit [Fintype M] [DecidableEq M] in
lemma realGoodInv_append_hidden (hp : p.Valid)
    {T_full : List (ByteState p.stateBytes × ByteState p.stateBytes)}
    {T_pub : List (PermutationEdge (ByteState p.stateBytes))}
    {hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)}
    (inv : RealGoodInv p T_full T_pub hid)
    {pref : List (ByteState p.rateBytes)} {block : ByteState p.rateBytes}
    {z : ByteState p.stateBytes}
    (hreach : (evalAbsorption p T_pub (zeroState p.stateBytes) pref).isSome ∨
      pref ∈ hid.map Prod.fst)
    (hunc : evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block]) = none)
    (hnothid : pref ++ [block] ∉ hid.map Prod.fst)
    (hz : capacityPart p z ∉ occupiedCapsList p T_pub ++ hiddenCapsList p hid) :
    RealGoodInv p
      (T_full ++ [(absorbBlock p (evalWithHidden p T_pub hid pref) block, z)])
      T_pub (hid ++ [(pref ++ [block], z)]) := by
  have hx_not : absorbBlock p (evalWithHidden p T_pub hid pref) block ∉ T_full.map Prod.fst :=
    realGoodInv_not_mem_fst_of_new_prefix p hp inv hreach hunc hnothid
  have hz_not : z ∉ T_full.map Prod.snd :=
    realGoodInv_not_mem_snd_of_cap_not_mem p inv hz
  rw [List.mem_append, not_or] at hz
  have heval_pres : ∀ bs : List (ByteState p.rateBytes),
      ((evalAbsorption p T_pub (zeroState p.stateBytes) bs).isSome ∨ bs ∈ hid.map Prod.fst) →
      evalWithHidden p T_pub (hid ++ [(pref ++ [block], z)]) bs =
        evalWithHidden p T_pub hid bs := by
    intro bs hbs
    unfold evalWithHidden
    cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) bs with
    | some s => rfl
    | none =>
      rcases hbs with hc | hh
      · rw [hev] at hc; cases hc
      · obtain ⟨v, hv_lu, _⟩ := lookup_eq_some_of_mem_map_fst hid hh
        have hne : bs ≠ pref ++ [block] := fun hEq => hnothid (hEq ▸ hh)
        rw [lookup_append_singleton_of_not_mem hid (pref ++ [block]) z hnothid bs,
          ite_eq_right hne]
  have hdrop : (pref ++ [block]).dropLast = pref := by
    rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _), List.dropLast_singleton,
      List.append_nil]
  have hlast : (pref ++ [block]).getLastD (zeroState p.rateBytes) = block :=
    getLastD_append_singleton pref block (zeroState p.rateBytes)
  have hlazy : LazyGoodInv p T_pub (hid ++ [(pref ++ [block], z)]) :=
    { partialBij := inv.lazy.partialBij
      capFree := inv.lazy.capFree
      keysNodup := by
        rw [List.map_append, List.map_singleton, List.nodup_append]
        refine ⟨inv.lazy.keysNodup, List.nodup_singleton _, ?_⟩
        rintro a ha b hb rfl
        have hba : a = pref ++ [block] := List.mem_singleton.mp hb
        exact hnothid (hba ▸ ha)
      keysNonempty := by
        intro entry he
        rcases List.mem_append.mp he with h1 | h2
        · exact inv.lazy.keysNonempty entry h1
        · rw [List.mem_singleton.mp h2]
          exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
      keysUncovered := by
        intro entry he
        rcases List.mem_append.mp he with h1 | h2
        · exact inv.lazy.keysUncovered entry h1
        · rw [List.mem_singleton.mp h2]; exact hunc
      prefixClosed := by
        intro entry he
        rcases List.mem_append.mp he with h1 | h2
        · rcases inv.lazy.prefixClosed entry h1 with hcov | hhid
          · exact Or.inl hcov
          · exact Or.inr (by simp only [List.map_append, List.mem_append]; exact Or.inl hhid)
        · rw [List.mem_singleton.mp h2]; dsimp only; rw [hdrop]
          rcases hreach with hcov | hhid
          · exact Or.inl hcov
          · exact Or.inr (by simp only [List.map_append, List.mem_append]; exact Or.inl hhid)
      capsNodup := by
        unfold hiddenCapsList
        rw [List.map_append, List.map_singleton, List.nodup_append]
        refine ⟨inv.lazy.capsNodup, List.nodup_singleton _, ?_⟩
        rintro a ha b hb rfl
        exact hz.2 ((List.mem_singleton.mp hb) ▸ ha)
      capsDisjoint := by
        intro c hc
        unfold hiddenCapsList at hc
        rw [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton] at hc
        rcases hc with h1 | rfl
        · exact inv.lazy.capsDisjoint c h1
        · exact hz.1 }
  refine ⟨hlazy, isPartialBijection_append inv.fullPB hx_not hz_not, ?_, ?_, ?_⟩
  · intro e he; exact List.mem_append_left _ (inv.pubInFull e he)
  · intro entry he
    rcases List.mem_append.mp he with h1 | h2
    · rw [hiddenInput, heval_pres entry.1.dropLast (inv.lazy.prefixClosed entry h1)]
      exact List.mem_append_left _ (inv.hidInFull entry h1)
    · rw [List.mem_singleton.mp h2]
      dsimp only
      rw [hiddenInput, hdrop, hlast, heval_pres pref hreach]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  · intro xy hxy
    rcases List.mem_append.mp hxy with h1 | h2
    · rcases inv.fullOnly xy h1 with ⟨e, he, hEq⟩ | ⟨entry, hentry, hEq⟩
      · exact Or.inl ⟨e, he, hEq⟩
      · refine Or.inr ⟨entry, List.mem_append_left _ hentry, ?_⟩
        rw [hiddenInput, heval_pres entry.1.dropLast (inv.lazy.prefixClosed entry hentry)]
        exact hEq
    · rw [List.mem_singleton.mp h2]
      refine Or.inr ⟨(pref ++ [block], z), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      dsimp only
      rw [hiddenInput, hdrop, hlast, heval_pres pref hreach]

omit [Fintype M] [DecidableEq M] in
lemma absorbRealGameBlocks_sim_sampleHidden (hp : p.Valid) (q : ℕ)
    (T_full : List (ByteState p.stateBytes × ByteState p.stateBytes))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (pref : List (ByteState p.rateBytes)) (blocks : List (ByteState p.rateBytes))
    (inv : RealGoodInv p T_full T_pub hid)
    (hreach : (evalAbsorption p T_pub (zeroState p.stateBytes) pref).isSome ∨
      pref ∈ hid.map Prod.fst) :
    (∀ r ∈ (absorbRealGameBlocks p q T_full T_pub hid false pref
        (evalWithHidden p T_pub hid pref) blocks).1.support,
      r.1.2 = false →
        r.1.1.2.1 = T_pub ∧ RealGoodInv p r.1.1.1 T_pub r.1.1.2.2 ∧
        r.2 = evalWithHidden p T_pub r.1.1.2.2 (pref ++ blocks)) ∧
    fTransform (fun r => (((r.1.1.2.1, r.1.1.2.2), r.1.2), (digestPart p r.2, r.1.2)))
        ((absorbRealGameBlocks p q T_full T_pub hid false pref
          (evalWithHidden p T_pub hid pref) blocks).1.restrict fun r => r.1.2 = false) =
      fTransform (fun p' => (((T_pub, p'.1), p'.2),
          (digestPart p (evalWithHidden p T_pub p'.1 (pref ++ blocks)), p'.2)))
        ((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub hid false
          (newHiddenPrefixesFrom p T_pub (hid.map Prod.fst) pref blocks)).1.restrict
            fun p' => p'.2 = false) := by
  induction blocks generalizing T_full hid pref with
  | nil =>
    rw [List.append_nil, newHiddenPrefixesFrom_nil_blocks]
    simp only [absorbRealGameBlocks, sampleHiddenPrefixesWithBad, ProbDist.single]
    constructor
    · intro r hr _
      rw [Finsupp.mem_support_iff] at hr
      have hEq : r = (((T_full, T_pub, hid), false), evalWithHidden p T_pub hid pref) := by
        by_contra hne; exact hr (Finsupp.single_eq_of_ne hne)
      subst hEq; exact ⟨rfl, inv, rfl⟩
    · have h1 : ∀ {α : Type} (a : α) (P : α → Prop), P a →
          Distribution.restrict (Finsupp.single a (1 : ℝ)) P = Finsupp.single a 1 := by
        intro α a P ha
        classical
        ext x
        rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.single_apply]
        by_cases hx : a = x
        · subst hx; simp only [ha, ↓reduceIte]
        · simp only [hx, ↓reduceIte, ite_self]
      rw [h1 (((T_full, T_pub, hid), false), evalWithHidden p T_pub hid pref)
            (fun r => r.1.2 = false) rfl,
          h1 (hid, false) (fun p' => p'.2 = false) rfl,
        fTransform_single, fTransform_single]
  | cons block rest ih =>
    have hassoc : pref ++ block :: rest = (pref ++ [block]) ++ rest := by
      simp only [List.append_assoc, List.singleton_append]
    rw [hassoc, newHiddenPrefixesFrom_cons]
    dsimp only [absorbRealGameBlocks]
    by_cases hnew : ((evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block])).isNone &&
        !((hid.map Prod.fst).contains (pref ++ [block]))) = true
    · have hunc : evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block]) = none := by
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hnew
        exact hnew.1
      have hnothid : pref ++ [block] ∉ hid.map Prod.fst := by
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnew
        intro hmem
        have hc := List.contains_iff_mem.mpr hmem
        rw [hnew.2] at hc; cases hc
      have hx_not : absorbBlock p (evalWithHidden p T_pub hid pref) block ∉ T_full.map Prod.fst :=
        realGoodInv_not_mem_fst_of_new_prefix p hp inv hreach hunc hnothid
      have hlu_none : lookupForward T_full (absorbBlock p (evalWithHidden p T_pub hid pref) block) =
          none := (lookupForward_eq_none_iff T_full _).mpr hx_not
      have hfst_ite : ∀ z : ByteState p.stateBytes,
          (if z ∉ T_full.map Prod.snd then
              (T_full ++ [(absorbBlock p (evalWithHidden p T_pub hid pref) block, z)], z)
            else (T_full, z)).1 =
          if z ∉ T_full.map Prod.snd then
            T_full ++ [(absorbBlock p (evalWithHidden p T_pub hid pref) block, z)]
          else T_full := fun z => by split_ifs <;> rfl
      have hsnd_ite : ∀ z : ByteState p.stateBytes,
          (if z ∉ T_full.map Prod.snd then
              (T_full ++ [(absorbBlock p (evalWithHidden p T_pub hid pref) block, z)], z)
            else (T_full, z)).2 = z := fun z => by split_ifs <;> rfl
      simp only [hnew, ↓reduceIte, lazyBidirectionalRFStep, hlu_none, probDist_bind_map,
        hfst_ite, hsnd_ite, sampleHiddenPrefixesWithBad, Bool.false_or]
      have hreach_bs : ∀ z : ByteState p.stateBytes,
          (evalAbsorption p T_pub (zeroState p.stateBytes) (pref ++ [block])).isSome ∨
            pref ++ [block] ∈ (hid ++ [(pref ++ [block], z)]).map Prod.fst := fun z =>
        Or.inr (by simp only [List.map_append, List.map_singleton, List.mem_append,
          List.mem_singleton]; exact Or.inr trivial)
      have heval_bs : ∀ z : ByteState p.stateBytes,
          evalWithHidden p T_pub (hid ++ [(pref ++ [block],
            z)]) (pref ++ [block]) = z := fun z => by
        rw [evalWithHidden, hunc, Option.getD_none,
          lookup_append_singleton_of_not_mem hid (pref ++ [block]) z hnothid (pref ++ [block]),
          ite_eq_left rfl, Option.getD_some]
      constructor
      · intro r hr hr_false
        rw [ProbDist.bind_val, Finsupp.mem_support_iff, bindK_apply, Finsupp.sum] at hr
        obtain ⟨z, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
        have hmem_z : r ∈ (absorbRealGameBlocks p q
            (if z ∉ T_full.map Prod.snd then
                T_full ++ [(absorbBlock p (evalWithHidden p T_pub hid pref) block, z)]
              else T_full)
            T_pub (hid ++ [(pref ++ [block], z)])
            (decide (capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid))
            (pref ++ [block]) z rest).1.support :=
          Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)
        by_cases hcap : capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid
        · rw [decide_eq_true hcap] at hmem_z
          have htr := absorbRealGameBlocks_monotone p q _ T_pub (hid ++ [(pref ++ [block], z)])
            true (pref ++ [block]) z rest r hmem_z rfl
          rw [hr_false] at htr; cases htr
        · rw [decide_eq_false hcap] at hmem_z
          have hz_not : z ∉ T_full.map Prod.snd :=
            realGoodInv_not_mem_snd_of_cap_not_mem p inv hcap
          rw [ite_eq_left hz_not] at hmem_z
          have inv1 := realGoodInv_append_hidden p hp inv hreach hunc hnothid hcap
          have hih1 := (ih (T_full ++ [(absorbBlock p (evalWithHidden p T_pub hid pref) block, z)])
            (hid ++ [(pref ++ [block], z)]) (pref ++ [block]) inv1 (hreach_bs z)).1
          rw [heval_bs z] at hih1
          exact hih1 r hmem_z hr_false
      · rw [ProbDist.bind_val, ProbDist.bind_val, Distribution.restrict_bindK,
          Distribution.restrict_bindK, fTransform_bindK, fTransform_bindK]
        apply bindK_congr
        intro z _
        by_cases hcap : capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid
        · rw [decide_eq_true hcap]
          have hL0 : ∀ T' : List (ByteState p.stateBytes × ByteState p.stateBytes),
              ((absorbRealGameBlocks p q T' T_pub (hid ++ [(pref ++ [block], z)]) true
                (pref ++ [block]) z rest).1.restrict fun r => r.1.2 = false) = 0 := by
            intro T'; ext r; rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.zero_apply]
            by_cases hmem : r ∈ (absorbRealGameBlocks p q T' T_pub (hid ++ [(pref ++ [block], z)])
                true (pref ++ [block]) z rest).1.support
            · have htr := absorbRealGameBlocks_monotone p q T' T_pub (hid ++ [(pref ++ [block], z)])
                true (pref ++ [block]) z rest r hmem rfl
              rw [ite_eq_right (by rw [htr]; decide)]
            · rw [Finsupp.notMem_support_iff.mp hmem, ite_self]
          have hR0 : ((sampleHiddenPrefixesWithBad p (fun _ => 𝒰[ByteState p.stateBytes]) T_pub
              (hid ++ [(pref ++ [block], z)]) true
              (newHiddenPrefixesFrom p T_pub (hid.map Prod.fst ++ [pref ++ [block]])
                (pref ++ [block]) rest)).1.restrict
                fun p' => p'.2 = false) = 0 := by
            ext p'; rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.zero_apply]
            by_cases hmem : p' ∈ (sampleHiddenPrefixesWithBad p
                (fun _ => 𝒰[ByteState p.stateBytes]) T_pub (hid ++ [(pref ++ [block], z)]) true
                (newHiddenPrefixesFrom p T_pub (hid.map Prod.fst ++ [pref ++ [block]])
                  (pref ++ [block]) rest)).1.support
            · have htr := sampleHiddenPrefixesWithBad_monotone p _ T_pub
                (hid ++ [(pref ++ [block], z)]) true _ p' hmem rfl
              rw [ite_eq_right (by rw [htr]; decide)]
            · rw [Finsupp.notMem_support_iff.mp hmem, ite_self]
          rw [hL0, hR0, fTransform_zero, fTransform_zero]
        · rw [decide_eq_false hcap]
          have hz_not : z ∉ T_full.map Prod.snd :=
            realGoodInv_not_mem_snd_of_cap_not_mem p inv hcap
          rw [ite_eq_left hz_not]
          have inv1 := realGoodInv_append_hidden p hp inv hreach hunc hnothid hcap
          have hih := (ih _ (hid ++ [(pref ++ [block], z)]) (pref ++ [block]) inv1
            (hreach_bs z)).2
          rw [heval_bs z] at hih
          simpa only [List.map_append, List.map_singleton] using hih
    · obtain ⟨hlu_some, hreach_bs⟩ := realGoodInv_evalWithHidden_step p inv hnew
      simp only [hnew, lazyBidirectionalRFStep, hlu_some, probDist_single_bind]
      exact ih T_full hid (pref ++ [block]) inv hreach_bs

omit [DecidableEq M] in
open Classical in
/-- `realSpongeGame` is game-equivalent to `lazyPathGame`. -/
theorem realSpongeGame_gameEquivalent_lazyPathGame (hp : p.Valid)
    {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    (realSpongeGame p M spec q_pub).1.1.GameEquivalent
      (lazyPathGame p M spec q_pub).1.1 := by
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  let K : (List (ByteState p.stateBytes × ByteState p.stateBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) →
      ProbDist (List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) :=
    fun s => ProbDist.single s.2
  refine unsetMBOs_eq_of_good_simulation (A := A)
    (realSpongeGameStep p M spec q_pub) (lazyPathGameStep p M spec q_pub)
    (ProbDist.single ([], [], [])) (ProbDist.single ([], []))
    (realSpongeGameStep_flag p M spec q_pub) (lazyPathGameStep_flag p M spec q_pub)
    (fun s => RealGoodInv p s.1 s.2.1 s.2.2) K ?_ ?_ ?_ ?_
  · intro s hs
    rw [ProbDist.single, Finsupp.mem_support_iff] at hs
    have hEq : s = ([], [], []) := by
      by_contra hne; exact hs (Finsupp.single_eq_of_ne hne)
    subst hEq; exact realGoodInv_nil p
  · apply Subtype.ext
    rw [ProbDist.bind_val, ProbDist.single, bindK_single, one_smul]
  · -- Good invariant preservation
    rintro ⟨T_full, T_pub, hid⟩ o u ⟨T_full', T_pub', hid'⟩ y inv hmem
    rcases o with o | o
    · cases o
      dsimp only [realSpongeGameStep] at hmem
      obtain ⟨r, hr, hEq⟩ := mem_support_fTransform _ _ hmem
      have hr1 : r.1 = ((T_full', T_pub', hid'), false) := (Prod.mk.inj hEq).1
      have hrb : r.1.2 = false := congrArg Prod.snd hr1
      have hsim := (absorbRealGameBlocks_sim_sampleHidden p hp (w + q_pub) T_full T_pub hid []
        (paddedBlocks p (encode u)) inv (Or.inl rfl)).1 r hr hrb
      have hTp : r.1.1.2.1 = T_pub' := by
        have := congrArg (fun p => p.1.2.1) hr1; exact this
      have hTf : r.1.1.1 = T_full' := congrArg (fun p => p.1.1) hr1
      have hHd : r.1.1.2.2 = hid' := congrArg (fun p => p.1.2.2) hr1
      rw [← hTf, ← hTp, hsim.1, ← hHd]
      exact hsim.2.1
    · cases o with
      | forward =>
        dsimp only [realSpongeGameStep] at hmem
        obtain ⟨p', hp', hEq⟩ := mem_support_fTransform _ _ hmem
        cases hlu : lookupForwardEdge T_pub u with
        | some y0 =>
          rw [hlu] at hEq
          have hmem_full : (u, y0) ∈ T_full := by
            obtain ⟨e, he, hi, ho⟩ := lookupForwardEdge_eq_some_mem hlu
            rw [← hi, ← ho]; exact inv.pubInFull e he
          have hlu_full := lookupForward_eq_some_of_mem inv.fullPB hmem_full
          simp only [lazyBidirectionalRFStep, hlu_full, ProbDist.single,
            Finsupp.mem_support_iff] at hp'
          have hp'_eq : p' = (T_full, y0) := by
            by_contra hne; exact hp' (Finsupp.single_eq_of_ne hne)
          subst hp'_eq
          have hst : ((T_full, T_pub, hid), false) = ((T_full', T_pub', hid'), false) :=
            (Prod.mk.inj hEq).1
          have h1 := (Prod.mk.inj hst).1
          rcases Prod.mk.inj h1 with ⟨rfl, h2⟩
          rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
          exact inv
        | none =>
          rw [hlu] at hEq
          cases hrp : rootedPrefix p M encode T_pub u with
          | some bs =>
            rw [hrp] at hEq
            by_cases hhid_mem : bs ∈ hid.map Prod.fst
            · simp only [hhid_mem, ↓reduceIte] at hEq
              obtain ⟨z, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhid_mem
              obtain ⟨pref, parent, last, hbs_eq, hpar, habs⟩ :=
                rootedPrefix_spec p M encode T_pub hrp
              have hdrop : bs.dropLast = pref := by
                rw [hbs_eq, List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),
                  List.dropLast_singleton, List.append_nil]
              have hlast : bs.getLastD (zeroState p.rateBytes) = last := by
                rw [hbs_eq, getLastD_append_singleton]
              have hhin : hiddenInput p T_pub hid bs = u := by
                rw [hiddenInput, hdrop, hlast, evalWithHidden, hpar, Option.getD_some, habs]
              have hmem_full : (u, z) ∈ T_full := hhin ▸ inv.hidInFull (bs, z) hz_mem
              have hlu_full := lookupForward_eq_some_of_mem inv.fullPB hmem_full
              simp only [lazyBidirectionalRFStep, hlu_full, ProbDist.single,
                Finsupp.mem_support_iff] at hp'
              have hp'_eq : p' = (T_full, z) := by
                by_contra hne; exact hp' (Finsupp.single_eq_of_ne hne)
              subst hp'_eq
              have hst := (Prod.mk.inj ((Prod.mk.inj hEq).1)).1
              rcases Prod.mk.inj hst with ⟨rfl, h2⟩
              rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
              have hz_cap : capacityPart p z ∉ occupiedCapsList p T_pub :=
                inv.lazy.capsDisjoint (capacityPart p z) (List.mem_map_of_mem hz_mem)
              have hz_occ : capacityPart p z ∉
                  occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
                rwa [← mem_occupiedCapsList_iff]
              have hEval := evalAbsorption_recordForwardEdge_of_rootedPrefix p M hp encode T_pub
                inv.lazy.partialBij inv.lazy.capFree hlu hz_cap hrp
              have heval_pres : ∀ bs' : List (ByteState p.rateBytes),
                  ((evalAbsorption p T_pub (zeroState p.stateBytes) bs').isSome ∨
                    bs' ∈ hid.map Prod.fst) →
                  evalWithHidden p (recordForwardEdge T_pub u z) (eraseHiddenKey p hid bs) bs' =
                    evalWithHidden p T_pub hid bs' := by
                intro bs' hbs'
                unfold evalWithHidden
                by_cases hsame : bs' = bs
                · rw [hsame, hEval.1, inv.lazy.keysUncovered (bs, z) hz_mem, hz_lu]; rfl
                · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) bs' with
                  | some s =>
                    rw [recordForwardEdge_eq_append_of_avoids p T_pub hz_occ,
                      evalAbsorption_mono p hev]; rfl
                  | none =>
                    have hne_nil : bs' ≠ [] := by intro hnil; subst hnil; cases hev
                    rw [hEval.2 bs' hne_nil hsame hev, lookup_eraseHiddenKey_of_ne p hid hsame]
              have hlazy' : LazyGoodInv p (recordForwardEdge T_pub u z)
                  (eraseHiddenKey p hid bs) := by
                have hrec := recordForwardEdge_eq_append_of_avoids p T_pub (x := u) hz_occ
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · rw [hrec]
                  have hne_out : z ∉ (toPairs T_pub).map Prod.snd := by
                    intro hm; rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hbz⟩
                    rcases List.mem_map.mp hab with ⟨e, he, hEq'⟩
                    have hbe : z = e.output := hbz.symm.trans (Prod.mk.inj hEq').2.symm
                    apply hz_occ; rw [hbe]
                    simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                      List.mem_toFinset]
                    exact Or.inr (Or.inr (List.mem_map_of_mem he))
                  have hne_in : u ∉ (toPairs T_pub).map Prod.fst := by
                    intro hm; rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hau⟩
                    rcases List.mem_map.mp hab with ⟨e, he, hEq'⟩
                    exact (lookupForwardEdge_eq_none_iff T_pub u).mp hlu e he
                      ((Prod.mk.inj hEq').1.trans hau)
                  simpa only [toPairs, List.map_append, List.map_singleton] using
                    isPartialBijection_append inv.lazy.partialBij hne_in hne_out
                · rw [hrec]
                  exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                    T_pub inv.lazy.capFree ⟨u, z, false⟩ hz_occ
                · rw [eraseHiddenKey]
                  exact inv.lazy.keysNodup.sublist (List.filter_sublist.map Prod.fst)
                · intro entry he
                  exact inv.lazy.keysNonempty entry (List.mem_of_mem_filter he)
                · intro entry he
                  have h1 := List.mem_filter.mp he
                  have hne_bs : entry.1 ≠ bs := decide_eq_true_eq.mp h1.2
                  exact hEval.2 entry.1 (inv.lazy.keysNonempty entry h1.1) hne_bs
                    (inv.lazy.keysUncovered entry h1.1)
                · intro entry he
                  have h1 := List.mem_filter.mp he
                  rcases inv.lazy.prefixClosed entry h1.1 with hcov | hhh
                  · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast
                      with
                    | none => rw [hev] at hcov; cases hcov
                    | some s =>
                      rw [hrec, evalAbsorption_mono p hev]; exact Or.inl rfl
                  · by_cases hdb : entry.1.dropLast = bs
                    · rw [hdb, hEval.1]; exact Or.inl rfl
                    · refine Or.inr ?_
                      unfold eraseHiddenKey
                      rcases List.mem_map.mp hhh with ⟨e', he', heq'⟩
                      exact List.mem_map.mpr ⟨e', List.mem_filter.mpr
                        ⟨he', decide_eq_true (heq'.symm ▸ hdb)⟩, heq'⟩
                · intro c hc hocc'
                  unfold hiddenCapsList eraseHiddenKey at hc
                  rcases List.mem_map.mp hc with ⟨entry, he, rfl⟩
                  have h1 := List.mem_filter.mp he
                  have hne_bs : entry.1 ≠ bs := decide_eq_true_eq.mp h1.2
                  rw [mem_occupiedCapsList_iff, hrec] at hocc'
                  simp only [occupiedCapacities, List.map_append, List.map_singleton,
                    List.toFinset_append, Finset.mem_insert, Finset.mem_union, List.mem_toFinset,
                    List.mem_singleton] at hocc'
                  have hocc_old : capacityPart p entry.2 ∈ occupiedCapsList p T_pub ∨
                      capacityPart p entry.2 = capacityPart p u ∨
                      capacityPart p entry.2 = capacityPart p z := by
                    rcases hocc' with h0 | h1' | h2'
                    · exact Or.inl (by
                        rw [mem_occupiedCapsList_iff]
                        simp only [occupiedCapacities, Finset.mem_insert, h0, true_or])
                    · rcases h1' with h1a | h1b
                      · exact Or.inl (by
                          rw [mem_occupiedCapsList_iff]
                          simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                            List.mem_toFinset, h1a, true_or, or_true])
                      · exact Or.inr (Or.inl h1b)
                    · rcases h2' with h2a | h2b
                      · exact Or.inl (by
                          rw [mem_occupiedCapsList_iff]
                          simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                            List.mem_toFinset, h2a, or_true])
                      · exact Or.inr (Or.inr h2b)
                  rcases hocc_old with hold | hu_eq | hz_eq
                  · exact inv.lazy.capsDisjoint _ (List.mem_map_of_mem h1.1) hold
                  · have hu_occ :=
                      rootedPrefix_cap_mem_occupied p M encode T_pub inv.lazy.capFree hrp
                    exact inv.lazy.capsDisjoint _ (List.mem_map_of_mem h1.1) (hu_eq ▸ hu_occ)
                  · have hpair : entry = (bs, z) := by
                      have hcap_uniq : ∀ (l : List (List (ByteState p.rateBytes) ×
                            ByteState p.stateBytes)),
                          (hiddenCapsList p l).Nodup →
                          ∀ {e₁ e₂ : List (ByteState p.rateBytes) × ByteState p.stateBytes},
                            e₁ ∈ l → e₂ ∈ l → capacityPart p e₁.2 = capacityPart p e₂.2 →
                              e₁ = e₂ := by
                        intro l hnd e₁ e₂ hm1 hm2 hce
                        induction l with
                        | nil => cases hm1
                        | cons hd tl ih =>
                          rw [hiddenCapsList, List.map_cons, List.nodup_cons] at hnd
                          rcases List.mem_cons.mp hm1 with rfl | ha <;>
                            rcases List.mem_cons.mp hm2 with rfl | hb
                          · rfl
                          · exact False.elim (hnd.1 (hce ▸ List.mem_map_of_mem hb))
                          · exact False.elim (hnd.1 (hce.symm ▸ List.mem_map_of_mem ha))
                          · exact ih hnd.2 ha hb
                      exact hcap_uniq hid inv.lazy.capsNodup h1.1 hz_mem hz_eq
                    exact hne_bs (congrArg Prod.fst hpair)
                · unfold hiddenCapsList eraseHiddenKey
                  exact inv.lazy.capsNodup.sublist
                    (List.filter_sublist.map
                      (fun e : List (ByteState p.rateBytes) × ByteState p.stateBytes =>
                        capacityPart p e.2))
              refine ⟨hlazy', inv.fullPB, ?_, ?_, ?_⟩
              · intro e he
                rw [recordForwardEdge_eq_append_of_avoids p T_pub hz_occ, List.mem_append,
                  List.mem_singleton] at he
                rcases he with h1 | rfl
                · exact inv.pubInFull e h1
                · exact hmem_full
              · intro entry he
                have h1 := List.mem_filter.mp he
                rw [hiddenInput, heval_pres entry.1.dropLast (inv.lazy.prefixClosed entry h1.1)]
                exact inv.hidInFull entry h1.1
              · intro xy hxy
                rcases inv.fullOnly xy hxy with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
                · refine Or.inl ⟨e, ?_, hEq'⟩
                  rw [recordForwardEdge_eq_append_of_avoids p T_pub hz_occ]
                  exact List.mem_append_left _ he
                · by_cases hsame : entry.1 = bs
                  · have hz' : entry.2 = z := by
                      have heq_snd : ∀ {α β : Type} {l : List (α × β)}, (l.map Prod.fst).Nodup →
                          ∀ {a : α} {b₁ b₂ : β}, (a, b₁) ∈ l → (a, b₂) ∈ l → b₁ = b₂ := by
                        intro α β l hnd a b₁ b₂ h1 h2
                        induction l with
                        | nil => cases h1
                        | cons hd tl ih =>
                          rw [List.map_cons, List.nodup_cons] at hnd
                          rcases List.mem_cons.mp h1 with h1' | h1' <;>
                            rcases List.mem_cons.mp h2 with h2' | h2'
                          · exact (Prod.mk.inj (h1'.trans h2'.symm)).2
                          · have hm : hd.1 ∈ tl.map Prod.fst :=
                              (Prod.mk.inj h1').1.symm ▸ List.mem_map_of_mem (f := Prod.fst) h2'
                            exact False.elim (hnd.1 hm)
                          · have hm : hd.1 ∈ tl.map Prod.fst :=
                              (Prod.mk.inj h2').1.symm ▸ List.mem_map_of_mem (f := Prod.fst) h1'
                            exact False.elim (hnd.1 hm)
                          · exact ih hnd.2 h1' h2'
                      exact heq_snd inv.lazy.keysNodup (by rwa [← hsame]) hz_mem
                    refine Or.inl ⟨⟨u, z, false⟩, ?_, ?_⟩
                    · rw [recordForwardEdge_eq_append_of_avoids p T_pub hz_occ]
                      exact List.mem_append_right _ (List.mem_singleton_self _)
                    · rw [hEq', hsame, hz', hhin]
                  · refine Or.inr ⟨entry, List.mem_filter.mpr
                      ⟨hentry, by simp only [ne_eq, decide_eq_true_eq]; exact hsame⟩, ?_⟩
                    rw [hiddenInput,
                      heval_pres entry.1.dropLast (inv.lazy.prefixClosed entry hentry)]
                    exact hEq'
            · simp only [hhid_mem, ↓reduceIte] at hEq
              have hbad_f : (false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                  decide (capacityPart p p'.2 ∈
                    occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false :=
                congrArg Prod.snd (Prod.mk.inj hEq).1
              simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
                List.mem_append, not_or] at hbad_f
              have hu_not_fst : u ∉ T_full.map Prod.fst := by
                intro hm
                rcases List.mem_map.mp hm with ⟨⟨x', y'⟩, hxy', rfl⟩
                rcases inv.fullOnly (x', y') hxy' with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
                · exact (lookupForwardEdge_eq_none_iff T_pub x').mp hlu e he (Prod.mk.inj
                    hEq').1.symm
                · have hx' : x' = hiddenInput p T_pub hid entry.1 := (Prod.mk.inj hEq').1
                  rcases inv.lazy.prefixClosed entry hentry with hcov | hhh
                  · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast
                      with
                    | none => rw [hev] at hcov; cases hcov
                    | some s_pre =>
                      have habs : absorbBlock p s_pre (entry.1.getLastD (zeroState p.rateBytes)) =
                        x' := by
                        rw [hx', hiddenInput, evalWithHidden, hev, Option.getD_some]
                      have hrp' := rootedPrefix_eq_some_of_path p M hp encode T_pub
                        inv.lazy.partialBij inv.lazy.capFree hev habs
                      rw [hrp] at hrp'
                      have hsplit : entry.1.dropLast ++ [entry.1.getLastD (zeroState p.rateBytes)] =
                          entry.1 := by
                        have hne := inv.lazy.keysNonempty entry hentry
                        cases hrev : entry.1.reverse with
                        | nil => exact False.elim (hne (List.reverse_eq_nil_iff.mp hrev))
                        | cons last rev =>
                          have heq : entry.1 = rev.reverse ++ [last] := by
                            have := congrArg List.reverse hrev
                            simpa only [List.reverse_reverse, List.reverse_cons] using this
                          rw [heq, List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),
                            List.dropLast_singleton, List.append_nil, getLastD_append_singleton]
                      rw [hsplit] at hrp'
                      exact hhid_mem ((Option.some.inj hrp') ▸ List.mem_map_of_mem hentry)
                  · obtain ⟨z_pre, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhh
                    have hnone := inv.lazy.keysUncovered (entry.1.dropLast, z_pre) hz_mem
                    apply hbad_f.1
                    rw [hx', hiddenInput, capacityPart_absorbBlock, evalWithHidden, hnone,
                      Option.getD_none, hz_lu, Option.getD_some]
                    exact List.mem_map_of_mem hz_mem
              have hlu_full : lookupForward T_full u = none :=
                (lookupForward_eq_none_iff T_full u).mpr hu_not_fst
              simp only [lazyBidirectionalRFStep, hlu_full] at hp'
              obtain ⟨y0, _, hp'_eq⟩ := mem_support_fTransform _ _ hp'
              have hy0_eq : p'.2 = y0 := by
                rw [← hp'_eq]; split_ifs <;> rfl
              rw [hy0_eq] at hbad_f
              have hy0_not_snd : y0 ∉ T_full.map Prod.snd :=
                realGoodInv_not_mem_snd_of_cap_not_mem p inv (by
                  rw [List.mem_append]; exact fun h => h.elim hbad_f.2.1 hbad_f.2.2)
              rw [ite_eq_left hy0_not_snd] at hp'_eq
              subst hp'_eq
              have hst := (Prod.mk.inj ((Prod.mk.inj hEq).1)).1
              rcases Prod.mk.inj hst with ⟨rfl, h2⟩
              rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
              have hy_occ : capacityPart p y0 ∉
                  occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
                rw [← mem_occupiedCapsList_iff]; exact hbad_f.2.1
              have hrec := recordForwardEdge_eq_append_of_avoids p T_pub (x := u) hy_occ
              have hEval := evalAbsorption_recordForwardEdge_of_rootedPrefix p M hp encode T_pub
                inv.lazy.partialBij inv.lazy.capFree hlu hbad_f.2.1 hrp
              have heval_pres : ∀ bs' : List (ByteState p.rateBytes),
                  ((evalAbsorption p T_pub (zeroState p.stateBytes) bs').isSome ∨
                    bs' ∈ hid.map Prod.fst) →
                  evalWithHidden p (recordForwardEdge T_pub u y0) hid bs' =
                    evalWithHidden p T_pub hid bs' := by
                intro bs' hbs'
                unfold evalWithHidden
                cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) bs' with
                | some s => rw [hrec, evalAbsorption_mono p hev]
                | none =>
                  rcases hbs' with hc | hh
                  · rw [hev] at hc; cases hc
                  · have hne_bs : bs' ≠ bs := fun hEq' => hhid_mem (hEq' ▸ hh)
                    have hne_nil : bs' ≠ [] := by intro hnil; subst hnil; cases hev
                    rw [hEval.2 bs' hne_nil hne_bs hev]
              have hlazy' : LazyGoodInv p (recordForwardEdge T_pub u y0) hid := by
                refine ⟨?_, ?_, inv.lazy.keysNodup, inv.lazy.keysNonempty, ?_, ?_,
                  ?_, inv.lazy.capsNodup⟩
                · rw [hrec]
                  have hne_out : y0 ∉ (toPairs T_pub).map Prod.snd := by
                    intro hm; rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hby⟩
                    rcases List.mem_map.mp hab with ⟨e, he, hEq'⟩
                    apply hy_occ; rw [hby.symm.trans (Prod.mk.inj hEq').2.symm]
                    simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                      List.mem_toFinset]
                    exact Or.inr (Or.inr (List.mem_map_of_mem he))
                  have hne_in : u ∉ (toPairs T_pub).map Prod.fst := by
                    intro hm; rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hau⟩
                    rcases List.mem_map.mp hab with ⟨e, he, hEq'⟩
                    exact (lookupForwardEdge_eq_none_iff T_pub u).mp hlu e he
                      ((Prod.mk.inj hEq').1.trans hau)
                  simpa only [toPairs, List.map_append, List.map_singleton] using
                    isPartialBijection_append inv.lazy.partialBij hne_in hne_out
                · rw [hrec]
                  exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                    T_pub inv.lazy.capFree ⟨u, y0, false⟩ hy_occ
                · intro entry he
                  have hne_bs : entry.1 ≠ bs := fun hEq' =>
                    hhid_mem (hEq' ▸ List.mem_map_of_mem he)
                  exact hEval.2 entry.1 (inv.lazy.keysNonempty entry he) hne_bs
                    (inv.lazy.keysUncovered entry he)
                · intro entry he
                  rcases inv.lazy.prefixClosed entry he with hcov | hhh
                  · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast
                      with
                    | none => rw [hev] at hcov; cases hcov
                    | some s => rw [hrec, evalAbsorption_mono p hev]; exact Or.inl rfl
                  · exact Or.inr hhh
                · intro c hc hocc'
                  rw [mem_occupiedCapsList_iff, hrec] at hocc'
                  simp only [occupiedCapacities, List.map_append, List.map_singleton,
                    List.toFinset_append, Finset.mem_insert, Finset.mem_union, List.mem_toFinset,
                    List.mem_singleton] at hocc'
                  rcases hocc' with h0 | h1' | h2'
                  · exact inv.lazy.capsDisjoint c hc (by
                      rw [mem_occupiedCapsList_iff]
                      simp only [occupiedCapacities, Finset.mem_insert, h0, true_or])
                  · rcases h1' with h1a | h1b
                    · exact inv.lazy.capsDisjoint c hc (by
                        rw [mem_occupiedCapsList_iff]
                        simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                          List.mem_toFinset, h1a, true_or, or_true])
                    · exact hbad_f.1 (h1b ▸ hc)
                  · rcases h2' with h2a | h2b
                    · exact inv.lazy.capsDisjoint c hc (by
                        rw [mem_occupiedCapsList_iff]
                        simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                          List.mem_toFinset, h2a, or_true])
                    · exact hbad_f.2.2 (h2b ▸ hc)
              refine ⟨hlazy', isPartialBijection_append inv.fullPB hu_not_fst hy0_not_snd, ?_, ?_,
                ?_⟩
              · intro e he
                rw [hrec, List.mem_append, List.mem_singleton] at he
                rcases he with h1 | rfl
                · exact List.mem_append_left _ (inv.pubInFull e h1)
                · exact List.mem_append_right _ (List.mem_singleton_self _)
              · intro entry he
                rw [hiddenInput, heval_pres entry.1.dropLast (inv.lazy.prefixClosed entry he)]
                exact List.mem_append_left _ (inv.hidInFull entry he)
              · intro xy hxy
                rw [List.mem_append, List.mem_singleton] at hxy
                rcases hxy with h1 | rfl
                · rcases inv.fullOnly xy h1 with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
                  · exact Or.inl ⟨e, by rw [hrec]; exact List.mem_append_left _ he, hEq'⟩
                  · refine Or.inr ⟨entry, hentry, ?_⟩
                    rw [hiddenInput,
                      heval_pres entry.1.dropLast (inv.lazy.prefixClosed entry hentry)]
                    exact hEq'
                · exact Or.inl ⟨⟨u, y0, false⟩,
                    by rw [hrec]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
          | none =>
            rw [hrp] at hEq
            have hbad_f : (false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                decide (capacityPart p p'.2 ∈
                  occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false :=
              congrArg Prod.snd (Prod.mk.inj hEq).1
            simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
              List.mem_append, not_or] at hbad_f
            have hu_not_fst : u ∉ T_full.map Prod.fst := by
              intro hm
              rcases List.mem_map.mp hm with ⟨⟨x', y'⟩, hxy', rfl⟩
              rcases inv.fullOnly (x', y') hxy' with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
              · exact (lookupForwardEdge_eq_none_iff T_pub x').mp hlu e he (Prod.mk.inj hEq').1.symm
              · have hx' : x' = hiddenInput p T_pub hid entry.1 := (Prod.mk.inj hEq').1
                rcases inv.lazy.prefixClosed entry hentry with hcov | hhh
                · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast with
                  | none => rw [hev] at hcov; cases hcov
                  | some s_pre =>
                    have habs : absorbBlock p s_pre (entry.1.getLastD (zeroState p.rateBytes)) =
                      x' := by
                      rw [hx', hiddenInput, evalWithHidden, hev, Option.getD_some]
                    have hrp' := rootedPrefix_eq_some_of_path p M hp encode T_pub
                      inv.lazy.partialBij inv.lazy.capFree hev habs
                    rw [hrp] at hrp'; cases hrp'
                · obtain ⟨z_pre, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhh
                  have hnone := inv.lazy.keysUncovered (entry.1.dropLast, z_pre) hz_mem
                  apply hbad_f.1
                  rw [hx', hiddenInput, capacityPart_absorbBlock, evalWithHidden, hnone,
                    Option.getD_none, hz_lu, Option.getD_some]
                  exact List.mem_map_of_mem hz_mem
            have hlu_full : lookupForward T_full u = none :=
              (lookupForward_eq_none_iff T_full u).mpr hu_not_fst
            simp only [lazyBidirectionalRFStep, hlu_full] at hp'
            obtain ⟨y0, _, hp'_eq⟩ := mem_support_fTransform _ _ hp'
            have hy0_eq : p'.2 = y0 := by
              rw [← hp'_eq]; split_ifs <;> rfl
            rw [hy0_eq] at hbad_f
            have hy0_not_snd : y0 ∉ T_full.map Prod.snd :=
              realGoodInv_not_mem_snd_of_cap_not_mem p inv (by
                rw [List.mem_append]; exact fun h => h.elim hbad_f.2.1 hbad_f.2.2)
            rw [ite_eq_left hy0_not_snd] at hp'_eq
            subst hp'_eq
            have hst := (Prod.mk.inj ((Prod.mk.inj hEq).1)).1
            rcases Prod.mk.inj hst with ⟨rfl, h2⟩
            rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
            have hy_occ : capacityPart p y0 ∉
                occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
              rw [← mem_occupiedCapsList_iff]; exact hbad_f.2.1
            have hrec := recordForwardEdge_eq_append_of_avoids p T_pub (x := u) hy_occ
            have hEval := evalAbsorption_recordForwardEdge_of_rootedPrefix_none p M hp encode T_pub
              inv.lazy.partialBij inv.lazy.capFree hbad_f.2.1 hrp
            have heval_pres : ∀ bs' : List (ByteState p.rateBytes),
                evalWithHidden p (recordForwardEdge T_pub u y0) hid bs' =
                  evalWithHidden p T_pub hid bs' := by
              intro bs'
              unfold evalWithHidden
              cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) bs' with
              | some s => rw [hrec, evalAbsorption_mono p hev]
              | none =>
                have hne_nil : bs' ≠ [] := by intro hnil; subst hnil; cases hev
                rw [hEval bs' hne_nil hev]
            have hlazy' : LazyGoodInv p (recordForwardEdge T_pub u y0) hid := by
              refine ⟨?_, ?_, inv.lazy.keysNodup, inv.lazy.keysNonempty, ?_, ?_,
                ?_, inv.lazy.capsNodup⟩
              · rw [hrec]
                have hne_out : y0 ∉ (toPairs T_pub).map Prod.snd := by
                  intro hm; rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hby⟩
                  rcases List.mem_map.mp hab with ⟨e, he, hEq'⟩
                  apply hy_occ; rw [hby.symm.trans (Prod.mk.inj hEq').2.symm]
                  simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                    List.mem_toFinset]
                  exact Or.inr (Or.inr (List.mem_map_of_mem he))
                have hne_in : u ∉ (toPairs T_pub).map Prod.fst := by
                  intro hm; rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hau⟩
                  rcases List.mem_map.mp hab with ⟨e, he, hEq'⟩
                  exact (lookupForwardEdge_eq_none_iff T_pub u).mp hlu e he
                    ((Prod.mk.inj hEq').1.trans hau)
                simpa only [toPairs, List.map_append, List.map_singleton] using
                  isPartialBijection_append inv.lazy.partialBij hne_in hne_out
              · rw [hrec]
                exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                  T_pub inv.lazy.capFree ⟨u, y0, false⟩ hy_occ
              · intro entry he
                exact hEval entry.1 (inv.lazy.keysNonempty entry he) (inv.lazy.keysUncovered entry
                  he)
              · intro entry he
                rcases inv.lazy.prefixClosed entry he with hcov | hhh
                · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast with
                  | none => rw [hev] at hcov; cases hcov
                  | some s => rw [hrec, evalAbsorption_mono p hev]; exact Or.inl rfl
                · exact Or.inr hhh
              · intro c hc hocc'
                rw [mem_occupiedCapsList_iff, hrec] at hocc'
                simp only [occupiedCapacities, List.map_append, List.map_singleton,
                  List.toFinset_append, Finset.mem_insert, Finset.mem_union, List.mem_toFinset,
                  List.mem_singleton] at hocc'
                rcases hocc' with h0 | h1' | h2'
                · exact inv.lazy.capsDisjoint c hc (by
                    rw [mem_occupiedCapsList_iff]
                    simp only [occupiedCapacities, Finset.mem_insert, h0, true_or])
                · rcases h1' with h1a | h1b
                  · exact inv.lazy.capsDisjoint c hc (by
                      rw [mem_occupiedCapsList_iff]
                      simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                        List.mem_toFinset, h1a, true_or, or_true])
                  · exact hbad_f.1 (h1b ▸ hc)
                · rcases h2' with h2a | h2b
                  · exact inv.lazy.capsDisjoint c hc (by
                      rw [mem_occupiedCapsList_iff]
                      simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                        List.mem_toFinset, h2a, or_true])
                  · exact hbad_f.2.2 (h2b ▸ hc)
            refine ⟨hlazy', isPartialBijection_append inv.fullPB hu_not_fst hy0_not_snd, ?_, ?_, ?_⟩
            · intro e he
              rw [hrec, List.mem_append, List.mem_singleton] at he
              rcases he with h1 | rfl
              · exact List.mem_append_left _ (inv.pubInFull e h1)
              · exact List.mem_append_right _ (List.mem_singleton_self _)
            · intro entry he
              rw [hiddenInput, heval_pres entry.1.dropLast]
              exact List.mem_append_left _ (inv.hidInFull entry he)
            · intro xy hxy
              rw [List.mem_append, List.mem_singleton] at hxy
              rcases hxy with h1 | rfl
              · rcases inv.fullOnly xy h1 with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
                · exact Or.inl ⟨e, by rw [hrec]; exact List.mem_append_left _ he, hEq'⟩
                · refine Or.inr ⟨entry, hentry, ?_⟩
                  rw [hiddenInput, heval_pres entry.1.dropLast]
                  exact hEq'
              · exact Or.inl ⟨⟨u, y0, false⟩,
                  by rw [hrec]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
      | inverse =>
        dsimp only [realSpongeGameStep] at hmem
        obtain ⟨p', hp', hEq⟩ := mem_support_fTransform _ _ hmem
        cases hlu : lookupInverseEdge T_pub u with
        | some x0 =>
          rw [hlu] at hEq
          have hmem_full : (x0, u) ∈ T_full := by
            obtain ⟨e, he, hi, ho⟩ := lookupInverseEdge_eq_some_mem hlu
            rw [← hi, ← ho]; exact inv.pubInFull e he
          have hlu_full := lookupInverse_eq_some_of_mem inv.fullPB hmem_full
          simp only [lazyBidirectionalRFStep, hlu_full, ProbDist.single,
            Finsupp.mem_support_iff] at hp'
          have hp'_eq : p' = (T_full, x0) := by
            by_contra hne; exact hp' (Finsupp.single_eq_of_ne hne)
          subst hp'_eq
          have hst := (Prod.mk.inj ((Prod.mk.inj hEq).1)).1
          rcases Prod.mk.inj hst with ⟨rfl, h2⟩
          rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
          exact inv
        | none =>
          rw [hlu] at hEq
          have hbad_f : (false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
              decide (capacityPart p p'.2 ∈
                occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false :=
            congrArg Prod.snd (Prod.mk.inj hEq).1
          simp only [Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
            List.mem_append, not_or] at hbad_f
          have hu_not_snd : u ∉ T_full.map Prod.snd := by
            intro hm
            rcases List.mem_map.mp hm with ⟨⟨x', y'⟩, hxy', rfl⟩
            rcases inv.fullOnly (x', y') hxy' with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
            · exact (lookupInverseEdge_eq_none_iff T_pub y').mp hlu e he (Prod.mk.inj hEq').2.symm
            · exact hbad_f.1 ((Prod.mk.inj hEq').2 ▸ List.mem_map_of_mem hentry)
          have hlu_full : lookupInverse T_full u = none :=
            (lookupInverse_eq_none_iff T_full u).mpr hu_not_snd
          simp only [lazyBidirectionalRFStep, hlu_full] at hp'
          obtain ⟨x0, _, hp'_eq⟩ := mem_support_fTransform _ _ hp'
          have hx0_eq : p'.2 = x0 := by
            rw [← hp'_eq]; split_ifs <;> rfl
          rw [hx0_eq] at hbad_f
          have hx0_not_fst : x0 ∉ T_full.map Prod.fst :=
            realGoodInv_not_mem_fst_of_cap_not_mem p inv (by
              rw [List.mem_append]; exact fun h => h.elim hbad_f.2.1 hbad_f.2.2)
          rw [ite_eq_left hx0_not_fst] at hp'_eq
          subst hp'_eq
          have hst := (Prod.mk.inj ((Prod.mk.inj hEq).1)).1
          rcases Prod.mk.inj hst with ⟨rfl, h2⟩
          rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
          have hx_occ : capacityPart p x0 ∉
              occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
            rw [← mem_occupiedCapsList_iff]; exact hbad_f.2.1
          have hrec := recordInverseEdge_eq_append_of_avoids p T_pub (y := u) hx_occ
          have hEval : ∀ bs' : List (ByteState p.rateBytes), bs' ≠ [] →
              evalAbsorption p T_pub (zeroState p.stateBytes) bs' = none →
              evalAbsorption p (recordInverseEdge T_pub x0 u) (zeroState p.stateBytes) bs' =
                none := by
            intro bs' hne_nil hnone
            by_contra hsome
            cases hnew : evalAbsorption p (recordInverseEdge T_pub x0 u)
                (zeroState p.stateBytes) bs' with
            | none => exact hsome hnew
            | some out =>
              rw [hrec] at hnew
              have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes)
                  T_pub ⟨x0, u, true⟩ := hx_occ
              have hinv_f := (no_preexisting_extension p T_pub ⟨x0, u, true⟩ hf bs' hne_nil
                hnew hnone).1
              cases hinv_f
          have heval_pres : ∀ bs' : List (ByteState p.rateBytes),
              evalWithHidden p (recordInverseEdge T_pub x0 u) hid bs' =
                evalWithHidden p T_pub hid bs' := by
            intro bs'
            unfold evalWithHidden
            cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) bs' with
            | some s => rw [hrec, evalAbsorption_mono p hev]
            | none =>
              have hne_nil : bs' ≠ [] := by intro hnil; subst hnil; cases hev
              rw [hEval bs' hne_nil hev]
          have hlazy' : LazyGoodInv p (recordInverseEdge T_pub x0 u) hid := by
            refine ⟨?_, ?_, inv.lazy.keysNodup, inv.lazy.keysNonempty, ?_, ?_,
              ?_, inv.lazy.capsNodup⟩
            · rw [hrec]
              have hne_in : x0 ∉ (toPairs T_pub).map Prod.fst := by
                intro hm; rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hax⟩
                rcases List.mem_map.mp hab with ⟨e, he, hEq'⟩
                apply hx_occ; rw [hax.symm.trans (Prod.mk.inj hEq').1.symm]
                simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                  List.mem_toFinset]
                exact Or.inr (Or.inl (List.mem_map_of_mem he))
              have hne_out : u ∉ (toPairs T_pub).map Prod.snd := by
                intro hm; rcases List.mem_map.mp hm with ⟨⟨a, b⟩, hab, hbu⟩
                rcases List.mem_map.mp hab with ⟨e, he, hEq'⟩
                exact (lookupInverseEdge_eq_none_iff T_pub u).mp hlu e he
                  ((Prod.mk.inj hEq').2.trans hbu)
              simpa only [toPairs, List.map_append, List.map_singleton] using
                isPartialBijection_append inv.lazy.partialBij hne_in hne_out
            · rw [hrec]
              exact capacityCollisionFree_append (capacityPart p) (zeroState p.capacityBytes)
                T_pub inv.lazy.capFree ⟨x0, u, true⟩ hx_occ
            · intro entry he
              exact hEval entry.1 (inv.lazy.keysNonempty entry he) (inv.lazy.keysUncovered entry he)
            · intro entry he
              rcases inv.lazy.prefixClosed entry he with hcov | hhh
              · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast with
                | none => rw [hev] at hcov; cases hcov
                | some s => rw [hrec, evalAbsorption_mono p hev]; exact Or.inl rfl
              · exact Or.inr hhh
            · intro c hc hocc'
              rw [mem_occupiedCapsList_iff, hrec] at hocc'
              simp only [occupiedCapacities, List.map_append, List.map_singleton,
                List.toFinset_append, Finset.mem_insert, Finset.mem_union, List.mem_toFinset,
                List.mem_singleton] at hocc'
              rcases hocc' with h0 | h1' | h2'
              · exact inv.lazy.capsDisjoint c hc (by
                  rw [mem_occupiedCapsList_iff]
                  simp only [occupiedCapacities, Finset.mem_insert, h0, true_or])
              · rcases h1' with h1a | h1b
                · exact inv.lazy.capsDisjoint c hc (by
                    rw [mem_occupiedCapsList_iff]
                    simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                      List.mem_toFinset, h1a, true_or, or_true])
                · exact hbad_f.2.2 (h1b ▸ hc)
              · rcases h2' with h2a | h2b
                · exact inv.lazy.capsDisjoint c hc (by
                    rw [mem_occupiedCapsList_iff]
                    simp only [occupiedCapacities, Finset.mem_insert, Finset.mem_union,
                      List.mem_toFinset, h2a, or_true])
                · exact hbad_f.1 (h2b ▸ hc)
          refine ⟨hlazy', isPartialBijection_append inv.fullPB hx0_not_fst hu_not_snd, ?_, ?_, ?_⟩
          · intro e he
            rw [hrec, List.mem_append, List.mem_singleton] at he
            rcases he with h1 | rfl
            · exact List.mem_append_left _ (inv.pubInFull e h1)
            · exact List.mem_append_right _ (List.mem_singleton_self _)
          · intro entry he
            rw [hiddenInput, heval_pres entry.1.dropLast]
            exact List.mem_append_left _ (inv.hidInFull entry he)
          · intro xy hxy
            rw [List.mem_append, List.mem_singleton] at hxy
            rcases hxy with h1 | rfl
            · rcases inv.fullOnly xy h1 with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
              · exact Or.inl ⟨e, by rw [hrec]; exact List.mem_append_left _ he, hEq'⟩
              · refine Or.inr ⟨entry, hentry, ?_⟩
                rw [hiddenInput, heval_pres entry.1.dropLast]
                exact hEq'
            · exact Or.inl ⟨⟨x0, u, true⟩,
                by rw [hrec]; exact List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  · -- Good-transition coupling
    rintro ⟨T_full, T_pub, hid⟩ o u v inv
    simp only [K, ProbDist.single, bindK_single, one_smul]
    have hlift : ∀ (μ₁ : ProbDist (((List (ByteState p.stateBytes × ByteState p.stateBytes) ×
            List (PermutationEdge (ByteState p.stateBytes)) ×
            List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
          (A.Y o × Bool)))
        (μ₂ : ProbDist (((List (PermutationEdge (ByteState p.stateBytes)) ×
            List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
          (A.Y o × Bool))),
        (∀ q ∈ μ₁.1.support, q.2.2 = q.1.2) →
        (∀ q ∈ μ₂.1.support, q.2.2 = q.1.2) →
        fTransform (fun q => ((q.1.1.2, q.1.2), q.2)) (μ₁.1.restrict fun q => q.1.2 = false) =
          μ₂.1.restrict (fun q => q.1.2 = false) →
        ((fTransform Prod.fst ((fTransform (ProbStep.tagged (X := A.X) (Y := withMBO A.Y) ⟨o, u⟩)
              μ₁.1).restrict fun sy => sy.2 = (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i))).bindK
            fun sb : (List (ByteState p.stateBytes × ByteState p.stateBytes) ×
                List (PermutationEdge (ByteState p.stateBytes)) ×
                List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool =>
              if sb.2 = false then
                (ProbDist.map (fun s₂ => (s₂, false)) (ProbDist.single sb.1.2)).1 else 0) =
          fTransform Prod.fst ((fTransform (ProbStep.tagged (X := A.X) (Y := withMBO A.Y) ⟨o, u⟩)
            μ₂.1).restrict fun sy => sy.2 = (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i)) := by
      intro μ₁ μ₂ hfl₁ hfl₂ hEq
      have hpred : ∀ {S : Type} (q : (S × Bool) × (A.Y o × Bool)),
          ((ProbStep.tagged (X := A.X) (Y := withMBO A.Y) ⟨o, u⟩ q).2 =
            (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i)) ↔ q.2 = (v, false) := fun q => by
        simp only [ProbStep.tagged, Sigma.mk.inj_iff, heq_eq_eq, true_and]
      rw [Distribution.restrict_fTransform, Distribution.restrict_congr _ hpred,
        fTransform_fTransform, bindK_fTransform,
        Distribution.restrict_fTransform, Distribution.restrict_congr _ hpred,
          fTransform_fTransform]
      have hfst_comp : ∀ {S : Type}, (Prod.fst ∘ ProbStep.tagged (X := A.X) (Y := withMBO A.Y)
          (S := S × Bool) ⟨o, u⟩) = Prod.fst := fun {S} => by funext q; rfl
      rw [hfst_comp, hfst_comp]
      have hrest_v : ∀ {S : Type} (μ : ProbDist ((S × Bool) × (A.Y o × Bool))),
          (∀ q ∈ μ.1.support, q.2.2 = q.1.2) →
          (μ.1.restrict fun q => q.2 = (v, false)) =
            ((μ.1.restrict fun q => q.1.2 = false).restrict fun q => q.2 = (v, false)) := by
        intro S μ hfl; ext q
        rw [Distribution.restrict, Distribution.restrict, Distribution.restrict,
          Finsupp.filter_apply, Finsupp.filter_apply, Finsupp.filter_apply]
        by_cases hmem : q ∈ μ.1.support
        · by_cases hq2 : q.2 = (v, false)
          · have h12 : q.1.2 = false := (hfl q hmem).symm.trans (congrArg Prod.snd hq2)
            simp only [hq2, h12, ↓reduceIte]
          · simp only [hq2, ↓reduceIte]
        · rw [Finsupp.notMem_support_iff.mp hmem]; simp only [ite_self]
      rw [hrest_v μ₁ hfl₁, hrest_v μ₂ hfl₂]
      have hL : (((μ₁.1.restrict fun q => q.1.2 = false).restrict fun q => q.2 = (v, false)).bindK
            fun q => if q.1.2 = false then
              (ProbDist.map (fun s₂ => (s₂, false)) (ProbDist.single q.1.1.2)).1 else 0) =
          fTransform Prod.fst ((fTransform (fun q => ((q.1.1.2, q.1.2), q.2))
            (μ₁.1.restrict fun q => q.1.2 = false)).restrict fun q => q.2 = (v, false)) := by
        rw [Distribution.restrict_fTransform, fTransform_fTransform, ← bindK_single_comp]
        apply bindK_congr
        intro q hq
        rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply,
          Distribution.restrict, Finsupp.filter_apply] at hq
        split_ifs at hq with hq2 h12
        · simp only [h12, ↓reduceIte, ProbDist.map_val, ProbDist.single, fTransform_single]
          dsimp only [Function.comp_def]
          rw [h12]
        · exact False.elim (hq rfl)
        · exact False.elim (hq rfl)
      exact hL.trans (by rw [hEq])
    apply hlift _ _
      (fun q hq => (realSpongeGameStep_flag p M spec q_pub (T_full, T_pub, hid) false o u q hq).1)
      (fun q hq => (lazyPathGameStep_flag p M spec q_pub (T_pub, hid) false o u q hq).1)
    rcases o with o | o
    · cases o
      dsimp only [realSpongeGameStep, lazyPathGameStep]
      rw [ProbDist.map_val, ProbDist.map_val, Distribution.restrict_fTransform,
        Distribution.restrict_fTransform, fTransform_fTransform]
      have hsim := (absorbRealGameBlocks_sim_sampleHidden p hp (w + q_pub) T_full T_pub hid []
        (paddedBlocks p (encode u)) inv (Or.inl rfl)).2
      rw [List.nil_append, newHiddenPrefixesFrom_nil_pref] at hsim
      have hzero_ewh : evalWithHidden p T_pub hid [] = zeroState p.stateBytes := rfl
      rw [hzero_ewh] at hsim
      exact hsim
    · cases o with
      | forward =>
        dsimp only [realSpongeGameStep, lazyPathGameStep]
        cases hlu : lookupForwardEdge T_pub u with
        | some y0 =>
          have hmem_full : (u, y0) ∈ T_full := by
            obtain ⟨e, he, hi, ho⟩ := lookupForwardEdge_eq_some_mem hlu
            rw [← hi, ← ho]; exact inv.pubInFull e he
          have hlu_full := lookupForward_eq_some_of_mem inv.fullPB hmem_full
          simp only [lazyBidirectionalRFStep, hlu_full, ProbDist.map_val, ProbDist.single,
            fTransform_single]
          have h1 : ∀ {S Y : Type} (s : S) (y : Y),
              Distribution.restrict (Finsupp.single ((s, false), (y, false)) (1 : ℝ))
                (fun q => q.1.2 = false) = Finsupp.single ((s, false), (y, false)) 1 := by
            intro S Y s y; ext a
            rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.single_apply]
            by_cases ha : ((s, false), (y, false)) = a
            · subst ha; simp only [↓reduceIte]
            · simp only [ha, ↓reduceIte, ite_self]
          exact (congrArg (fTransform _) (h1 (T_full, T_pub, hid) y0)).trans
            ((fTransform_single _ _ 1).trans (h1 (T_pub, hid) y0).symm)
        | none =>
          cases hrp : rootedPrefix p M encode T_pub u with
          | some bs =>
            by_cases hhid_mem : bs ∈ hid.map Prod.fst
            · simp only [hhid_mem, ↓reduceIte]
              obtain ⟨z, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhid_mem
              obtain ⟨pref, parent, last, hbs_eq, hpar, habs⟩ :=
                rootedPrefix_spec p M encode T_pub hrp
              have hdrop : bs.dropLast = pref := by
                rw [hbs_eq, List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),
                  List.dropLast_singleton, List.append_nil]
              have hlast : bs.getLastD (zeroState p.rateBytes) = last := by
                rw [hbs_eq, getLastD_append_singleton]
              have hhin : hiddenInput p T_pub hid bs = u := by
                rw [hiddenInput, hdrop, hlast, evalWithHidden, hpar, Option.getD_some, habs]
              have hmem_full : (u, z) ∈ T_full := hhin ▸ inv.hidInFull (bs, z) hz_mem
              have hlu_full := lookupForward_eq_some_of_mem inv.fullPB hmem_full
              simp only [lazyBidirectionalRFStep, hlu_full, hz_lu, Option.getD_some,
                ProbDist.map_val, ProbDist.single, fTransform_single]
              have h1 : ∀ {S Y : Type} (s : S) (y : Y),
                  Distribution.restrict (Finsupp.single ((s, false), (y, false)) (1 : ℝ))
                    (fun q => q.1.2 = false) = Finsupp.single ((s, false), (y, false)) 1 := by
                intro S Y s y; ext a
                rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.single_apply]
                by_cases ha : ((s, false), (y, false)) = a
                · subst ha; simp only [↓reduceIte]
                · simp only [ha, ↓reduceIte, ite_self]
              exact (congrArg (fTransform _)
                (h1 (T_full, recordForwardEdge T_pub u z, eraseHiddenKey p hid bs) z)).trans
                ((fTransform_single _ _ 1).trans
                  (h1 (recordForwardEdge T_pub u z, eraseHiddenKey p hid bs) z).symm)
            · simp only [hhid_mem, ↓reduceIte]
              by_cases hhitX : capacityPart p u ∈ hiddenCapsList p hid
              · have hdt : decide (capacityPart p u ∈ hiddenCapsList p hid) = true :=
                  decide_eq_true hhitX
                rw [ProbDist.map_val, ProbDist.map_val, Distribution.restrict_fTransform,
                  Distribution.restrict_fTransform]
                have hf1 : ∀ p' : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
                      ByteState p.stateBytes,
                    ((false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p p'.2 ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false) ↔ False := by
                  intro p'; simp only [hdt, Bool.false_or, Bool.true_or, reduceCtorEq]
                have hf2 : ∀ y : ByteState p.stateBytes,
                    ((false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p y ∈
                        occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false) ↔ False := by
                  intro y; simp only [hdt, Bool.false_or, Bool.true_or, reduceCtorEq]
                rw [Distribution.restrict_congr _ hf1, Distribution.restrict_false,
                  Distribution.restrict_congr _ hf2, Distribution.restrict_false,
                  fTransform_zero, fTransform_zero, fTransform_zero]
              · have hu_not_fst : u ∉ T_full.map Prod.fst := by
                  intro hm
                  rcases List.mem_map.mp hm with ⟨⟨x', y'⟩, hxy', rfl⟩
                  rcases inv.fullOnly (x', y') hxy' with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
                  · exact (lookupForwardEdge_eq_none_iff T_pub x').mp hlu e he
                      (Prod.mk.inj hEq').1.symm
                  · have hx' : x' = hiddenInput p T_pub hid entry.1 := (Prod.mk.inj hEq').1
                    rcases inv.lazy.prefixClosed entry hentry with hcov | hhh
                    · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast
                        with
                      | none => rw [hev] at hcov; cases hcov
                      | some s_pre =>
                        have habs : absorbBlock p s_pre (entry.1.getLastD (zeroState p.rateBytes)) =
                            x' := by rw [hx', hiddenInput, evalWithHidden, hev, Option.getD_some]
                        have hrp' := rootedPrefix_eq_some_of_path p M hp encode T_pub
                          inv.lazy.partialBij inv.lazy.capFree hev habs
                        rw [hrp] at hrp'
                        have hsplit : entry.1.dropLast ++
                            [entry.1.getLastD (zeroState p.rateBytes)] = entry.1 := by
                          have hne := inv.lazy.keysNonempty entry hentry
                          cases hrev : entry.1.reverse with
                          | nil => exact False.elim (hne (List.reverse_eq_nil_iff.mp hrev))
                          | cons last rev =>
                            have heq : entry.1 = rev.reverse ++ [last] := by
                              have := congrArg List.reverse hrev
                              simpa only [List.reverse_reverse, List.reverse_cons] using this
                            rw [heq, List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),
                              List.dropLast_singleton, List.append_nil, getLastD_append_singleton]
                        rw [hsplit] at hrp'
                        exact hhid_mem ((Option.some.inj hrp') ▸ List.mem_map_of_mem hentry)
                    · obtain ⟨z_pre, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhh
                      have hnone := inv.lazy.keysUncovered (entry.1.dropLast, z_pre) hz_mem
                      apply hhitX
                      rw [hx', hiddenInput, capacityPart_absorbBlock, evalWithHidden, hnone,
                        Option.getD_none, hz_lu, Option.getD_some]
                      exact List.mem_map_of_mem hz_mem
                have hlu_full : lookupForward T_full u = none :=
                  (lookupForward_eq_none_iff T_full u).mpr hu_not_fst
                simp only [lazyBidirectionalRFStep, hlu_full, ProbDist.map_val,
                  fTransform_fTransform, Distribution.restrict_fTransform]
                have hf_eq : ∀ y : ByteState p.stateBytes,
                    (if y ∉ T_full.map Prod.snd then (T_full ++ [(u, y)], y) else (T_full, y)).2 =
                      y := fun y => by split_ifs <;> rfl
                exact congrArg₂ fTransform
                  (funext fun y => by dsimp only [Function.comp_def]; rw [hf_eq y])
                  (Distribution.restrict_congr _ fun y => by
                    dsimp only [Function.comp_def]; rw [hf_eq y])
          | none =>
            by_cases hhitX : capacityPart p u ∈ hiddenCapsList p hid
            · have hdt : decide (capacityPart p u ∈ hiddenCapsList p hid) = true :=
                decide_eq_true hhitX
              rw [ProbDist.map_val, ProbDist.map_val, Distribution.restrict_fTransform,
                Distribution.restrict_fTransform]
              have hf1 : ∀ p' : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
                    ByteState p.stateBytes,
                  ((false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                    decide (capacityPart p p'.2 ∈
                      occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false) ↔ False := by
                intro p'; simp only [hdt, Bool.false_or, Bool.true_or, reduceCtorEq]
              have hf2 : ∀ y : ByteState p.stateBytes,
                  ((false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                    decide (capacityPart p y ∈
                      occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false) ↔ False := by
                intro y; simp only [hdt, Bool.false_or, Bool.true_or, reduceCtorEq]
              rw [Distribution.restrict_congr _ hf1, Distribution.restrict_false,
                Distribution.restrict_congr _ hf2, Distribution.restrict_false,
                fTransform_zero, fTransform_zero, fTransform_zero]
            · have hu_not_fst : u ∉ T_full.map Prod.fst := by
                intro hm
                rcases List.mem_map.mp hm with ⟨⟨x', y'⟩, hxy', rfl⟩
                rcases inv.fullOnly (x', y') hxy' with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
                · exact (lookupForwardEdge_eq_none_iff T_pub x').mp hlu e he
                    (Prod.mk.inj hEq').1.symm
                · have hx' : x' = hiddenInput p T_pub hid entry.1 := (Prod.mk.inj hEq').1
                  rcases inv.lazy.prefixClosed entry hentry with hcov | hhh
                  · cases hev : evalAbsorption p T_pub (zeroState p.stateBytes) entry.1.dropLast
                      with
                    | none => rw [hev] at hcov; cases hcov
                    | some s_pre =>
                      have habs : absorbBlock p s_pre (entry.1.getLastD (zeroState p.rateBytes)) =
                          x' := by rw [hx', hiddenInput, evalWithHidden, hev, Option.getD_some]
                      have hrp' := rootedPrefix_eq_some_of_path p M hp encode T_pub
                        inv.lazy.partialBij inv.lazy.capFree hev habs
                      rw [hrp] at hrp'; cases hrp'
                  · obtain ⟨z_pre, hz_lu, hz_mem⟩ := lookup_eq_some_of_mem_map_fst hid hhh
                    have hnone := inv.lazy.keysUncovered (entry.1.dropLast, z_pre) hz_mem
                    apply hhitX
                    rw [hx', hiddenInput, capacityPart_absorbBlock, evalWithHidden, hnone,
                      Option.getD_none, hz_lu, Option.getD_some]
                    exact List.mem_map_of_mem hz_mem
              have hlu_full : lookupForward T_full u = none :=
                (lookupForward_eq_none_iff T_full u).mpr hu_not_fst
              simp only [lazyBidirectionalRFStep, hlu_full, ProbDist.map_val,
                fTransform_fTransform, Distribution.restrict_fTransform]
              have hf_eq : ∀ y : ByteState p.stateBytes,
                  (if y ∉ T_full.map Prod.snd then (T_full ++ [(u, y)], y) else (T_full, y)).2 =
                    y := fun y => by split_ifs <;> rfl
              exact congrArg₂ fTransform
                (funext fun y => by dsimp only [Function.comp_def]; rw [hf_eq y])
                (Distribution.restrict_congr _ fun y => by
                  dsimp only [Function.comp_def]; rw [hf_eq y])
      | inverse =>
        dsimp only [realSpongeGameStep, lazyPathGameStep]
        cases hlu : lookupInverseEdge T_pub u with
        | some x0 =>
          have hmem_full : (x0, u) ∈ T_full := by
            obtain ⟨e, he, hi, ho⟩ := lookupInverseEdge_eq_some_mem hlu
            rw [← hi, ← ho]; exact inv.pubInFull e he
          have hlu_full := lookupInverse_eq_some_of_mem inv.fullPB hmem_full
          simp only [lazyBidirectionalRFStep, hlu_full, ProbDist.map_val, ProbDist.single,
            fTransform_single]
          have h1 : ∀ {S Y : Type} (s : S) (y : Y),
              Distribution.restrict (Finsupp.single ((s, false), (y, false)) (1 : ℝ))
                (fun q => q.1.2 = false) = Finsupp.single ((s, false), (y, false)) 1 := by
            intro S Y s y; ext a
            rw [Distribution.restrict, Finsupp.filter_apply, Finsupp.single_apply]
            by_cases ha : ((s, false), (y, false)) = a
            · subst ha; simp only [↓reduceIte]
            · simp only [ha, ↓reduceIte, ite_self]
          exact (congrArg (fTransform _) (h1 (T_full, T_pub, hid) x0)).trans
            ((fTransform_single _ _ 1).trans (h1 (T_pub, hid) x0).symm)
        | none =>
          by_cases hhitY : capacityPart p u ∈ hiddenCapsList p hid
          · have hdt : decide (capacityPart p u ∈ hiddenCapsList p hid) = true :=
              decide_eq_true hhitY
            rw [ProbDist.map_val, ProbDist.map_val, Distribution.restrict_fTransform,
              Distribution.restrict_fTransform]
            have hf1 : ∀ p' : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
                  ByteState p.stateBytes,
                ((false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                  decide (capacityPart p p'.2 ∈
                    occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false) ↔ False := by
              intro p'; simp only [hdt, Bool.false_or, Bool.true_or, reduceCtorEq]
            have hf2 : ∀ x : ByteState p.stateBytes,
                ((false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                  decide (capacityPart p x ∈
                    occupiedCapsList p T_pub ++ hiddenCapsList p hid)) = false) ↔ False := by
              intro x; simp only [hdt, Bool.false_or, Bool.true_or, reduceCtorEq]
            rw [Distribution.restrict_congr _ hf1, Distribution.restrict_false,
              Distribution.restrict_congr _ hf2, Distribution.restrict_false,
              fTransform_zero, fTransform_zero, fTransform_zero]
          · have hu_not_snd : u ∉ T_full.map Prod.snd := by
              intro hm
              rcases List.mem_map.mp hm with ⟨⟨x', y'⟩, hxy', rfl⟩
              rcases inv.fullOnly (x', y') hxy' with ⟨e, he, hEq'⟩ | ⟨entry, hentry, hEq'⟩
              · exact (lookupInverseEdge_eq_none_iff T_pub y').mp hlu e he
                  (Prod.mk.inj hEq').2.symm
              · exact hhitY ((Prod.mk.inj hEq').2 ▸ List.mem_map_of_mem hentry)
            have hlu_full : lookupInverse T_full u = none :=
              (lookupInverse_eq_none_iff T_full u).mpr hu_not_snd
            simp only [lazyBidirectionalRFStep, hlu_full, ProbDist.map_val,
              fTransform_fTransform, Distribution.restrict_fTransform]
            have hf_eq : ∀ x : ByteState p.stateBytes,
                (if x ∉ T_full.map Prod.fst then (T_full ++ [(x, u)], x) else (T_full, x)).2 =
                  x := fun x => by split_ifs <;> rfl
            exact congrArg₂ fTransform
              (funext fun x => by dsimp only [Function.comp_def]; rw [hf_eq x])
              (Distribution.restrict_congr _ fun x => by
                dsimp only [Function.comp_def]; rw [hf_eq x])

open Classical in
/-- **Game equivalence (`≡g`)**: `realSpongeGame` and `idealSpongeGame` have identical unset-MBO
transcript distributions. -/
theorem realSpongeGame_gameEquivalent_idealSpongeGame (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    (realSpongeGame p M spec q_pub).1.1.GameEquivalent
      (idealSpongeGame p M spec q_pub).1.1 := by
  intro h
  exact (realSpongeGame_gameEquivalent_lazyPathGame p M hp spec q_pub h).trans
    (lazyPathGame_gameEquivalent_idealSpongeGame p M hp henc spec q_pub h)

open Classical in
/-- **Hop 2 (`LazyBidirectionalRF` vs ideal sponge via `≡g` and `gameStepCost`)**:
`Δ (spongePublic • LazyBidirectionalRF) ((id ◁ spongeSimulator) • sharedIdealRO) ≤ Q^2 / |C|`. -/
theorem lazyBidirectionalRF_sponge_dist_ideal_le (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        LazyBidirectionalRF (ByteState p.stateBytes) (w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      ENNReal.ofReal
        (((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
  rw [← realSpongeGame_visible p M spec q_pub, ← idealSpongeGame_visible p M hp henc spec q_pub]
  let G := idealSpongeGame p M spec q_pub
  let H := realSpongeGame p M spec q_pub
  have hge : G.1.1.GameEquivalent H.1.1 := fun h =>
    (realSpongeGame_gameEquivalent_idealSpongeGame p M hp henc spec q_pub h).symm
  have hnonneg : 0 ≤ ((w + q_pub : ℕ) : ℝ) ^ 2 /
      (Fintype.card (ByteState p.capacityBytes) : ℝ) := by positivity
  let ε : NNReal := ⟨((w + q_pub : ℕ) : ℝ) ^ 2 /
    (Fintype.card (ByteState p.capacityBytes) : ℝ), hnonneg⟩
  have hdist : G.visible.1.transcriptDistance H.visible.1 ≤ ε :=
    RandomSystem.transcriptDistance_le_of_transcriptCost_le G.1.2.visible
      G.1.1.mass_unsetMBOs_le_visible
      (fun h => (hge h).trans_le (H.1.1.mass_unsetMBOs_le_visible h))
      G.1.1.mass_nil
      (fun h x _ hx => idealSpongeGame_loss_le_gameStepCost p M hp henc spec q_pub h x hx)
      (fun h hne => by
        apply transcriptCost_gameStepCost_le p M spec q_pub h
        · cases h with
          | nil => exact Or.inl rfl
          | cons z rest =>
            right
            cases hrev : z :: rest using List.reverseRecOn with
            | nil => cases hrev
            | append_singleton pre last =>
              rw [hrev] at hne
              by_contra hnd
              apply hne
              exact RandomSystem.mass_eq_zero_of_not_admitted G.visible.1
                (by
                  change ¬ (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain
                    (pre.map Prod.fst ++ [last.1])
                  simpa only [List.map_append, List.map_singleton] using hnd)
                last.2
        · clear hge hnonneg ε
          induction h using List.reverseRecOn with
          | nil => intro z hz; cases hz
          | append_singleton pre last ih =>
            rcases last with ⟨lx, ly⟩
            have hlast : lx.1 = ly.1 := by
              by_contra hne_p
              exact hne (G.1.2.visible pre lx ly (fun h => hne_p h.symm))
            have hpre : G.visible.1 pre ≠ 0 := by
              intro h0
              apply hne
              rcases G.visible.1.2.2.2 pre lx with ⟨μ, hμ, hw⟩
              have hnn : ∀ y, 0 ≤ μ y := fun y => by rw [hμ y]; exact G.visible.1.2.2.1 _
              have hle : μ ly ≤ μ.weight := by
                rw [Distribution.weight, Finsupp.sum]
                by_cases hm : ly ∈ μ.support
                · exact Finset.single_le_sum (fun y _ => hnn y) hm
                · rw [Finsupp.notMem_support_iff.mp hm]
                  exact Finset.sum_nonneg fun y _ => hnn y
              have hw0 : μ.weight = 0 := by rw [hw, h0]; split_ifs <;> rfl
              have hval0 : μ ly = 0 := le_antisymm (hw0 ▸ hle) (hnn ly)
              exact (hμ ly).symm.trans hval0
            intro z hz
            rcases List.mem_append.mp hz with hz' | hz'
            · exact ih hpre z hz'
            · rw [List.mem_singleton.mp hz']; exact hlast)
  have hsymm : Δ H.visible G.visible = Δ G.visible H.visible :=
    ConstructiveCryptography.CryptographicAlgebra.distance_comm H.visible G.visible
  rw [hsymm]
  have hcoe : (ε : ENNReal) = ENNReal.ofReal
      (((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
    rw [ENNReal.ofReal_eq_coe_nnreal hnonneg]; rfl
  rw [← hcoe]
  exact_mod_cast hdist

open Classical in
/-- **Path A (2-hop `≡g` game-equivalence + bidirectional switching indifferentiability bound)**:
combines `strongURP_attach_dist_lazyBidirectionalRF_le` (Hop 1) with `realSpongeGame ≡g
idealSpongeGame` (Hop 2) to establish the unified bound `Q^2 / |C| + C(Q, 2) / |S|`. -/
theorem sponge_indifferentiability_of_gameEquivalent (hp : p.Valid)
    {encode : M → List (BitVec 8)} (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      ENNReal.ofReal
        (((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ) +
          (((w + q_pub).choose 2 : ℕ) : ℝ) / (Fintype.card (ByteState p.stateBytes) : ℝ)) := by
  have h1 : Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      (spongePublic p M spec q_pub •
        LazyBidirectionalRF (ByteState p.stateBytes) (w + q_pub)) ≤
      ENNReal.ofReal
        ((((w + q_pub).choose 2 : ℕ) : ℝ) / (Fintype.card (ByteState p.stateBytes) : ℝ)) :=
    strongURP_attach_dist_lazyBidirectionalRF_le (ByteState p.stateBytes) (w + q_pub)
      (spongePublic p M spec q_pub)
  have h2 := lazyBidirectionalRF_sponge_dist_ideal_le p M hp henc spec q_pub
  have htri : Δ (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub))
      ((spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub) ≤
      ENNReal.ofReal
        ((((w + q_pub).choose 2 : ℕ) : ℝ) / (Fintype.card (ByteState p.stateBytes) : ℝ)) +
      ENNReal.ofReal
        (((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ)) :=
    (ConstructiveCryptography.CryptographicAlgebra.distance_triangle _ _ _).trans
      (add_le_add h1 h2)
  refine htri.trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_comm]

end GameEquivalenceProof

end Commons.Sponge
