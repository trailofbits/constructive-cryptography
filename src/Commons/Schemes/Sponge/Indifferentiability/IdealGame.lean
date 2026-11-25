module

public import Commons.Schemes.Sponge.Simulator

/-!
# Ideal sponge MBO game, ghost replay, and quadratic potential bound

Defines the monotone-MBO ideal sponge game `idealSpongeGame`, establishes its visible equivalence
with `(spec.toInterface ◁ spongeSimulator) • sharedIdealRO`, and bounds its per-step MBO-setting
loss by `gameStepCost` whose transcript sum is bounded by `(w + q_pub)^2 / |C|` [1, §4], [2, §4].

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

/-! ### Path A: 2-hop `≡g` game-equivalence proof via `BidirectionalSwitching` -/

section GameEquivalenceProof

variable (p : Parameters) (M : Type) [Fintype M] [DecidableEq M]

/-! #### General unset-MBO simulation lemma for monotone-MBO automata -/

omit [Fintype M] [DecidableEq M] in
/-- If a kernel `K` relates two monotone-MBO probabilistic automata on every `bad = false`
transition (preserving an invariant `Inv`), then the two games have identical unset-MBO
transcript probabilities (`GameEquivalent`). -/
lemma unsetMBOs_eq_of_good_simulation {A : Interface} {S₁ S₂ : Type}
    (step₁ : ProbStep (S₁ × Bool) A.I A.X (withMBO A.Y))
    (step₂ : ProbStep (S₂ × Bool) A.I A.X (withMBO A.Y))
    (init₁ : ProbDist S₁) (init₂ : ProbDist S₂)
    (hflag₁ : ∀ (s : S₁) (b : Bool) (i : A.I) (x : A.X i)
      (p : (S₁ × Bool) × (A.Y i × Bool)),
      p ∈ (step₁ (s, b) i x).1.support → p.2.2 = p.1.2 ∧ (b = true → p.1.2 = true))
    (hflag₂ : ∀ (s : S₂) (b : Bool) (i : A.I) (x : A.X i)
      (p : (S₂ × Bool) × (A.Y i × Bool)),
      p ∈ (step₂ (s, b) i x).1.support → p.2.2 = p.1.2 ∧ (b = true → p.1.2 = true))
    (Inv : S₁ → Prop) (K : S₁ → ProbDist S₂)
    (hinitInv : ∀ s₁ ∈ init₁.1.support, Inv s₁)
    (hinitK : init₁.bind K = init₂)
    (hstepInv : ∀ s₁ o u s₁' y, Inv s₁ →
      ((s₁', false), (y, false)) ∈ (step₁ (s₁, false) o u).1.support → Inv s₁')
    (hsim : ∀ s₁ o u y, Inv s₁ →
      (fTransform Prod.fst
          ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩) (step₁ (s₁,
            false) o u).1).restrict
            fun sy => sy.2 = (⟨o, (y, false)⟩ : Σ i, withMBO A.Y i))).bindK
        (fun sb => if sb.2 = false then ((K sb.1).map fun s₂ => (s₂, false)).1 else 0) =
      (K s₁).1.bindK fun s₂ =>
        fTransform Prod.fst
          ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩) (step₂ (s₂,
            false) o u).1).restrict
            fun sy => sy.2 = (⟨o, (y, false)⟩ : Σ i, withMBO A.Y i))) :
    (TypedGame.ofProbAutomaton step₁ init₁ hflag₁).1.1.GameEquivalent
      (TypedGame.ofProbAutomaton step₂ init₂ hflag₂).1.1 := by
  classical
  let liftK : S₁ × Bool → Distribution (S₂ × Bool) :=
    fun sb => if sb.2 = false then ((K sb.1).map fun s₂ => (s₂, false)).1 else 0
  have hbel : ∀ h : List ((Σ i, A.X i) × Σ i, A.Y i),
      (∀ sb ∈ (step₁.belief A.withMBO.inputDomain (init₁.map fun s => (s, false)).1
          (unsetMBOs h)).support, sb.2 = false ∧ Inv sb.1) ∧
      (step₁.belief A.withMBO.inputDomain (init₁.map fun s => (s, false)).1
          (unsetMBOs h)).bindK liftK =
        step₂.belief A.withMBO.inputDomain (init₂.map fun s => (s, false)).1
          (unsetMBOs h) := by
    intro h
    induction h using List.reverseRecOn with
    | nil =>
      simp only [unsetMBOs, List.map_nil, ProbStep.belief, ProbStep.beliefRev, List.reverse_nil]
      constructor
      · intro sb hsb
        rw [ProbDist.map_val, Finsupp.mem_support_iff] at hsb
        have hex : ∃ s₁ ∈ init₁.1.support, (s₁, false) = sb := by
          by_contra hnone
          push Not at hnone
          apply hsb
          change (init₁.1.sum fun a w => Finsupp.single (a, false) w) sb = 0
          rw [Finsupp.sum_apply]
          simp only [Finsupp.sum]
          apply Finset.sum_eq_zero
          intro s₁ hs₁
          exact Finsupp.single_eq_of_ne (hnone s₁ hs₁).symm
        rcases hex with ⟨s₁, hs₁, rfl⟩
        exact ⟨rfl, hinitInv s₁ hs₁⟩
      · rw [ProbDist.map_val, bindK_fTransform]
        have hEq : (init₁.1.bindK fun s₁ => liftK (s₁, false)) =
            (init₂.map fun s => (s, false)).1 := by
          simp only [liftK, ↓reduceIte, ProbDist.map_val, ← hinitK, ProbDist.bind_val,
            fTransform_bindK]
        exact hEq
    | append_singleton h z ih =>
      rcases z with ⟨⟨o, u⟩, ⟨o', v⟩⟩
      have hunset : unsetMBOs (h ++ [(⟨o, u⟩, ⟨o', v⟩)]) =
          unsetMBOs h ++ [(⟨o, u⟩, tagMBO false ⟨o', v⟩)] := by
        simp only [unsetMBOs, List.map_append, List.map_singleton, tagMBO]
      rw [hunset, ProbStep.belief_snoc, ProbStep.belief_snoc]
      by_cases hadm : A.withMBO.inputDomain (unsetMBOs h) ⟨o, u⟩
      · rw [ite_eq_left hadm, ite_eq_left hadm]
        set μ₁ := step₁.belief A.withMBO.inputDomain (init₁.map fun s => (s, false)).1
          (unsetMBOs h)
        set μ₂ := step₂.belief A.withMBO.inputDomain (init₂.map fun s => (s, false)).1
          (unsetMBOs h)
        have hsupp₁ := ih.1
        have hmap₁ := ih.2
        by_cases ho : o = o'
        · subst ho
          constructor
          · intro sb hsb
            simp only [ProbStep.transition, ProbStep.outcome, tagMBO] at hsb
            rw [Finsupp.mem_support_iff, bindK_apply, Finsupp.sum] at hsb
            have hex : ∃ sb₀ ∈ μ₁.support,
                μ₁ sb₀ * (fTransform Prod.fst
                  ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩)
                    (step₁ sb₀ o u).1).restrict
                      fun sy => sy.2 = (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i))) sb ≠ 0 := by
              by_contra hall
              push Not at hall
              exact hsb (Finset.sum_eq_zero hall)
            rcases hex with ⟨⟨s₀, b₀⟩, hsb₀, hne⟩
            rcases hsupp₁ (s₀, b₀) hsb₀ with ⟨rfl, hInv₀⟩
            have hne' : (fTransform Prod.fst
                ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩)
                  (step₁ (s₀, false) o u).1).restrict
                    fun sy => sy.2 = (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i))) sb ≠ 0 :=
              right_ne_zero_of_mul hne
            rw [Distribution.restrict_fTransform, fTransform_fTransform] at hne'
            change (((step₁ (s₀, false) o u).1.restrict fun a =>
                (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩ a).2 =
                  (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i)).sum
                fun a w => Finsupp.single a.1 w) sb ≠ 0 at hne'
            rw [Finsupp.sum_apply] at hne'
            simp only [Finsupp.sum] at hne'
            have hex' : ∃ p' ∈ ((step₁ (s₀, false) o u).1.restrict fun a =>
                (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩ a).2 =
                  (⟨o, (v, false)⟩ : Σ i, withMBO A.Y i)).support,
                p'.1 = sb := by
              by_contra hall
              push Not at hall
              apply hne'
              apply Finset.sum_eq_zero
              intro p' hp'
              exact Finsupp.single_eq_of_ne (hall p' hp').symm
            rcases hex' with ⟨⟨⟨s₁', b₁'⟩, ⟨y₁', by₁'⟩⟩, hp', rfl⟩
            rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply] at hp'
            split_ifs at hp' with heq
            · simp only [ProbStep.tagged, Sigma.mk.inj_iff, heq_eq_eq, true_and,
                Prod.mk.injEq] at heq
              rcases heq with ⟨rfl, rfl⟩
              have hfl := hflag₁ s₀ false o u ((s₁', b₁'), (y₁', false))
                (Finsupp.mem_support_iff.mpr hp')
              have hb1 : b₁' = false := hfl.1.symm
              subst hb1
              exact ⟨rfl, hstepInv s₀ o u s₁' y₁' hInv₀ (Finsupp.mem_support_iff.mpr hp')⟩
            · exact False.elim (hp' rfl)
          · rw [← hmap₁]
            simp only [ProbStep.transition, ProbStep.outcome, tagMBO]
            rw [bindK_bindK, bindK_bindK]
            apply bindK_congr
            intro ⟨s₀, b₀⟩ hsb₀
            rcases hsupp₁ (s₀, b₀) hsb₀ with ⟨rfl, hInv₀⟩
            have hrhs : (liftK (s₀, false)).bindK (fun s => fTransform Prod.fst
                ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩) (step₂ s o u).1).restrict
                  fun sy => sy.2 = ⟨o, (v, false)⟩)) =
                (K s₀).1.bindK fun s₂ => fTransform Prod.fst
                  ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩)
                    (step₂ (s₂, false) o u).1).restrict fun sy => sy.2 = ⟨o, (v, false)⟩) := by
              simp only [liftK, ↓reduceIte, ProbDist.map_val, bindK_fTransform]
              rfl
            rw [hrhs]
            exact hsim s₀ o u v hInv₀
        · have hzero₁ : step₁.transition μ₁ ⟨o, u⟩ (tagMBO false ⟨o', v⟩) = 0 := by
            simp only [ProbStep.transition, ProbStep.outcome, tagMBO]
            have hz : ∀ sb : S₁ × Bool,
                fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩)
                  (step₁ sb o u).1).restrict fun sy => sy.2 = ⟨o', (v, false)⟩) = 0 := by
              intro sb
              rw [Distribution.restrict_fTransform]
              have hf : ∀ x : (S₁ × Bool) × withMBO A.Y o,
                  ((ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩ x).2 =
                    (⟨o', (v, false)⟩ : Σ i, withMBO A.Y i)) ↔ False := by
                intro x
                simp only [ProbStep.tagged, iff_false]
                intro hEq
                exact ho (congrArg Sigma.fst hEq)
              refine (congrArg (fTransform Prod.fst) (congrArg (fTransform _)
                ((Distribution.restrict_congr _ hf).trans (Distribution.restrict_false _)))).trans
                  ?_
              rw [fTransform_zero, fTransform_zero]
            simp only [hz, bindK_zero_right]
          have hzero₂ : step₂.transition μ₂ ⟨o, u⟩ (tagMBO false ⟨o', v⟩) = 0 := by
            simp only [ProbStep.transition, ProbStep.outcome, tagMBO]
            have hz : ∀ sb : S₂ × Bool,
                fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩)
                  (step₂ sb o u).1).restrict fun sy => sy.2 = ⟨o', (v, false)⟩) = 0 := by
              intro sb
              rw [Distribution.restrict_fTransform]
              have hf : ∀ x : (S₂ × Bool) × withMBO A.Y o,
                  ((ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩ x).2 =
                    (⟨o', (v, false)⟩ : Σ i, withMBO A.Y i)) ↔ False := by
                intro x
                simp only [ProbStep.tagged, iff_false]
                intro hEq
                exact ho (congrArg Sigma.fst hEq)
              refine (congrArg (fTransform Prod.fst) (congrArg (fTransform _)
                ((Distribution.restrict_congr _ hf).trans (Distribution.restrict_false _)))).trans
                  ?_
              rw [fTransform_zero, fTransform_zero]
            simp only [hz, bindK_zero_right]
          rw [hzero₁, hzero₂, bindK_zero]
          exact ⟨fun _ h => False.elim (Finset.notMem_empty _ h), rfl⟩
      · rw [ite_eq_right hadm, ite_eq_right hadm, bindK_zero]
        exact ⟨fun _ h => False.elim (Finset.notMem_empty _ h), rfl⟩
  intro h
  change ((step₁.belief A.withMBO.inputDomain (init₁.map fun s => (s, false)).1
      (unsetMBOs h)).weight) =
    ((step₂.belief A.withMBO.inputDomain (init₂.map fun s => (s, false)).1
      (unsetMBOs h)).weight)
  have h1 := (hbel h).1
  have h2 := (hbel h).2
  rw [← h2, Distribution.weight_bindK]
  rw [Distribution.weight_eq_finsupp_sum]
  simp only [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro sb hsb
  rcases h1 sb hsb with ⟨hb, _⟩
  simp only [liftK, hb, ↓reduceIte, ProbDist.map_val, Distribution.weight_fTransform,
    (K sb.1).2.2, mul_one]

/-! #### Rooted path prefixes, ghost replay, and the `Φ(a, b)` potential -/

/-- All nonempty prefixes of a block sequence `blocks`, in ascending length order. -/
def nonemptyPrefixes {α : Type*} (blocks : List α) : List (List α) :=
  (List.range blocks.length).map fun i => blocks.take (i + 1)

omit [Fintype M] [DecidableEq M] in
lemma length_nonemptyPrefixes {α : Type*} (blocks : List α) :
    (nonemptyPrefixes blocks).length = blocks.length := by
  simp only [nonemptyPrefixes, List.length_map, List.length_range]

omit [Fintype M] [DecidableEq M] in
lemma mem_nonemptyPrefixes_ne_nil {α : Type*} {blocks bs : List α}
    (h : bs ∈ nonemptyPrefixes blocks) : bs ≠ [] := by
  rcases List.mem_map.mp h with ⟨i, hi, rfl⟩
  rw [List.mem_range] at hi
  intro hnil
  have hlen := congrArg List.length hnil
  simp only [List.length_take, List.length_nil] at hlen
  omega

open Classical in
/-- Prefix-completion key selector for a public forward query `x` against `T_pub`:
prefers `completingMessage` when one exists (ensuring unconditional consistency with
`simFixedROStep`), and otherwise picks any rooted prefix `pref ++ [b]` reaching `x`. -/
noncomputable def rootedPrefix (encode : M → List (BitVec 8))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (x : ByteState p.stateBytes) : Option (List (ByteState p.rateBytes)) :=
  match completingMessage p encode table x with
  | some m => some (paddedBlocks p (encode m))
  | none =>
    if h : ∃ (pref : List (ByteState p.rateBytes)) (s : ByteState p.stateBytes)
        (b : ByteState p.rateBytes),
        evalAbsorption p table (zeroState p.stateBytes) pref = some s ∧
        absorbBlock p s b = x then
      some (Classical.choose h ++ [Classical.choose (Classical.choose_spec h).choose_spec])
    else none

/-- Exact `ℕ`-valued double potential `2 * Φ(a, b) = 2a^2 + 4ab + b(b + 1)`. -/
def spongePotential2 (a b : ℕ) : ℕ :=
  2 * a ^ 2 + 4 * a * b + b * (b + 1)

omit [Fintype M] [DecidableEq M] in
lemma spongePotential2_le_two_mul_sq (a b : ℕ) :
    spongePotential2 a b ≤ 2 * (a + b) ^ 2 := by
  unfold spongePotential2
  have hb : b ≤ b ^ 2 := by
    cases b with
    | zero => exact le_rfl
    | succ k => nlinarith
  nlinarith

omit [Fintype M] [DecidableEq M] in
lemma spongePotential2_step_pub (a b : ℕ) :
    spongePotential2 (a + 1) b = spongePotential2 a b + 2 * (2 * a + 2 * b + 1) := by
  unfold spongePotential2
  ring

omit [Fintype M] [DecidableEq M] in
lemma spongePotential2_step_hid (a b : ℕ) :
    spongePotential2 a (b + 1) = spongePotential2 a b + 2 * (2 * a + b + 1) := by
  unfold spongePotential2
  ring

omit [Fintype M] [DecidableEq M] in
lemma spongePotential2_le_pop (a b : ℕ) (hb : 1 ≤ b) :
    spongePotential2 a b ≤ spongePotential2 (a + 1) (b - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, (Nat.sub_add_cancel hb).symm⟩
  simp only [Nat.add_sub_cancel, spongePotential2]
  nlinarith

/-- New nonempty prefixes of `blocks` not yet covered in `T_pub` and not already in `keys`. -/
def newHiddenPrefixes (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (keys : List (List (ByteState p.rateBytes))) (blocks : List (ByteState p.rateBytes)) :
    List (List (ByteState p.rateBytes)) :=
  (nonemptyPrefixes blocks).filter fun bs =>
    (evalAbsorption p T_pub (zeroState p.stateBytes) bs).isNone && !(keys.contains bs)

omit [Fintype M] [DecidableEq M] in
lemma newHiddenPrefixes_length_le (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (keys : List (List (ByteState p.rateBytes))) (blocks : List (ByteState p.rateBytes)) :
    (newHiddenPrefixes p T_pub keys blocks).length ≤ blocks.length := by
  calc (newHiddenPrefixes p T_pub keys blocks).length
      ≤ (nonemptyPrefixes blocks).length := List.length_filter_le _ _
    _ = blocks.length := length_nonemptyPrefixes blocks

open Classical in
/-- Deterministic ghost state `(T_pub, keys, a_count)` tracking the public table, the exact list
of unpopped hidden prefix keys, and the total count of fresh public queries. -/
noncomputable def ghostStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (st : List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes)) × ℕ)
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o)
    (yq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o) :
    List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes)) × ℕ :=
  let (T_pub, keys, a_cnt) := st
  match xq, yq with
  | ⟨Sum.inl Evaluation.Port.eval, m⟩, _ =>
    let added := newHiddenPrefixes p T_pub keys (paddedBlocks p (encode m))
    (T_pub, keys ++ added, a_cnt)
  | ⟨Sum.inr Bidirectional.Port.forward, x⟩, ⟨Sum.inr Bidirectional.Port.forward, y⟩ =>
    match lookupForwardEdge T_pub x with
    | some _ => (T_pub, keys, a_cnt)
    | none =>
      let keys' :=
        match rootedPrefix p M encode T_pub x with
        | some bs => if bs ∈ keys then keys.erase bs else keys
        | none => keys
      (recordForwardEdge T_pub x y, keys', a_cnt + 1)
  | ⟨Sum.inr Bidirectional.Port.inverse, y⟩, ⟨Sum.inr Bidirectional.Port.inverse, x⟩ =>
    match lookupInverseEdge T_pub y with
    | some _ => (T_pub, keys, a_cnt)
    | none => (recordInverseEdge T_pub x y, keys, a_cnt + 1)
  | _, _ => (T_pub, keys, a_cnt)

open Classical in
/-- Fold `ghostStep` over a visible transcript `h`. -/
noncomputable def replayGhost {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)) →
      List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes)) × ℕ :=
  List.foldl (fun st z => ghostStep p M spec q_pub st z.1 z.2) ([], [], 0)

omit [DecidableEq M] in
lemma replayGhost_nil {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    replayGhost p M spec q_pub [] = ([], [], 0) := rfl

omit [DecidableEq M] in
lemma replayGhost_snoc {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o)
    (yq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o) :
    replayGhost p M spec q_pub (h ++ [(xq, yq)]) =
      ghostStep p M spec q_pub (replayGhost p M spec q_pub h) xq yq := by
  simp only [replayGhost, List.foldl_append, List.foldl_cons, List.foldl_nil]

open Classical in
/-- Per-step MBO-set cost function for Path A, derived directly from `spongePotential2`. -/
noncomputable def gameStepCost {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) : ℝ :=
  let (T_pub, keys, a_cnt) := replayGhost p M spec q_pub h
  let b_cnt := keys.length
  match xq with
  | ⟨Sum.inl Evaluation.Port.eval, m⟩ =>
    let k := (newHiddenPrefixes p T_pub keys (paddedBlocks p (encode m))).length
    ((spongePotential2 a_cnt (b_cnt + k) - spongePotential2 a_cnt b_cnt : ℕ) : ℝ) /
      (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ))
  | ⟨Sum.inr Bidirectional.Port.forward, x⟩ =>
    match lookupForwardEdge T_pub x with
    | some _ => 0
    | none =>
      match rootedPrefix p M encode T_pub x with
      | some bs =>
        if bs ∈ keys then 0
        else ((2 * a_cnt + 2 * b_cnt + 1 : ℕ) : ℝ) /
          (Fintype.card (ByteState p.capacityBytes) : ℝ)
      | none =>
        ((2 * a_cnt + 2 * b_cnt + 1 : ℕ) : ℝ) /
          (Fintype.card (ByteState p.capacityBytes) : ℝ)
  | ⟨Sum.inr Bidirectional.Port.inverse, y⟩ =>
    match lookupInverseEdge T_pub y with
    | some _ => 0
    | none =>
      ((2 * a_cnt + 2 * b_cnt + 1 : ℕ) : ℝ) /
        (Fintype.card (ByteState p.capacityBytes) : ℝ)

omit [DecidableEq M] in
lemma gameStepCost_nonneg {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) :
    0 ≤ gameStepCost p M spec q_pub h xq := by
  unfold gameStepCost
  rcases hrg : replayGhost p M spec q_pub h with ⟨T_pub, keys, a_cnt⟩
  rcases xq with ⟨o, u⟩
  rcases o with o | o
  · cases o
    dsimp only
    positivity
  · cases o with
    | forward =>
      dsimp only
      cases lookupForwardEdge T_pub u with
      | some _ => exact le_rfl
      | none =>
        cases rootedPrefix p M encode T_pub u with
        | some bs =>
          by_cases hmem : bs ∈ keys
          · simp only [hmem, ↓reduceIte, le_refl]
          · simp only [hmem, ↓reduceIte]; positivity
        | none => positivity
    | inverse =>
      dsimp only
      cases lookupInverseEdge T_pub u with
      | some _ => exact le_rfl
      | none => positivity

omit [DecidableEq M] in
/-- Every replay step preserves `T_pub.length ≤ a_cnt` and
`a_cnt + keys.length ≤ honestWork + publicQueryCount`. -/
lemma replayGhost_bounds {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o))) :
    let (T_pub, keys, a_cnt) := replayGhost p M spec q_pub h
    T_pub.length ≤ a_cnt ∧
      a_cnt + keys.length ≤
        ((honestMessages p M spec q_pub h).map fun m =>
          paddedBlockCount p (encode m).length).sum + publicQueryCount h := by
  induction h using List.reverseRecOn with
  | nil =>
    simp only [replayGhost_nil, List.length_nil, honestMessages, List.filterMap_nil,
      List.map_nil, List.sum_nil, publicQueryCount_nil, add_zero, le_refl, and_self]
  | append_singleton h z ih =>
    rcases z with ⟨xq, yq⟩
    rw [replayGhost_snoc]
    rcases hrg : replayGhost p M spec q_pub h with ⟨T_pub, keys, a_cnt⟩
    rw [hrg] at ih
    rcases ih with ⟨hT_le, hsum_le⟩
    have hhon : honestMessages p M spec q_pub (h ++ [(xq, yq)]) =
        honestMessages p M spec q_pub h ++
          match xq with
          | ⟨Sum.inl Evaluation.Port.eval, m⟩ => [m]
          | ⟨Sum.inr _, _⟩ => [] := by
      unfold honestMessages
      rw [List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
      rcases xq with ⟨o, u⟩
      rcases o with o | o
      · cases o; rfl
      · rfl
    rw [hhon, List.map_append, List.sum_append, publicQueryCount_snoc]
    unfold ghostStep
    dsimp only
    rcases xq with ⟨o, u⟩; rcases yq with ⟨o', v⟩
    rcases o with o | o <;> rcases o' with o' | o'
    · cases o; cases o'
      simp only [List.length_append, List.map_singleton, List.sum_singleton, Sum.isRight_inl,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      have hk := newHiddenPrefixes_length_le p T_pub keys (paddedBlocks p (encode u))
      rw [length_paddedBlocks] at hk
      exact ⟨hT_le, by omega⟩
    · cases o; simp only [List.length_append, List.map_singleton, List.sum_singleton,
        Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, add_zero]
      have hk := newHiddenPrefixes_length_le p T_pub keys (paddedBlocks p (encode u))
      rw [length_paddedBlocks] at hk
      exact ⟨hT_le, by omega⟩
    · simp only [List.map_nil, List.sum_nil, add_zero, Sum.isRight_inr, ↓reduceIte]
      exact ⟨hT_le, by omega⟩
    · cases o <;> cases o'
      · dsimp only
        simp only [List.map_nil, List.sum_nil, add_zero, Sum.isRight_inr, ↓reduceIte]
        cases lookupForwardEdge T_pub u with
        | some _ => dsimp only; exact ⟨hT_le, by omega⟩
        | none =>
          dsimp only
          have hrec_le : (recordForwardEdge T_pub u v).length ≤ T_pub.length + 1 := by
            unfold recordForwardEdge
            by_cases hmem : v ∉ T_pub.map PermutationEdge.output
            · rw [ite_eq_left hmem, List.length_append, List.length_singleton]
            · rw [ite_eq_right hmem]; exact Nat.le_succ _
          have hk_le : (match rootedPrefix p M encode T_pub u with
              | some bs => if bs ∈ keys then keys.erase bs else keys
              | none => keys).length ≤ keys.length := by
            cases rootedPrefix p M encode T_pub u with
            | none => exact le_rfl
            | some bs =>
              by_cases hmem : bs ∈ keys
              · simp only [hmem, ↓reduceIte]
                rw [List.length_erase_of_mem hmem]; exact Nat.sub_le _ _
              · simp only [hmem, ↓reduceIte, le_refl]
          exact ⟨by omega, by omega⟩
      · dsimp only
        simp only [List.map_nil, List.sum_nil, add_zero, Sum.isRight_inr, ↓reduceIte]
        exact ⟨hT_le, by omega⟩
      · dsimp only
        simp only [List.map_nil, List.sum_nil, add_zero, Sum.isRight_inr, ↓reduceIte]
        exact ⟨hT_le, by omega⟩
      · dsimp only
        simp only [List.map_nil, List.sum_nil, add_zero, Sum.isRight_inr, ↓reduceIte]
        cases lookupInverseEdge T_pub u with
        | some _ => dsimp only; exact ⟨hT_le, by omega⟩
        | none =>
          dsimp only
          have hrec_le : (recordInverseEdge T_pub v u).length ≤ T_pub.length + 1 := by
            unfold recordInverseEdge
            by_cases hmem : v ∉ T_pub.map PermutationEdge.input
            · rw [ite_eq_left hmem, List.length_append, List.length_singleton]
            · rw [ite_eq_right hmem]; exact Nat.le_succ _
          exact ⟨by omega, by omega⟩

omit [DecidableEq M] in
/-- Telescoping bound: `transcriptCost gameStepCost h ≤ spongePotential2 a b / (2 * |C|)` on
every transcript whose replies stay at the queried port. -/
lemma transcriptCost_gameStepCost_le_potential {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (hport : ∀ z ∈ h, z.1.1 = z.2.1) :
    let (_, keys, a_cnt) := replayGhost p M spec q_pub h
    SystemAlgebra.transcriptCost (gameStepCost p M spec q_pub) h ≤
      (spongePotential2 a_cnt keys.length : ℝ) /
        (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
  have hC_pos : (0 : ℝ) < (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC_ne : (Fintype.card (ByteState p.capacityBytes) : ℝ) ≠ 0 := ne_of_gt hC_pos
  induction h using List.reverseRecOn with
  | nil =>
    simp only [replayGhost_nil, SystemAlgebra.transcriptCost, List.length_nil, spongePotential2,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    positivity
  | append_singleton h z ih =>
    rcases z with ⟨xq, yq⟩
    have hport_pre : ∀ z' ∈ h, z'.1.1 = z'.2.1 := fun z' hz' =>
      hport z' (List.mem_append_left _ hz')
    have hport_last : xq.1 = yq.1 := hport (xq,
      yq) (List.mem_append_right _ (List.mem_singleton_self _))
    have ih' := ih hport_pre
    rw [replayGhost_snoc, SystemAlgebra.transcriptCost_snoc]
    rcases hrg : replayGhost p M spec q_pub h with ⟨T_pub, keys, a_cnt⟩
    rw [hrg] at ih'
    unfold ghostStep
    rcases xq with ⟨o, u⟩; rcases yq with ⟨o', v⟩
    simp only at hport_last
    subst hport_last
    rcases o with o | o
    · cases o
      dsimp only
      conv_lhs => arg 2; unfold gameStepCost; rw [hrg]
      dsimp only
      simp only [List.length_append]
      set k := (newHiddenPrefixes p T_pub keys (paddedBlocks p (encode u))).length
      have hle : spongePotential2 a_cnt keys.length ≤ spongePotential2 a_cnt (keys.length + k) := by
        unfold spongePotential2
        have : keys.length ≤ keys.length + k := Nat.le_add_right _ _
        nlinarith
      calc SystemAlgebra.transcriptCost (gameStepCost p M spec q_pub) h +
            ((spongePotential2 a_cnt (keys.length + k) -
              spongePotential2 a_cnt keys.length : ℕ) : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ))
          ≤ (spongePotential2 a_cnt keys.length : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) +
            ((spongePotential2 a_cnt (keys.length + k) -
              spongePotential2 a_cnt keys.length : ℕ) : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) :=
            add_le_add ih' le_rfl
        _ = (spongePotential2 a_cnt (keys.length + k) : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
            rw [Nat.cast_sub hle, ← add_div]
            ring
    · cases o with
      | forward =>
        dsimp only
        conv_lhs => arg 2; unfold gameStepCost; rw [hrg]
        dsimp only
        cases hlu : lookupForwardEdge T_pub u with
        | some _ =>
          simpa only [add_zero] using ih'
        | none =>
          cases hrp : rootedPrefix p M encode T_pub u with
          | some bs =>
            by_cases hmem : bs ∈ keys
            · simp only [hmem, ↓reduceIte, add_zero]
              have hb1 : 1 ≤ keys.length := by
                cases keys with
                | nil => cases hmem
                | cons _ _ => simp only [List.length_cons]; omega
              rw [List.length_erase_of_mem hmem]
              exact ih'.trans (div_le_div_of_nonneg_right
                (Nat.cast_le.mpr (spongePotential2_le_pop a_cnt keys.length hb1)) (by positivity))
            · simp only [hmem, ↓reduceIte]
              calc SystemAlgebra.transcriptCost (gameStepCost p M spec q_pub) h +
                    ((2 * a_cnt + 2 * keys.length + 1 : ℕ) : ℝ) /
                      (Fintype.card (ByteState p.capacityBytes) : ℝ)
                  ≤ (spongePotential2 a_cnt keys.length : ℝ) /
                      (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) +
                    ((2 * a_cnt + 2 * keys.length + 1 : ℕ) : ℝ) /
                      (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
                    add_le_add ih' le_rfl
                _ = (spongePotential2 (a_cnt + 1) keys.length : ℝ) /
                      (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
                    rw [spongePotential2_step_pub]
                    push_cast
                    field_simp [hC_ne]
          | none =>
            calc SystemAlgebra.transcriptCost (gameStepCost p M spec q_pub) h +
                  ((2 * a_cnt + 2 * keys.length + 1 : ℕ) : ℝ) /
                    (Fintype.card (ByteState p.capacityBytes) : ℝ)
                ≤ (spongePotential2 a_cnt keys.length : ℝ) /
                    (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) +
                  ((2 * a_cnt + 2 * keys.length + 1 : ℕ) : ℝ) /
                    (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
                  add_le_add ih' le_rfl
              _ = (spongePotential2 (a_cnt + 1) keys.length : ℝ) /
                    (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
                  rw [spongePotential2_step_pub]
                  push_cast
                  field_simp [hC_ne]
      | inverse =>
        dsimp only
        conv_lhs => arg 2; unfold gameStepCost; rw [hrg]
        dsimp only
        cases hlu : lookupInverseEdge T_pub u with
        | some _ =>
          simpa only [add_zero] using ih'
        | none =>
          calc SystemAlgebra.transcriptCost (gameStepCost p M spec q_pub) h +
                ((2 * a_cnt + 2 * keys.length + 1 : ℕ) : ℝ) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ)
              ≤ (spongePotential2 a_cnt keys.length : ℝ) /
                  (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) +
                ((2 * a_cnt + 2 * keys.length + 1 : ℕ) : ℝ) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
                add_le_add ih' le_rfl
            _ = (spongePotential2 (a_cnt + 1) keys.length : ℝ) /
                  (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
                rw [spongePotential2_step_pub]
                push_cast
                field_simp [hC_ne]

omit [DecidableEq M] in
/-- Every admitted transcript with port-respecting replies has total Path-A cost at most
`((w + q_pub)^2) / |C|`. -/
lemma transcriptCost_gameStepCost_le {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (hadm : h = [] ∨ (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain (h.map Prod.fst))
    (hport : ∀ z ∈ h, z.1.1 = z.2.1) :
    SystemAlgebra.transcriptCost (gameStepCost p M spec q_pub) h ≤
      ((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
  have hC_pos : (0 : ℝ) < (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC_ne : (Fintype.card (ByteState p.capacityBytes) : ℝ) ≠ 0 := ne_of_gt hC_pos
  have hpot := transcriptCost_gameStepCost_le_potential p M spec q_pub h hport
  have hbds := replayGhost_bounds p M spec q_pub h
  rcases hrg : replayGhost p M spec q_pub h with ⟨T_pub, keys, a_cnt⟩
  rw [hrg] at hpot hbds
  have hwork := honestMessages_work_le p M spec q_pub h hadm
  have hpub := publicQueryCount_le_bound p h hadm
  have htot : a_cnt + keys.length ≤ w + q_pub := hbds.2.trans (Nat.add_le_add hwork hpub)
  have hpot_le : spongePotential2 a_cnt keys.length ≤ 2 * (w + q_pub) ^ 2 :=
    (spongePotential2_le_two_mul_sq a_cnt keys.length).trans
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left htot 2))
  calc SystemAlgebra.transcriptCost (gameStepCost p M spec q_pub) h
      ≤ (spongePotential2 a_cnt keys.length : ℝ) /
          (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := hpot
    _ ≤ ((2 * (w + q_pub) ^ 2 : ℕ) : ℝ) /
          (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hpot_le) (by positivity)
    _ = ((w + q_pub : ℕ) : ℝ) ^ 2 / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
        push_cast
        field_simp [hC_ne]

/-! #### Capacity-tracking helpers, `nodeLaw`, and `sampleHiddenList` -/

omit [Fintype M] [DecidableEq M] in
lemma probDist_map_bind {α β γ : Type*} (μ : ProbDist α) (f : α → ProbDist β) (g : β → γ) :
    (μ.bind f).map g = μ.bind fun a => (f a).map g := by
  apply Subtype.ext
  exact fTransform_bindK g μ.1 fun a => (f a).1

omit [Fintype M] [DecidableEq M] in
lemma probDist_bind_map {α β γ : Type*} (μ : ProbDist α) (f : α → β) (g : β → ProbDist γ) :
    (μ.map f).bind g = μ.bind fun a => g (f a) := by
  apply Subtype.ext
  exact bindK_fTransform f μ.1 fun b => (g b).1

omit [Fintype M] [DecidableEq M] in
lemma probDist_bind_assoc {α β γ : Type*} (μ : ProbDist α) (f : α → ProbDist β)
    (g : β → ProbDist γ) :
    (μ.bind f).bind g = μ.bind fun a => (f a).bind g := by
  apply Subtype.ext
  exact bindK_bindK μ.1 (fun a => (f a).1) (fun b => (g b).1)

omit [Fintype M] [DecidableEq M] in
lemma probDist_single_bind {α β : Type*} (a : α) (f : α → ProbDist β) :
    (ProbDist.single a).bind f = f a := by
  apply Subtype.ext
  change Distribution.bindK (Finsupp.single a (1 : ℝ)) (fun x => (f x).1) = (f a).1
  rw [bindK_single, one_smul]

omit [Fintype M] [DecidableEq M] in
lemma probDist_map_eq_bind {α β : Type*} (μ : ProbDist α) (f : α → β) :
    μ.map f = μ.bind fun a => ProbDist.single (f a) := by
  classical
  apply Subtype.ext
  ext b
  rw [ProbDist.map_val, ProbDist.bind_val, bindK_apply]
  change (μ.1.sum fun a w => Finsupp.single (f a) w) b =
    μ.1.sum fun a w => w * (Finsupp.single (f a) (1 : ℝ)) b
  rw [Finsupp.sum_apply]
  apply Finsupp.sum_congr
  intro a _
  rw [Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> ring

omit [Fintype M] [DecidableEq M] in
/-- Fubini swap for independent `ProbDist.bind` draws. -/
lemma probDist_bind_comm {α β γ : Type*} (μ : ProbDist α) (ν : ProbDist β)
    (f : α → β → ProbDist γ) :
    (μ.bind fun a => ν.bind fun b => f a b) =
      (ν.bind fun b => μ.bind fun a => f a b) := by
  apply Subtype.ext
  ext c
  simp only [ProbDist.bind_val, bindK_apply, Finsupp.sum]
  calc ∑ a ∈ μ.1.support, μ.1 a * ∑ b ∈ ν.1.support, ν.1 b * (f a b).1 c
      = ∑ a ∈ μ.1.support, ∑ b ∈ ν.1.support, μ.1 a * (ν.1 b * (f a b).1 c) := by
          apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]
    _ = ∑ b ∈ ν.1.support, ∑ a ∈ μ.1.support, μ.1 a * (ν.1 b * (f a b).1 c) := Finset.sum_comm
    _ = ∑ b ∈ ν.1.support, ν.1 b * ∑ a ∈ μ.1.support, μ.1 a * (f a b).1 c := by
          apply Finset.sum_congr rfl; intro b _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _; ring

/-- Occupied capacities in the public table `T_pub` (including the zero capacity). -/
def occupiedCapsList (T_pub : List (PermutationEdge (ByteState p.stateBytes))) :
    List (ByteState p.capacityBytes) :=
  zeroState p.capacityBytes ::
    (T_pub.map (fun e => capacityPart p e.input) ++ T_pub.map (fun e => capacityPart p e.output))

omit [Fintype M] [DecidableEq M] in
lemma length_occupiedCapsList (T_pub : List (PermutationEdge (ByteState p.stateBytes))) :
    (occupiedCapsList p T_pub).length = 2 * T_pub.length + 1 := by
  simp only [occupiedCapsList, List.length_cons, List.length_append, List.length_map]
  omega

omit [Fintype M] [DecidableEq M] in
lemma mem_occupiedCapsList_iff (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (c : ByteState p.capacityBytes) :
    c ∈ occupiedCapsList p T_pub ↔
      c ∈ occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) T_pub := by
  simp only [occupiedCapsList, occupiedCapacities, List.mem_cons, List.mem_append, List.mem_map,
    Finset.mem_insert, Finset.mem_union, List.mem_toFinset]

/-- Capacities currently held by unpopped hidden prefix outputs. -/
def hiddenCapsList
    (hidden : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) :
    List (ByteState p.capacityBytes) :=
  hidden.map fun entry => capacityPart p entry.2

omit [Fintype M] [DecidableEq M] in
lemma length_hiddenCapsList
    (hidden : List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) :
    (hiddenCapsList p hidden).length = hidden.length := by
  simp only [hiddenCapsList, List.length_map]

/-- Remove all entries for key `bs` from a hidden association list. -/
def eraseHiddenKey
    (hidden : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (bs : List (ByteState p.rateBytes)) :
    List (List (ByteState p.rateBytes) × ByteState p.stateBytes) :=
  hidden.filter fun entry => decide (entry.1 ≠ bs)

omit [Fintype M] [DecidableEq M] in
lemma map_fst_eraseHiddenKey_of_nodup
    (hidden : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (hnd : (hidden.map Prod.fst).Nodup) (bs : List (ByteState p.rateBytes)) :
    (eraseHiddenKey p hidden bs).map Prod.fst = (hidden.map Prod.fst).erase bs := by
  induction hidden with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases hnd with ⟨hnotmem, hnd_tl⟩
    unfold eraseHiddenKey
    rw [List.filter_cons]
    by_cases heq : hd.1 = bs
    · subst heq
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.erase_cons_head]
      have hfil : tl.filter (fun entry => decide (entry.1 ≠ hd.1)) = tl := by
        apply List.filter_eq_self.mpr
        intro a ha
        simp only [decide_eq_true_eq]
        intro hEq
        exact hnotmem (hEq ▸ List.mem_map_of_mem ha)
      rw [hfil]
    · have hne : decide (hd.1 ≠ bs) = true := decide_eq_true heq
      simp only [hne, ↓reduceIte, List.map_cons, List.erase_cons_tail (not_beq_of_ne heq)]
      exact congrArg (hd.1 :: ·) (ih hnd_tl)

open Classical in
/-- Exact single-node output law for a prefix `bs` given a fixed random oracle `ro`:
when `bs` is the padded block list of a message `m`, fix its digest to `ro m` with uniform tail;
otherwise draw a full uniform state. -/
noncomputable def nodeLaw (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes) (bs : List (ByteState p.rateBytes)) :
    ProbDist (ByteState p.stateBytes) :=
  if h : ∃ m : M, paddedBlocks p (encode m) = bs then
    (𝒰[ByteState (tailBytes p)]).map fun t => assembleState p (ro (Classical.choose h)) t
  else
    𝒰[ByteState p.stateBytes]

omit [DecidableEq M] in
lemma nodeLaw_cap_mem_mass (hp : p.Valid) (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes) (bs : List (ByteState p.rateBytes))
    (caps : Finset (ByteState p.capacityBytes)) :
    (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z ∈ caps) =
      (caps.card : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
  unfold nodeLaw
  split_ifs with h
  · rw [ProbDist.map_val, mass_fTransform]
    exact uniform_tail_mass_cap_mem p hp (ro (Classical.choose h)) caps
  · exact uniform_mass_cap_mem p hp caps

omit [DecidableEq M] in
lemma nodeLaw_cap_mem_list_le (hp : p.Valid) (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes) (bs : List (ByteState p.rateBytes))
    (caps : List (ByteState p.capacityBytes)) :
    (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z ∈ caps) ≤
      (caps.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
  have hEq : (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z ∈ caps) =
      (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z ∈ caps.toFinset) := by
    apply Distribution.mass_congr
    intro z
    simp only [List.mem_toFinset]
  rw [hEq, nodeLaw_cap_mem_mass p M hp encode ro bs caps.toFinset]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (List.toFinset_card_le caps)) (by positivity)

omit [DecidableEq M] in
lemma nodeLaw_paddedBlocks (hp : p.Valid) (encode : M → List (BitVec 8))
    (henc : Function.Injective encode) (ro : M → ByteState p.outputBytes) (m : M) :
    nodeLaw p M encode ro (paddedBlocks p (encode m)) =
      (𝒰[ByteState (tailBytes p)]).map fun t => assembleState p (ro m) t := by
  unfold nodeLaw
  have hex : ∃ m' : M, paddedBlocks p (encode m') = paddedBlocks p (encode m) := ⟨m, rfl⟩
  rw [dite_eq_left hex]
  have hch : Classical.choose hex = m :=
    henc (paddedBlocks_injective p hp.1 hp.2.2.2.2.1 hp.2.2.2.2.2 (Classical.choose_spec hex))
  rw [hch]

omit [DecidableEq M] in
lemma nodeLaw_rootedPrefix_of_completingMessage_none
    (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes)
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (x : ByteState p.stateBytes) (bs : List (ByteState p.rateBytes))
    (hnone : completingMessage p encode T_pub x = none)
    (hrp : rootedPrefix p M encode T_pub x = some bs) :
    nodeLaw p M encode ro bs = 𝒰[ByteState p.stateBytes] := by
  unfold rootedPrefix at hrp
  rw [hnone] at hrp
  split_ifs at hrp with hex
  · obtain ⟨rfl⟩ := Option.some.inj hrp
    unfold nodeLaw
    have hno : ¬ ∃ m : M,
        paddedBlocks p (encode m) =
          Classical.choose hex ++ [Classical.choose (Classical.choose_spec hex).choose_spec] := by
      rintro ⟨m, hm⟩
      have hspec := Classical.choose_spec (Classical.choose_spec hex).choose_spec
      have hdrop : (paddedBlocks p (encode m)).dropLast = Classical.choose hex := by
        rw [hm, List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
        simp only [List.dropLast_singleton, List.append_nil]
      have hmc : MatchesCompletion p encode T_pub x m := by
        refine ⟨Classical.choose (Classical.choose_spec hex),
          Classical.choose (Classical.choose_spec hex).choose_spec, ?_, ?_, hspec.2⟩
        · rw [hdrop]; exact hm
        · rw [hdrop]; exact hspec.1
      unfold completingMessage at hnone
      rw [dite_eq_left ⟨m, hmc⟩] at hnone
      cases hnone
    rw [dite_eq_right hno]

/-- Independent product law over a list of unpopped hidden prefix keys for a fixed `ro`. -/
noncomputable def sampleHiddenList (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes) :
    List (List (ByteState p.rateBytes)) →
      ProbDist (List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
  | [] => ProbDist.single []
  | bs :: rest =>
    (nodeLaw p M encode ro bs).bind fun z =>
      (sampleHiddenList encode ro rest).map fun l => (bs, z) :: l

omit [DecidableEq M] in
lemma sampleHiddenList_keys (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes) (keys : List (List (ByteState p.rateBytes))) :
    ∀ hidden ∈ (sampleHiddenList p M encode ro keys).1.support,
      hidden.map Prod.fst = keys := by
  induction keys with
  | nil =>
    intro hidden hh
    change hidden ∈ (Finsupp.single ([] : List (List (ByteState p.rateBytes) ×
      ByteState p.stateBytes)) (1 : ℝ)).support at hh
    rw [Finsupp.mem_support_iff] at hh
    have hEq : hidden = [] := by
      by_contra hne
      exact hh (Finsupp.single_eq_of_ne hne)
    subst hEq; rfl
  | cons bs rest ih =>
    intro hidden hh
    simp only [sampleHiddenList, ProbDist.bind_val, ProbDist.map_val] at hh
    rw [Finsupp.mem_support_iff, bindK_apply, Finsupp.sum] at hh
    have hex : ∃ z ∈ (nodeLaw p M encode ro bs).1.support,
        (fTransform (fun l => (bs,
          z) :: l) (sampleHiddenList p M encode ro rest).1) hidden ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hh
      apply Finset.sum_eq_zero
      intro z hz
      rw [hall z hz, mul_zero]
    rcases hex with ⟨z, _, hne⟩
    change ((sampleHiddenList p M encode ro rest).1.sum fun l w =>
      Finsupp.single ((bs, z) :: l) w) hidden ≠ 0 at hne
    rw [Finsupp.sum_apply] at hne
    simp only [Finsupp.sum] at hne
    have hex' : ∃ l ∈ (sampleHiddenList p M encode ro rest).1.support, (bs, z) :: l = hidden := by
      by_contra hall
      push Not at hall
      apply hne
      apply Finset.sum_eq_zero
      intro l hl
      exact Finsupp.single_eq_of_ne (hall l hl).symm
    rcases hex' with ⟨l, hl, rfl⟩
    simp only [List.map_cons, ih l hl]

omit [DecidableEq M] in
lemma sampleHiddenList_append (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes)
    (l₁ l₂ : List (List (ByteState p.rateBytes))) :
    sampleHiddenList p M encode ro (l₁ ++ l₂) =
      (sampleHiddenList p M encode ro l₁).bind fun h₁ =>
        (sampleHiddenList p M encode ro l₂).map fun h₂ => h₁ ++ h₂ := by
  induction l₁ with
  | nil =>
    simp only [List.nil_append, sampleHiddenList, probDist_single_bind]
    apply Subtype.ext
    change (sampleHiddenList p M encode ro l₂).1 =
      fTransform id (sampleHiddenList p M encode ro l₂).1
    rw [fTransform_id]
  | cons bs rest ih =>
    simp only [List.cons_append, sampleHiddenList, ih, probDist_bind_assoc, probDist_bind_map,
      probDist_map_bind]
    apply congrArg (ProbDist.bind _)
    funext z
    apply congrArg (ProbDist.bind _)
    funext h₁
    rw [ProbDist.map_map]
    rfl

omit [DecidableEq M] in
lemma sampleHiddenList_pop (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes)
    (keys : List (List (ByteState p.rateBytes))) (hnd : keys.Nodup)
    (bs : List (ByteState p.rateBytes)) (hmem : bs ∈ keys) :
    (sampleHiddenList p M encode ro keys).map
        (fun hidden =>
          (eraseHiddenKey p hidden bs,
            (hidden.lookup bs).getD (zeroState p.stateBytes))) =
      (nodeLaw p M encode ro bs).bind fun z =>
        (sampleHiddenList p M encode ro (keys.erase bs)).map fun hidden' => (hidden', z) := by
  induction keys with
  | nil => cases hmem
  | cons hd tl ih =>
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨hnotmem, hnd_tl⟩
    by_cases heq : hd = bs
    · subst heq
      simp only [sampleHiddenList, List.erase_cons_head, probDist_map_bind]
      apply congrArg (ProbDist.bind _)
      funext z
      rw [ProbDist.map_map]
      apply Subtype.ext
      change (sampleHiddenList p M encode ro tl).1.sum (fun hidden w =>
          Finsupp.single ((eraseHiddenKey p ((hd, z) :: hidden) hd,
            (((hd, z) :: hidden).lookup hd).getD (zeroState p.stateBytes))) w) =
        (sampleHiddenList p M encode ro tl).1.sum fun hidden w =>
          Finsupp.single (hidden, z) w
      apply Finsupp.sum_congr
      intro hidden hh
      have hkeys := sampleHiddenList_keys p M encode ro tl hidden hh
      have hfil : eraseHiddenKey p ((hd, z) :: hidden) hd = hidden := by
        unfold eraseHiddenKey
        rw [List.filter_cons]
        simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        apply List.filter_eq_self.mpr
        intro a ha
        simp only [decide_eq_true_eq]
        intro hEq
        exact hnotmem (hkeys ▸ hEq ▸ List.mem_map_of_mem ha)
      simp only [hfil, List.lookup_cons_self, Option.getD_some]
    · have hmem_tl : bs ∈ tl := by
        rcases List.mem_cons.mp hmem with rfl | htl
        · exact False.elim (heq rfl)
        · exact htl
      simp only [sampleHiddenList, List.erase_cons_tail (not_beq_of_ne heq)]
      rw [probDist_map_bind]
      have hstep : ∀ z_hd,
          ((sampleHiddenList p M encode ro tl).map fun l => (hd, z_hd) :: l).map
              (fun hidden =>
                (eraseHiddenKey p hidden bs,
                  (hidden.lookup bs).getD (zeroState p.stateBytes))) =
            ((sampleHiddenList p M encode ro tl).map fun hidden =>
                (eraseHiddenKey p hidden bs,
                  (hidden.lookup bs).getD (zeroState p.stateBytes))).map
              fun p' => ((hd, z_hd) :: p'.1, p'.2) := by
        intro z_hd
        rw [ProbDist.map_map, ProbDist.map_map]
        apply congrArg (fun f => (sampleHiddenList p M encode ro tl).map f)
        funext hidden
        have hdec : decide (hd ≠ bs) = true := decide_eq_true heq
        have hbeq : (bs == hd) = false := beq_false_of_ne (Ne.symm heq)
        simp only [Function.comp_def, eraseHiddenKey, List.filter_cons, hdec, ↓reduceIte,
          List.lookup_cons, hbeq]
      simp_rw [hstep, ih hnd_tl hmem_tl, probDist_map_bind, ProbDist.map_map]
      rw [probDist_bind_comm]
      apply congrArg (ProbDist.bind _)
      funext z
      simp only [Function.comp_def]

omit [DecidableEq M] in
lemma sampleHiddenList_cap_mem_mass (hp : p.Valid) (encode : M → List (BitVec 8))
    (ro : M → ByteState p.outputBytes)
    (keys : List (List (ByteState p.rateBytes))) (c : ByteState p.capacityBytes) :
    (sampleHiddenList p M encode ro keys).1.mass (fun hidden => c ∈ hiddenCapsList p hidden) ≤
      (keys.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
  induction keys with
  | nil =>
    simp only [sampleHiddenList, List.length_nil, Nat.cast_zero, zero_div]
    change Distribution.mass
      (Finsupp.single ([] : List (List (ByteState p.rateBytes) ×
        ByteState p.stateBytes)) (1 : ℝ)) (fun hidden => c ∈ hiddenCapsList p hidden) ≤ 0
    rw [Distribution.mass_single]
    simp only [hiddenCapsList, List.map_nil, List.not_mem_nil, ↓reduceIte, le_refl]
  | cons bs rest ih =>
    simp only [sampleHiddenList, ProbDist.bind_val, ProbDist.map_val, List.length_cons,
      Nat.cast_add, Nat.cast_one, add_div]
    rw [mass_bindK]
    have hsplit : ∀ z : ByteState p.stateBytes,
        (fTransform (fun l => (bs, z) :: l) (sampleHiddenList p M encode ro rest).1).mass
            (fun hidden => c ∈ hiddenCapsList p hidden) ≤
          (if capacityPart p z = c then 1 else 0) +
            (sampleHiddenList p M encode ro rest).1.mass
              (fun hidden => c ∈ hiddenCapsList p hidden) := by
      intro z
      rw [mass_fTransform]
      by_cases hcz : capacityPart p z = c
      · rw [ite_eq_left hcz]
        have hle1 : (sampleHiddenList p M encode ro rest).1.mass
            (fun l => c ∈ hiddenCapsList p ((bs, z) :: l)) ≤ 1 := by
          calc (sampleHiddenList p M encode ro rest).1.mass _
              ≤ (sampleHiddenList p M encode ro rest).1.weight :=
                Distribution.mass_le_weight (sampleHiddenList p M encode ro rest).2.1 _
            _ = 1 := (sampleHiddenList p M encode ro rest).2.2
        have hm0 : 0 ≤ (sampleHiddenList p M encode ro rest).1.mass
            (fun hidden => c ∈ hiddenCapsList p hidden) :=
          Distribution.NonNeg.mass_nonneg (sampleHiddenList p M encode ro rest).2.1 _
        linarith
      · rw [ite_eq_right hcz, zero_add]
        apply le_of_eq
        apply Distribution.mass_congr
        intro l
        simp only [hiddenCapsList, List.map_cons, List.mem_cons]
        exact or_iff_right (Ne.symm hcz)
    calc (nodeLaw p M encode ro bs).1.sum
          (fun z w => w * (fTransform (fun l => (bs, z) :: l)
            (sampleHiddenList p M encode ro rest).1).mass
              (fun hidden => c ∈ hiddenCapsList p hidden))
        ≤ (nodeLaw p M encode ro bs).1.sum
            (fun z w => w * ((if capacityPart p z = c then 1 else 0) +
              (sampleHiddenList p M encode ro rest).1.mass
                (fun hidden => c ∈ hiddenCapsList p hidden))) := by
          simp only [Finsupp.sum]
          apply Finset.sum_le_sum
          intro z _
          exact mul_le_mul_of_nonneg_left (hsplit z) ((nodeLaw p M encode ro bs).2.1 z)
      _ = (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z = c) +
            (sampleHiddenList p M encode ro rest).1.mass
              (fun hidden => c ∈ hiddenCapsList p hidden) := by
          simp only [Finsupp.sum, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
          have hw : ∑ x ∈ (nodeLaw p M encode ro bs).1.support,
              (nodeLaw p M encode ro bs).1 x = 1 := (nodeLaw p M encode ro bs).2.2
          rw [hw, one_mul]
          congr 1
          classical
          rw [Distribution.mass_eq_sum_of_support_subset _ Finset.Subset.rfl, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro z _
          split_ifs <;> ring
      _ ≤ 1 / (Fintype.card (ByteState p.capacityBytes) : ℝ) +
            (rest.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
          have h1 : (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z = c) =
              1 / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
            have hEq : (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z = c) =
                (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z ∈ ({c} : Finset _)) :=
                  by
              apply Distribution.mass_congr; intro z; simp only [Finset.mem_singleton]
            rw [hEq, nodeLaw_cap_mem_mass p M hp encode ro bs {c}, Finset.card_singleton,
              Nat.cast_one]
          rw [h1]
          exact add_le_add le_rfl ih
      _ = (rest.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) +
            1 / (Fintype.card (ByteState p.capacityBytes) : ℝ) := add_comm _ _

/-! #### Ideal path game (`idealSpongeGame`), visible equivalence, and MBO-set domination -/

omit [Fintype M] [DecidableEq M] in
lemma nonemptyPrefixes_nodup {α : Type*} (blocks : List α) :
    (nonemptyPrefixes blocks).Nodup := by
  unfold nonemptyPrefixes
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj hEq
  rw [List.mem_range] at hi hj
  have hlen := congrArg List.length hEq
  simp only [List.length_take] at hlen
  omega

omit [Fintype M] [DecidableEq M] in
lemma keys_append_newHiddenPrefixes_nodup
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (keys : List (List (ByteState p.rateBytes))) (hnd : keys.Nodup)
    (blocks : List (ByteState p.rateBytes)) :
    (keys ++ newHiddenPrefixes p T_pub keys blocks).Nodup := by
  rw [List.nodup_append]
  refine ⟨hnd, (nonemptyPrefixes_nodup blocks).filter _, ?_⟩
  intro a ha b hb hEq
  subst hEq
  unfold newHiddenPrefixes at hb
  rw [List.mem_filter] at hb
  have hnc : !(keys.contains a) = true := (Bool.and_eq_true _ _ |>.mp hb.2).2
  simp only [Bool.not_eq_true', List.contains_iff_mem, decide_eq_false_iff_not] at hnc
  exact hnc ha

/-- Sequentially sample hidden outputs for a list of newly added prefixes while tracking whether
any drawn output capacity collides with previously occupied or hidden capacities. -/
noncomputable def sampleHiddenPrefixesWithBad
    (draw : List (ByteState p.rateBytes) → ProbDist (ByteState p.stateBytes))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes))) :
    List (List (ByteState p.rateBytes) × ByteState p.stateBytes) →
    Bool →
    List (List (ByteState p.rateBytes)) →
    ProbDist (List (List (ByteState p.rateBytes) × ByteState p.stateBytes) × Bool)
  | hid, bad, [] => ProbDist.single (hid, bad)
  | hid, bad, bs :: rest =>
    (draw bs).bind fun z =>
      let hit : Bool :=
        decide (capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)
      sampleHiddenPrefixesWithBad draw T_pub (hid ++ [(bs, z)]) (bad || hit) rest

omit [Fintype M] [DecidableEq M] in
lemma sampleHiddenPrefixesWithBad_monotone
    (draw : List (ByteState p.rateBytes) → ProbDist (ByteState p.stateBytes))
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hidden : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (bad : Bool) (added : List (List (ByteState p.rateBytes))) :
    ∀ p' ∈ (sampleHiddenPrefixesWithBad p draw T_pub hidden bad added).1.support,
      bad = true → p'.2 = true := by
  induction added generalizing hidden bad with
  | nil =>
    intro p' hp' hbad
    change p' ∈ (Finsupp.single (hidden, bad) (1 : ℝ)).support at hp'
    rw [Finsupp.mem_support_iff] at hp'
    have hEq : p' = (hidden, bad) := by
      by_contra hne
      exact hp' (Finsupp.single_eq_of_ne hne)
    subst hEq; exact hbad
  | cons bs rest ih =>
    intro p' hp' hbad
    simp only [sampleHiddenPrefixesWithBad, ProbDist.bind_val] at hp'
    rw [Finsupp.mem_support_iff, bindK_apply, Finsupp.sum] at hp'
    have hex : ∃ z ∈ (draw bs).1.support,
        (sampleHiddenPrefixesWithBad p draw T_pub (hidden ++ [(bs, z)])
          (bad || decide (capacityPart p z ∈ occupiedCapsList p T_pub ++
            hiddenCapsList p hidden)) rest).1 p' ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hp'
      apply Finset.sum_eq_zero
      intro z hz
      rw [hall z hz, mul_zero]
    rcases hex with ⟨z, _, hne⟩
    exact ih (hidden ++ [(bs, z)]) _ p' (Finsupp.mem_support_iff.mpr hne)
      (by simp only [hbad, Bool.true_or])

omit [DecidableEq M] in
lemma sampleHiddenPrefixesWithBad_map_fst
    (encode : M → List (BitVec 8)) (ro : M → ByteState p.outputBytes)
    (T_pub : List (PermutationEdge (ByteState p.stateBytes)))
    (hidden : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (bad : Bool) (added : List (List (ByteState p.rateBytes))) :
    (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hidden bad added).map Prod.fst =
      (sampleHiddenList p M encode ro added).map fun ext => hidden ++ ext := by
  induction added generalizing hidden bad with
  | nil =>
    simp only [sampleHiddenPrefixesWithBad, sampleHiddenList]
    apply Subtype.ext
    change fTransform Prod.fst (Finsupp.single (hidden, bad) (1 : ℝ)) =
      fTransform (fun ext => hidden ++ ext) (Finsupp.single [] (1 : ℝ))
    simp only [fTransform_single, List.append_nil]
  | cons bs rest ih =>
    simp only [sampleHiddenPrefixesWithBad, sampleHiddenList, probDist_map_bind]
    apply congrArg (ProbDist.bind _)
    funext z
    rw [ih, ProbDist.map_map]
    apply congrArg (fun f => (sampleHiddenList p M encode ro rest).map f)
    funext ext
    simp only [Function.comp_def, List.append_assoc, List.singleton_append]

omit [DecidableEq M] in
lemma sampleHiddenPrefixesWithBad_bad_mass_le (hp : p.Valid)
    (encode : M → List (BitVec 8)) (ro : M → ByteState p.outputBytes)
    (T_pub : List (PermutationEdge (ByteState p.stateBytes))) {a_cnt : ℕ}
    (hT : T_pub.length ≤ a_cnt)
    (hidden : List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (added : List (List (ByteState p.rateBytes))) :
    (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hidden false added).1.mass
        (fun p' => p'.2 = true) ≤
      ((spongePotential2 a_cnt (hidden.length + added.length) -
        spongePotential2 a_cnt hidden.length : ℕ) : ℝ) /
        (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
  have hC_pos : (0 : ℝ) < (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hC_ne : (Fintype.card (ByteState p.capacityBytes) : ℝ) ≠ 0 := ne_of_gt hC_pos
  induction added generalizing hidden with
  | nil =>
    simp only [sampleHiddenPrefixesWithBad, List.length_nil, add_zero, Nat.sub_self, Nat.cast_zero,
      zero_div]
    change Distribution.mass (Finsupp.single (hidden, false) (1 : ℝ))
      (fun p' => p'.2 = true) ≤ 0
    rw [Distribution.mass_single]
    simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  | cons bs rest ih =>
    simp only [sampleHiddenPrefixesWithBad, ProbDist.bind_val, Bool.false_or, List.length_cons]
    rw [mass_bindK]
    set S := occupiedCapsList p T_pub ++ hiddenCapsList p hidden
    have hS_len : S.length ≤ 2 * a_cnt + hidden.length + 1 := by
      simp only [S, List.length_append, length_occupiedCapsList, length_hiddenCapsList]
      omega
    have hpot_step :
        spongePotential2 a_cnt (hidden.length + 1) ≤
          spongePotential2 a_cnt (hidden.length + (rest.length + 1)) := by
      unfold spongePotential2
      have : hidden.length + 1 ≤ hidden.length + (rest.length + 1) := by omega
      nlinarith
    have hpot_base :
        spongePotential2 a_cnt hidden.length ≤
          spongePotential2 a_cnt (hidden.length + (rest.length + 1)) := by
      unfold spongePotential2
      have : hidden.length ≤ hidden.length + (rest.length + 1) := by omega
      nlinarith
    have hbound : ∀ z : ByteState p.stateBytes,
        (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub (hidden ++ [(bs, z)])
            (decide (capacityPart p z ∈ S)) rest).1.mass (fun p' => p'.2 = true) ≤
          (if capacityPart p z ∈ S then (1 : ℝ) else 0) +
            ((spongePotential2 a_cnt (hidden.length + 1 + rest.length) -
              spongePotential2 a_cnt (hidden.length + 1) : ℕ) : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
      intro z
      by_cases hmem : capacityPart p z ∈ S
      · rw [ite_eq_left hmem]
        have hle1 : (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
            (hidden ++ [(bs, z)]) (decide (capacityPart p z ∈ S)) rest).1.mass
            (fun p' => p'.2 = true) ≤ 1 := by
          calc _ ≤ (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
                (hidden ++ [(bs, z)]) (decide (capacityPart p z ∈ S)) rest).1.weight :=
                Distribution.mass_le_weight
                  (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
                    (hidden ++ [(bs, z)]) (decide (capacityPart p z ∈ S)) rest).2.1 _
            _ = 1 :=
                (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
                  (hidden ++ [(bs, z)]) (decide (capacityPart p z ∈ S)) rest).2.2
        have hnonneg : (0 : ℝ) ≤
            ((spongePotential2 a_cnt (hidden.length + 1 + rest.length) -
              spongePotential2 a_cnt (hidden.length + 1) : ℕ) : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by positivity
        linarith
      · rw [ite_eq_right hmem, zero_add]
        have hdec : decide (capacityPart p z ∈ S) = false := decide_eq_false hmem
        rw [hdec]
        have hih := ih (hidden ++ [(bs, z)])
        simp only [List.length_append, List.length_singleton] at hih
        exact hih
    calc (nodeLaw p M encode ro bs).1.sum
          (fun z w => w * (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub
            (hidden ++ [(bs, z)]) (decide (capacityPart p z ∈ S)) rest).1.mass
              (fun p' => p'.2 = true))
        ≤ (nodeLaw p M encode ro bs).1.sum
            (fun z w => w * ((if capacityPart p z ∈ S then (1 : ℝ) else 0) +
              ((spongePotential2 a_cnt (hidden.length + 1 + rest.length) -
                spongePotential2 a_cnt (hidden.length + 1) : ℕ) : ℝ) /
                (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)))) := by
          simp only [Finsupp.sum]
          apply Finset.sum_le_sum
          intro z _
          exact mul_le_mul_of_nonneg_left (hbound z) ((nodeLaw p M encode ro bs).2.1 z)
      _ = (nodeLaw p M encode ro bs).1.mass (fun z => capacityPart p z ∈ S) +
            ((spongePotential2 a_cnt (hidden.length + 1 + rest.length) -
              spongePotential2 a_cnt (hidden.length + 1) : ℕ) : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
          simp only [Finsupp.sum, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
          have hw : ∑ x ∈ (nodeLaw p M encode ro bs).1.support,
              (nodeLaw p M encode ro bs).1 x = 1 := (nodeLaw p M encode ro bs).2.2
          rw [hw, one_mul]
          congr 1
          classical
          rw [Distribution.mass_eq_sum_of_support_subset _ Finset.Subset.rfl, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro z _
          split_ifs <;> ring
      _ ≤ (S.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) +
            ((spongePotential2 a_cnt (hidden.length + 1 + rest.length) -
              spongePotential2 a_cnt (hidden.length + 1) : ℕ) : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) :=
          add_le_add (nodeLaw_cap_mem_list_le p M hp encode ro bs S) le_rfl
      _ ≤ ((2 * a_cnt + hidden.length + 1 : ℕ) : ℝ) /
              (Fintype.card (ByteState p.capacityBytes) : ℝ) +
            ((spongePotential2 a_cnt (hidden.length + 1 + rest.length) -
              spongePotential2 a_cnt (hidden.length + 1) : ℕ) : ℝ) /
              (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) :=
          add_le_add (div_le_div_of_nonneg_right (Nat.cast_le.mpr hS_len) (by positivity)) le_rfl
      _ = ((spongePotential2 a_cnt (hidden.length + (rest.length + 1)) -
            spongePotential2 a_cnt hidden.length : ℕ) : ℝ) /
            (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)) := by
          have hidx : hidden.length + 1 + rest.length = hidden.length + (rest.length + 1) := by
            omega
          rw [hidx, Nat.cast_sub hpot_step, Nat.cast_sub hpot_base, spongePotential2_step_hid]
          push_cast
          field_simp [hC_ne]
          ring

open Classical in
/-- Auxiliary ghost-key automaton on `(ro, T_pub, keys)` used to relate `idealSpongeGame.visible`
simultaneously to `idealFixedROStep` and to `sampleHiddenList ro keys`. -/
noncomputable def idealGhostStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    ProbStep ((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes)))
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y
  | (ro, T_pub, keys), Sum.inl Evaluation.Port.eval, m =>
    let added := newHiddenPrefixes p T_pub keys (paddedBlocks p (encode m))
    ProbDist.single ((ro, T_pub, keys ++ added), ro m)
  | (ro, T_pub, keys), Sum.inr Bidirectional.Port.forward, x =>
    match lookupForwardEdge T_pub x with
    | some y => ProbDist.single ((ro, T_pub, keys), y)
    | none =>
      let keys' :=
        match rootedPrefix p M encode T_pub x with
        | some bs => if bs ∈ keys then keys.erase bs else keys
        | none => keys
      match completingMessage p encode T_pub x with
      | some m =>
        (𝒰[ByteState (tailBytes p)]).map fun t =>
          let y := assembleState p (ro m) t
          ((ro, recordForwardEdge T_pub x y, keys'), y)
      | none =>
        (𝒰[ByteState p.stateBytes]).map fun y =>
          ((ro, recordForwardEdge T_pub x y, keys'), y)
  | (ro, T_pub, keys), Sum.inr Bidirectional.Port.inverse, y =>
    match lookupInverseEdge T_pub y with
    | some x => ProbDist.single ((ro, T_pub, keys), x)
    | none =>
      (𝒰[ByteState p.stateBytes]).map fun x =>
        ((ro, recordInverseEdge T_pub x y, keys), x)

open Classical in
/-- Visible-only path automaton on `(ro, T_pub, hidden)` obtained by dropping the MBO flag from
`idealSpongeGameStep`. -/
noncomputable def idealPathVisStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    ProbStep ((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y
  | (ro, T_pub, hid), Sum.inl Evaluation.Port.eval, m =>
    let added := newHiddenPrefixes p T_pub (hid.map Prod.fst) (paddedBlocks p (encode m))
    (sampleHiddenList p M encode ro added).map fun ext =>
      ((ro, T_pub, hid ++ ext), ro m)
  | (ro, T_pub, hid), Sum.inr Bidirectional.Port.forward, x =>
    match lookupForwardEdge T_pub x with
    | some y => ProbDist.single ((ro, T_pub, hid), y)
    | none =>
      match rootedPrefix p M encode T_pub x with
      | some bs =>
        if bs ∈ hid.map Prod.fst then
          let z := (hid.lookup bs).getD (zeroState p.stateBytes)
          ProbDist.single ((ro, recordForwardEdge T_pub x z, eraseHiddenKey p hid bs), z)
        else
          match completingMessage p encode T_pub x with
          | some m =>
            (𝒰[ByteState (tailBytes p)]).map fun t =>
              let y := assembleState p (ro m) t
              ((ro, recordForwardEdge T_pub x y, hid), y)
          | none =>
            (𝒰[ByteState p.stateBytes]).map fun y =>
              ((ro, recordForwardEdge T_pub x y, hid), y)
      | none =>
        match completingMessage p encode T_pub x with
        | some m =>
          (𝒰[ByteState (tailBytes p)]).map fun t =>
            let y := assembleState p (ro m) t
            ((ro, recordForwardEdge T_pub x y, hid), y)
        | none =>
          (𝒰[ByteState p.stateBytes]).map fun y =>
            ((ro, recordForwardEdge T_pub x y, hid), y)
  | (ro, T_pub, hid), Sum.inr Bidirectional.Port.inverse, y =>
    match lookupInverseEdge T_pub y with
    | some x => ProbDist.single ((ro, T_pub, hid), x)
    | none =>
      (𝒰[ByteState p.stateBytes]).map fun x =>
        ((ro, recordInverseEdge T_pub x y, hid), x)

open Classical in
/-- Monotone-MBO game step of the ideal path game `idealSpongeGame`. -/
noncomputable def idealSpongeGameStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    ProbStep (((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool)
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (withMBO (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y)
  | ((ro, T_pub, hid), bad), Sum.inl Evaluation.Port.eval, m =>
    let added := newHiddenPrefixes p T_pub (hid.map Prod.fst) (paddedBlocks p (encode m))
    (sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hid bad added).map
      fun ⟨hid', bad'⟩ => (((ro, T_pub, hid'), bad'), (ro m, bad'))
  | ((ro, T_pub, hid), bad), Sum.inr Bidirectional.Port.forward, x =>
    match lookupForwardEdge T_pub x with
    | some y => ProbDist.single (((ro, T_pub, hid), bad), (y, bad))
    | none =>
      match rootedPrefix p M encode T_pub x with
      | some bs =>
        if bs ∈ hid.map Prod.fst then
          let z := (hid.lookup bs).getD (zeroState p.stateBytes)
          ProbDist.single
            (((ro, recordForwardEdge T_pub x z, eraseHiddenKey p hid bs), bad), (z, bad))
        else
          let hitX : Bool := decide (capacityPart p x ∈ hiddenCapsList p hid)
          let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
          match completingMessage p encode T_pub x with
          | some m =>
            (𝒰[ByteState (tailBytes p)]).map fun t =>
              let y := assembleState p (ro m) t
              let bad' := bad || hitX || decide (capacityPart p y ∈ occ)
              (((ro, recordForwardEdge T_pub x y, hid), bad'), (y, bad'))
          | none =>
            (𝒰[ByteState p.stateBytes]).map fun y =>
              let bad' := bad || hitX || decide (capacityPart p y ∈ occ)
              (((ro, recordForwardEdge T_pub x y, hid), bad'), (y, bad'))
      | none =>
        let hitX : Bool := decide (capacityPart p x ∈ hiddenCapsList p hid)
        let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
        match completingMessage p encode T_pub x with
        | some m =>
          (𝒰[ByteState (tailBytes p)]).map fun t =>
            let y := assembleState p (ro m) t
            let bad' := bad || hitX || decide (capacityPart p y ∈ occ)
            (((ro, recordForwardEdge T_pub x y, hid), bad'), (y, bad'))
        | none =>
          (𝒰[ByteState p.stateBytes]).map fun y =>
            let bad' := bad || hitX || decide (capacityPart p y ∈ occ)
            (((ro, recordForwardEdge T_pub x y, hid), bad'), (y, bad'))
  | ((ro, T_pub, hid), bad), Sum.inr Bidirectional.Port.inverse, y =>
    match lookupInverseEdge T_pub y with
    | some x => ProbDist.single (((ro, T_pub, hid), bad), (x, bad))
    | none =>
      let hitY : Bool := decide (capacityPart p y ∈ hiddenCapsList p hid)
      let occ := occupiedCapsList p T_pub ++ hiddenCapsList p hid
      (𝒰[ByteState p.stateBytes]).map fun x =>
        let bad' := bad || hitY || decide (capacityPart p x ∈ occ)
        (((ro, recordInverseEdge T_pub x y, hid), bad'), (x, bad'))

omit [DecidableEq M] in
lemma idealSpongeGameStep_flag {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (s : (M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (b : Bool) (i : (spec.toInterface ⊗ PrimitiveInterface p q_pub).I)
    (x : (spec.toInterface ⊗ PrimitiveInterface p q_pub).X i)
    (q : (((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool) ×
      ((spec.toInterface ⊗ PrimitiveInterface p q_pub).Y i × Bool))
    (hq : q ∈ (idealSpongeGameStep p M spec q_pub (s, b) i x).1.support) :
    q.2.2 = q.1.2 ∧ (b = true → q.1.2 = true) := by
  rcases s with ⟨ro, T_pub, hid⟩
  have hmap_supp : ∀ {α β : Type} (μ : ProbDist α) (f : α → β) (y : β),
      y ∈ (μ.map f).1.support → ∃ a ∈ μ.1.support, f a = y := by
    intro α β μ f y hy
    rw [ProbDist.map_val, Finsupp.mem_support_iff] at hy
    by_contra hall
    push Not at hall
    apply hy
    change (μ.1.sum fun a w => Finsupp.single (f a) w) y = 0
    rw [Finsupp.sum_apply]
    simp only [Finsupp.sum]
    exact Finset.sum_eq_zero fun a ha => Finsupp.single_eq_of_ne (hall a ha).symm
  have hsing_supp : ∀ {α : Type} (a y : α),
      y ∈ (ProbDist.single a).1.support → y = a := by
    intro α a y hy
    change y ∈ (Finsupp.single a (1 : ℝ)).support at hy
    rw [Finsupp.mem_support_iff] at hy
    by_contra hne
    exact hy (Finsupp.single_eq_of_ne hne)
  rcases i with i | i
  · cases i
    dsimp only [idealSpongeGameStep] at hq
    rcases hmap_supp _ _ _ hq with ⟨⟨hid', bad'⟩, hmem, rfl⟩
    exact ⟨rfl, sampleHiddenPrefixesWithBad_monotone p _ T_pub hid b _ _ hmem⟩
  · cases i with
    | forward =>
      dsimp only [idealSpongeGameStep] at hq
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
            cases hcm : completingMessage p encode T_pub x with
            | some m =>
              rw [hcm] at hq
              rcases hmap_supp _ _ _ hq with ⟨t, _, rfl⟩
              exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩
            | none =>
              rw [hcm] at hq
              rcases hmap_supp _ _ _ hq with ⟨y, _, rfl⟩
              exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩
        | none =>
          rw [hrp] at hq
          cases hcm : completingMessage p encode T_pub x with
          | some m =>
            rw [hcm] at hq
            rcases hmap_supp _ _ _ hq with ⟨t, _, rfl⟩
            exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩
          | none =>
            rw [hcm] at hq
            rcases hmap_supp _ _ _ hq with ⟨y, _, rfl⟩
            exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩
    | inverse =>
      dsimp only [idealSpongeGameStep] at hq
      cases hlu : lookupInverseEdge T_pub x with
      | some x' =>
        rw [hlu] at hq
        rcases hsing_supp _ _ hq with rfl; exact ⟨rfl, fun h => h⟩
      | none =>
        rw [hlu] at hq
        rcases hmap_supp _ _ _ hq with ⟨x', _, rfl⟩
        exact ⟨rfl, fun h => by simp only [h, Bool.true_or]⟩

/-- Initial distribution on `(ro, [], [])` with `ro ∼ 𝒰[M → ByteState p.outputBytes]`. -/
noncomputable def idealGameInit :
    ProbDist ((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) :=
  (𝒰[M → ByteState p.outputBytes]).map fun ro => (ro, [], [])

/-- The ideal path game whose visible system is `(spec.toInterface ◁ spongeSimulator) •
sharedIdealRO`
and whose monotone MBO monitors capacity collisions among public and hidden sponge nodes. -/
noncomputable def idealSpongeGame {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    TypedGame (spec.toInterface ⊗ PrimitiveInterface p q_pub) :=
  TypedGame.ofProbAutomaton (idealSpongeGameStep p M spec q_pub) (idealGameInit p M)
    (idealSpongeGameStep_flag p M spec q_pub)

omit [Fintype M] [DecidableEq M] in
/-- For any monotone-MBO automaton, the unset-MBO belief is supported on `bad = false` and lies
pointwise below the visible belief. -/
lemma unsetMBOs_belief_le_visible {A : Interface} {S : Type}
    (step : ProbStep (S × Bool) A.I A.X (withMBO A.Y)) (init : ProbDist S)
    (hflag : ∀ (s : S) (b : Bool) (i : A.I) (x : A.X i)
      (q : (S × Bool) × (A.Y i × Bool)),
      q ∈ (step (s, b) i x).1.support → q.2.2 = q.1.2 ∧ (b = true → q.1.2 = true))
    (h : List ((Σ i, A.X i) × Σ i, A.Y i)) :
    (∀ sb ∈ (step.belief A.withMBO.inputDomain (init.map fun s => (s, false)).1
        (unsetMBOs h)).support, sb.2 = false) ∧
    (∀ sb : S × Bool,
      step.belief A.withMBO.inputDomain (init.map fun s => (s, false)).1 (unsetMBOs h) sb ≤
        (ProbStep.forgetMBO step).belief A.inputDomain (init.map fun s => (s, false)).1 h sb) := by
  classical
  have hrestrict_nn : ∀ {α : Type} {μ : Distribution α} (_ : μ.NonNeg) (P : α → Prop),
      (μ.restrict P).NonNeg := fun hμ P a => by
    rw [Distribution.restrict, Finsupp.filter_apply]
    split_ifs
    · exact hμ a
    · exact le_rfl
  have hnonneg_trans : ∀ (μ : Distribution (S × Bool)) (_hμ : μ.NonNeg)
      (xq : Σ i, A.X i) (yq : Σ i, withMBO A.Y i),
      (step.transition μ xq yq).NonNeg := by
    intro μ hμ ⟨o, u⟩ yq sb
    simp only [ProbStep.transition, ProbStep.outcome]
    rw [bindK_apply, Finsupp.sum]
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (hμ a)
      (Distribution.NonNeg.fTransform (hrestrict_nn
        (Distribution.NonNeg.fTransform (step a o u).2.1 _) _) _ sb)
  have hmono_trans : ∀ (μ₁ μ₂ : Distribution (S × Bool))
      (_hle : ∀ a, μ₁ a ≤ μ₂ a) (xq : Σ i, A.X i) (yq : Σ i, withMBO A.Y i) (sb : S × Bool),
      step.transition μ₁ xq yq sb ≤ step.transition μ₂ xq yq sb := by
    intro μ₁ μ₂ hle ⟨o, u⟩ yq sb
    simp only [ProbStep.transition, ProbStep.outcome]
    rw [bindK_apply, bindK_apply]
    set k : S × Bool → ℝ := fun a =>
      (fTransform Prod.fst ((fTransform (ProbStep.tagged (Y := withMBO A.Y) ⟨o, u⟩)
        (step a o u).1).restrict fun sy => sy.2 = yq)) sb
    have hk_nn : ∀ a, 0 ≤ k a := fun a =>
      Distribution.NonNeg.fTransform (hrestrict_nn
        (Distribution.NonNeg.fTransform (step a o u).2.1 _) _) _ sb
    set S_both := μ₁.support ∪ μ₂.support
    have h1 : μ₁.sum (fun a w => w * k a) = ∑ a ∈ S_both, μ₁ a * k a := by
      rw [Finsupp.sum]
      exact Finset.sum_subset Finset.subset_union_left fun a _ ha => by
        rw [Finsupp.notMem_support_iff.mp ha, zero_mul]
    have h2 : μ₂.sum (fun a w => w * k a) = ∑ a ∈ S_both, μ₂ a * k a := by
      rw [Finsupp.sum]
      exact Finset.sum_subset Finset.subset_union_right fun a _ ha => by
        rw [Finsupp.notMem_support_iff.mp ha, zero_mul]
    rw [h1, h2]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hle a) (hk_nn a)
  have hbelief_nn : ∀ h',
      (step.belief A.withMBO.inputDomain (init.map fun s => (s,
        false)).1 (unsetMBOs h')).NonNeg := by
    intro h'
    induction h' using List.reverseRecOn with
    | nil =>
      simp only [unsetMBOs, List.map_nil, ProbStep.belief, ProbStep.beliefRev, List.reverse_nil,
        ProbDist.map_val]
      exact Distribution.NonNeg.fTransform init.2.1 _
    | append_singleton h' z ih' =>
      have hunset : unsetMBOs (h' ++ [z]) = unsetMBOs h' ++ [(z.1, tagMBO false z.2)] := by
        simp only [unsetMBOs, List.map_append, List.map_singleton, tagMBO]
      rw [hunset, ProbStep.belief_snoc]
      split_ifs
      · exact hnonneg_trans _ ih' z.1 (tagMBO false z.2)
      · intro _; exact le_rfl
  induction h using List.reverseRecOn with
  | nil =>
    simp only [unsetMBOs, List.map_nil, ProbStep.belief, ProbStep.beliefRev, List.reverse_nil]
    refine ⟨?_, fun _ => le_rfl⟩
    intro sb hsb
    rw [ProbDist.map_val, Finsupp.mem_support_iff] at hsb
    have hex : ∃ s ∈ init.1.support, (s, false) = sb := by
      by_contra hall; push Not at hall; apply hsb
      change (init.1.sum fun a w => Finsupp.single (a, false) w) sb = 0
      rw [Finsupp.sum_apply]; simp only [Finsupp.sum]
      exact Finset.sum_eq_zero fun a ha => Finsupp.single_eq_of_ne (hall a ha).symm
    rcases hex with ⟨s, _, rfl⟩; rfl
  | append_singleton h z ih =>
    rcases z with ⟨⟨o, u⟩, ⟨o', v⟩⟩
    have hunset : unsetMBOs (h ++ [(⟨o, u⟩, ⟨o', v⟩)]) =
        unsetMBOs h ++ [(⟨o, u⟩, tagMBO false ⟨o', v⟩)] := by
      simp only [unsetMBOs, List.map_append, List.map_singleton, tagMBO]
    rw [hunset, ProbStep.belief_snoc, ProbStep.belief_snoc]
    have hadm_iff : A.withMBO.inputDomain (unsetMBOs h) ⟨o, u⟩ ↔ A.inputDomain h ⟨o, u⟩ := by
      change A.domain ((unsetMBOs h).map Prod.fst ++ [⟨o, u⟩]) ↔
        A.domain (h.map Prod.fst ++ [⟨o, u⟩])
      have hfst : (unsetMBOs h).map Prod.fst = h.map Prod.fst := by
        simp only [unsetMBOs, List.map_map, Function.comp_def]
      rw [hfst]
    by_cases hadm : A.inputDomain h ⟨o, u⟩
    · rw [ite_eq_left (hadm_iff.mpr hadm), ite_eq_left hadm]
      constructor
      · intro sb hsb
        obtain ⟨sb₀, _, hout⟩ :=
          ProbStep.mem_support_transition step ⟨o, u⟩ (tagMBO false ⟨o', v⟩) hsb
        obtain ⟨q, hq, htag⟩ := mem_support_fTransform _ _ hout
        have hsbeq : q.1 = sb := congrArg Prod.fst htag
        have hzeq : (⟨o, q.2⟩ : Σ i, withMBO A.Y i) = tagMBO false ⟨o', v⟩ := congrArg Prod.snd htag
        have hmb := (hflag sb₀.1 sb₀.2 o u q hq).1
        have hzb : q.2.2 = false := by
          have ho : o = o' := congrArg Sigma.fst hzeq
          subst ho
          simp only [tagMBO, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hzeq
          exact congrArg Prod.snd hzeq
        rw [← hsbeq, ← hmb, hzb]
      · intro sb
        have hvis_nn : ((ProbStep.forgetMBO step).belief A.inputDomain
            (init.map fun s => (s, false)).1 h).NonNeg := fun a =>
          (hbelief_nn h a).trans (ih.2 a)
        calc step.transition _ ⟨o, u⟩ (tagMBO false ⟨o', v⟩) sb
            ≤ step.transition ((ProbStep.forgetMBO step).belief A.inputDomain
                (init.map fun s => (s, false)).1 h) ⟨o, u⟩ (tagMBO false ⟨o', v⟩) sb :=
              hmono_trans _ _ ih.2 ⟨o, u⟩ (tagMBO false ⟨o', v⟩) sb
          _ ≤ (step.transition ((ProbStep.forgetMBO step).belief A.inputDomain
                (init.map fun s => (s, false)).1 h) ⟨o, u⟩ (tagMBO false ⟨o', v⟩) +
              step.transition ((ProbStep.forgetMBO step).belief A.inputDomain
                (init.map fun s => (s, false)).1 h) ⟨o, u⟩ (tagMBO true ⟨o', v⟩)) sb := by
              rw [Finsupp.add_apply]
              linarith [hnonneg_trans _ hvis_nn ⟨o, u⟩ (tagMBO true ⟨o', v⟩) sb]
          _ = (ProbStep.forgetMBO step).transition ((ProbStep.forgetMBO step).belief A.inputDomain
                (init.map fun s => (s, false)).1 h) ⟨o, u⟩ ⟨o', v⟩ sb := by
              rw [transition_tagMBO_add]
    · rw [ite_eq_right (mt hadm_iff.mp hadm), ite_eq_right hadm]
      exact ⟨fun _ h => False.elim (Finset.notMem_empty _ h), fun _ => le_rfl⟩

omit [Fintype M] [DecidableEq M] in
/-- For `TypedGame.ofProbAutomaton`, the one-step MBO-set mass equals the expectation under
the unset-MBO belief of the per-state probability that the next step emits MBO bit `true`. -/
lemma ofProbAutomatonGame_sum_tagMBO_true {A : Interface} {S : Type}
    (step : ProbStep (S × Bool) A.I A.X (withMBO A.Y)) (init : ProbDist S)
    (hflag : ∀ (s : S) (b : Bool) (i : A.I) (x : A.X i)
      (q : (S × Bool) × (A.Y i × Bool)),
      q ∈ (step (s, b) i x).1.support → q.2.2 = q.1.2 ∧ (b = true → q.1.2 = true))
    (h : List ((Σ i, A.X i) × Σ i, A.Y i)) (xq : Σ i, A.X i)
    (hadm : A.inputDomain h xq) :
    ∑ y : Σ i, A.Y i,
        (TypedGame.ofProbAutomaton step init hflag).1.1 (unsetMBOs h ++ [(xq, tagMBO true y)]) =
      (step.belief A.withMBO.inputDomain (init.map fun s => (s, false)).1 (unsetMBOs h)).sum
        fun sb w => w * (step sb xq.1 xq.2).1.mass (fun q => q.2.2 = true) := by
  classical
  rcases xq with ⟨o, u⟩
  have hadm' : A.withMBO.inputDomain (unsetMBOs h) ⟨o, u⟩ := by
    change A.domain ((unsetMBOs h).map Prod.fst ++ [⟨o, u⟩])
    have hfst : (unsetMBOs h).map Prod.fst = h.map Prod.fst := by
      simp only [unsetMBOs, List.map_map, Function.comp_def]
    rw [hfst]; exact hadm
  set μ := step.belief A.withMBO.inputDomain (init.map fun s => (s, false)).1 (unsetMBOs h)
  have hterm : ∀ y : Σ i, A.Y i,
      (TypedGame.ofProbAutomaton step init hflag).1.1 (unsetMBOs h ++ [(⟨o, u⟩, tagMBO true y)]) =
        μ.sum fun sb w => w * (step sb o u).1.mass
          (fun q => (⟨o, q.2⟩ : Σ i, withMBO A.Y i) = tagMBO true y) := by
    intro y
    change (step.belief A.withMBO.inputDomain (init.map fun s => (s, false)).1
        (unsetMBOs h ++ [(⟨o, u⟩, tagMBO true y)])).weight = _
    rw [ProbStep.belief_snoc, ite_eq_left hadm']
    simp only [ProbStep.transition, ProbStep.outcome]
    rw [Distribution.weight_bindK]
    apply Finsupp.sum_congr
    intro sb _
    congr 1
    rw [Distribution.weight_fTransform, Distribution.weight_restrict, Distribution.mass_fTransform]
    rfl
  simp_rw [hterm, Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sb _
  rw [← Finset.mul_sum]
  congr 1
  have hfib : ∑ y : Σ i, A.Y i, (step sb o u).1.mass
      (fun q => (⟨o, q.2⟩ : Σ i, withMBO A.Y i) = tagMBO true y) =
      (step sb o u).1.mass (fun q => q.2.2 = true) := by
    have hmass_eq : ∀ y : Σ i, A.Y i,
        (step sb o u).1.mass (fun q => (⟨o, q.2⟩ : Σ i, withMBO A.Y i) = tagMBO true y) =
          ∑ q ∈ (step sb o u).1.support,
            if (⟨o, q.2⟩ : Σ i, withMBO A.Y i) = tagMBO true y then (step sb o u).1 q else 0 := by
      intro y
      rw [Distribution.mass_eq_sum_of_support_subset _ Finset.Subset.rfl, Finset.sum_filter]
    simp_rw [hmass_eq]
    rw [Finset.sum_comm, Distribution.mass_eq_sum_of_support_subset _ Finset.Subset.rfl,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hqt : q.2.2 = true
    · rw [ite_eq_left hqt]
      rw [Finset.sum_eq_single (⟨o, q.2.1⟩ : Σ i, A.Y i)]
      · have hEq : (⟨o, q.2⟩ : Σ i, withMBO A.Y i) = tagMBO true ⟨o, q.2.1⟩ := by
          simp only [tagMBO, Sigma.mk.inj_iff, heq_eq_eq, true_and]
          exact Prod.ext rfl hqt
        rw [ite_eq_left hEq]
      · intro y _ hne
        have hneq : (⟨o, q.2⟩ : Σ i, withMBO A.Y i) ≠ tagMBO true y := by
          intro hEq
          apply hne
          rcases y with ⟨i, v⟩
          have hi : o = i := congrArg Sigma.fst hEq
          subst hi
          simp only [tagMBO, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hEq
          exact Sigma.ext rfl (heq_of_eq (congrArg Prod.fst hEq).symm)
        rw [ite_eq_right hneq]
      · intro habs; exact False.elim (habs (Finset.mem_univ _))
    · rw [ite_eq_right hqt]
      apply Finset.sum_eq_zero
      intro y _
      have hneq : (⟨o, q.2⟩ : Σ i, withMBO A.Y i) ≠ tagMBO true y := by
        intro hEq
        apply hqt
        rcases y with ⟨i, v⟩
        have hi : o = i := congrArg Sigma.fst hEq
        subst hi
        simp only [tagMBO, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hEq
        exact congrArg Prod.snd hEq
      rw [ite_eq_right hneq]
  exact hfib

omit [DecidableEq M] in
/-- Dropping the state bit from the visible ideal game yields `idealPathVisStep`. -/
lemma forgetMBOStep_idealSpongeGameStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (s : (M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes) × ByteState p.stateBytes))
    (b : Bool) (i : (spec.toInterface ⊗ PrimitiveInterface p q_pub).I)
    (x : (spec.toInterface ⊗ PrimitiveInterface p q_pub).X i) :
    ((ProbStep.forgetMBO (idealSpongeGameStep p M spec q_pub)) (s, b) i x).map
        (fun q => (q.1.1, q.2)) =
      idealPathVisStep p M spec q_pub s i x := by
  rcases s with ⟨ro, T_pub, hid⟩
  rcases i with i | i
  · cases i
    simp only [ProbStep.forgetMBO, idealSpongeGameStep, idealPathVisStep, ProbDist.map_map]
    change ProbDist.map ((fun hid' => ((ro, T_pub, hid'), ro x)) ∘ Prod.fst) _ = _
    rw [← ProbDist.map_map, sampleHiddenPrefixesWithBad_map_fst, ProbDist.map_map]
    rfl
  · cases i with
    | forward =>
      simp only [ProbStep.forgetMBO, idealSpongeGameStep, idealPathVisStep]
      cases lookupForwardEdge T_pub x with
      | some y =>
        apply Subtype.ext
        simp only [ProbDist.map_val, ProbDist.single, fTransform_single]
      | none =>
        cases rootedPrefix p M encode T_pub x with
        | some bs =>
          by_cases hmem : bs ∈ hid.map Prod.fst
          · simp only [hmem, ↓reduceIte]
            apply Subtype.ext
            simp only [ProbDist.map_val, ProbDist.single, fTransform_single]
          · simp only [hmem, ↓reduceIte]
            cases completingMessage p encode T_pub x with
            | some m => simp only [ProbDist.map_map]; rfl
            | none => simp only [ProbDist.map_map]; rfl
        | none =>
          cases completingMessage p encode T_pub x with
          | some m => simp only [ProbDist.map_map]; rfl
          | none => simp only [ProbDist.map_map]; rfl
    | inverse =>
      simp only [ProbStep.forgetMBO, idealSpongeGameStep, idealPathVisStep]
      cases lookupInverseEdge T_pub x with
      | some x' =>
        apply Subtype.ext
        simp only [ProbDist.map_val, ProbDist.single, fTransform_single]
      | none =>
        simp only [ProbDist.map_map]; rfl

open Classical in
/-- Exact simultaneous belief coupling for `idealGhostStep`, `idealSpongeGame.visible`, and the
lifted `idealFixedROStep` automaton at every visible transcript `h`. -/
lemma idealGhost_belief_rel (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o))) :
    let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
    let initG : ProbDist ((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes))) :=
      (𝒰[M → ByteState p.outputBytes]).map fun ro => (ro, [], [])
    let stepI : ProbStep ((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes))) A.I A.X A.Y :=
      fun ps o u => (idealFixedROStep p M spec q_pub ps.1 ps.2 o u).map
        fun sy => ((ps.1, sy.1), sy.2)
    let initI : ProbDist ((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes))) :=
      (𝒰[M → ByteState p.outputBytes]).bind fun ro =>
        (ProbDist.single ([] : List (PermutationEdge (ByteState p.stateBytes)))).map
          fun s => (ro, s)
    let μ_g := (idealGhostStep p M spec q_pub).belief A.inputDomain initG.1 h
    let μ_v := (ProbStep.forgetMBO (idealSpongeGameStep p M spec q_pub)).belief A.inputDomain
      ((idealGameInit p M).map fun s => (s, false)).1 h
    let μ_i := stepI.belief A.inputDomain initI.1 h
    let (T_pub, keys, _) := replayGhost p M spec q_pub h
    (∀ st ∈ μ_g.support, st.2.1 = T_pub ∧ st.2.2 = keys ∧ st.2.2.Nodup) ∧
    (μ_g.bindK (fun st =>
      ((sampleHiddenList p M encode st.1 st.2.2).map fun hid => (st.1, st.2.1, hid)).1) =
        fTransform Prod.fst μ_v) ∧
    (fTransform (fun st => (st.1, st.2.1)) μ_g = μ_i) := by
  dsimp only
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  let initG : ProbDist ((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes))) :=
    (𝒰[M → ByteState p.outputBytes]).map fun ro => (ro, [], [])
  let stepI : ProbStep ((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes))) A.I A.X A.Y :=
    fun ps o u => (idealFixedROStep p M spec q_pub ps.1 ps.2 o u).map
      fun sy => ((ps.1, sy.1), sy.2)
  let initI : ProbDist ((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes))) :=
    (𝒰[M → ByteState p.outputBytes]).bind fun ro =>
      (ProbDist.single ([] : List (PermutationEdge (ByteState p.stateBytes)))).map
        fun s => (ro, s)
  let K_hid : ((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes))) →
      Distribution ((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes)) ×
        List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) :=
    fun st => ((sampleHiddenList p M encode st.1 st.2.2).map fun hid => (st.1, st.2.1, hid)).1
  have hproj_vis : ∀ (μ : Distribution (((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) × Bool))
      (xq : Σ o, A.X o) (yq : Σ o, A.Y o),
      fTransform Prod.fst
        ((ProbStep.forgetMBO (idealSpongeGameStep p M spec q_pub)).transition μ xq yq)
        =
        (idealPathVisStep p M spec q_pub).transition (fTransform Prod.fst μ) xq yq := by
    intro μ ⟨o, u⟩ yq
    simp only [ProbStep.transition, ProbStep.outcome]
    rw [fTransform_bindK, bindK_fTransform]
    apply bindK_congr
    intro ⟨s, b⟩ _
    dsimp only [Function.comp_def]
    have hstep := congrArg Subtype.val (forgetMBOStep_idealSpongeGameStep p M spec q_pub s b o u)
    rw [ProbDist.map_val] at hstep
    rw [← hstep, Distribution.restrict_fTransform, fTransform_fTransform, fTransform_fTransform]
    rw [Distribution.restrict_fTransform, fTransform_fTransform]
    rw [Distribution.restrict_fTransform, fTransform_fTransform]
    rfl
  induction h using List.reverseRecOn with
  | nil =>
    simp only [replayGhost_nil, ProbStep.belief, ProbStep.beliefRev, List.reverse_nil]
    refine ⟨?_, ?_, ?_⟩
    · intro st hst
      rw [ProbDist.map_val, Finsupp.mem_support_iff] at hst
      have hex : ∃ ro ∈ (𝒰[M → ByteState p.outputBytes]).1.support, (ro, [], []) = st := by
        by_contra hall; push Not at hall; apply hst
        change ((𝒰[M → ByteState p.outputBytes]).1.sum fun a w =>
          Finsupp.single (a, [], []) w) st = 0
        rw [Finsupp.sum_apply]; simp only [Finsupp.sum]
        exact Finset.sum_eq_zero fun a ha => Finsupp.single_eq_of_ne (hall a ha).symm
      rcases hex with ⟨ro, _, rfl⟩
      exact ⟨rfl, rfl, List.nodup_nil⟩
    · change initG.1.bindK K_hid =
        fTransform Prod.fst ((idealGameInit p M).map fun s => (s, false)).1
      simp only [initG, idealGameInit, K_hid, sampleHiddenList, ProbDist.map_val,
        bindK_fTransform, fTransform_fTransform, ProbDist.single, fTransform_single,
        Function.comp_def]
      change ((𝒰[M → ByteState p.outputBytes]).1.sum fun ro w =>
        w • Finsupp.single (ro, [], []) (1 : ℝ)) =
        ((𝒰[M → ByteState p.outputBytes]).1.sum fun ro w =>
          Finsupp.single (ro, [], []) w)
      apply Finsupp.sum_congr
      intro ro _
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    · simp only [ProbDist.map_val, ProbDist.bind_val, ProbDist.single, fTransform_single,
        fTransform_fTransform]
      change ((𝒰[M → ByteState p.outputBytes]).1.sum fun ro w =>
        Finsupp.single (ro, []) w) =
        ((𝒰[M → ByteState p.outputBytes]).1.sum fun ro w =>
          w • Finsupp.single (ro, []) (1 : ℝ))
      apply Finsupp.sum_congr
      intro ro _
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  | append_singleton h z ih =>
    rcases z with ⟨xq, yq⟩
    rw [replayGhost_snoc]
    rcases hrg : replayGhost p M spec q_pub h with ⟨T_pub, keys, a_cnt⟩
    rw [hrg] at ih
    rcases ih with ⟨hsupp, hvis, hfix⟩
    rw [ProbStep.belief_snoc, ProbStep.belief_snoc, ProbStep.belief_snoc]
    by_cases hadm : A.inputDomain h xq
    · rw [ite_eq_left hadm, ite_eq_left hadm, ite_eq_left hadm]
      set μ_g := (idealGhostStep p M spec q_pub).belief A.inputDomain initG.1 h
      set μ_v := (ProbStep.forgetMBO (idealSpongeGameStep p M spec q_pub)).belief A.inputDomain
        ((idealGameInit p M).map fun s => (s, false)).1 h
      set μ_i := stepI.belief A.inputDomain initI.1 h
      rcases xq with ⟨o, u⟩; rcases yq with ⟨o', v⟩
      by_cases ho : o = o'
      · subst ho
        have hstep_rel : ∀ ro : M → ByteState p.outputBytes, keys.Nodup →
            (∀ st' ∈ (fTransform Prod.fst
                ((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩)).support,
              st'.2.1 = (ghostStep p M spec q_pub (T_pub, keys, a_cnt) ⟨o, u⟩ ⟨o, v⟩).1 ∧
              st'.2.2 = (ghostStep p M spec q_pub (T_pub, keys, a_cnt) ⟨o, u⟩ ⟨o, v⟩).2.1 ∧
              st'.2.2.Nodup) ∧
            ((fTransform Prod.fst
                ((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩)).bindK K_hid =
              (K_hid (ro, T_pub, keys)).bindK fun s_v =>
                fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealPathVisStep p M spec q_pub s_v o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩)) ∧
            (fTransform (fun st => (st.1, st.2.1))
                (fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩)) =
              fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩)
                (stepI (ro, T_pub) o u).1).restrict fun sy => sy.2 = ⟨o, v⟩)) := by
          intro ro hnd
          have hlift : ∀ {S₁ S₂ : Type} (μ₁ : ProbDist (S₁ × A.Y o)) (μ₂ : ProbDist (S₂ × A.Y o))
              (f : S₁ → Distribution S₂),
              (fTransform (ProbStep.tagged ⟨o, u⟩) μ₁.1).bindK
                (fun sy => fTransform (fun s₂ => (s₂, sy.2)) (f sy.1)) =
                fTransform (ProbStep.tagged ⟨o, u⟩) μ₂.1 →
              (fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩) μ₁.1).restrict
                  fun sy => sy.2 = ⟨o, v⟩)).bindK f =
                fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩) μ₂.1).restrict
                  fun sy => sy.2 = ⟨o, v⟩) := by
            intro S₁ S₂ μ₁ μ₂ f hEq
            rw [← hEq, bindK_fTransform]
            have hcomm :
                ((fTransform (ProbStep.tagged ⟨o, u⟩) μ₁.1).bindK fun sy =>
                  fTransform (fun s₂ => (s₂, sy.2)) (f sy.1)).restrict (fun sy => sy.2 = ⟨o, v⟩) =
                ((fTransform (ProbStep.tagged ⟨o, u⟩) μ₁.1).restrict
                  fun sy => sy.2 = ⟨o, v⟩).bindK fun sy =>
                    fTransform (fun s₂ => (s₂, sy.2)) (f sy.1) := by
              rw [Distribution.restrict_bindK]
              ext ⟨s₂, y⟩
              rw [bindK_apply, bindK_apply]
              simp only [Finsupp.sum]
              have hsub : ((fTransform (ProbStep.tagged ⟨o, u⟩) μ₁.1).restrict
                  fun sy => sy.2 = ⟨o, v⟩).support ⊆
                  (fTransform (ProbStep.tagged ⟨o, u⟩) μ₁.1).support := by
                intro sy hsy
                rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply] at hsy
                split_ifs at hsy
                · exact Finsupp.mem_support_iff.mpr hsy
                · exact False.elim (hsy rfl)
              rw [← Finset.sum_subset hsub]
              · apply Finset.sum_congr rfl
                intro sy hsy
                by_cases hy : sy.2 = ⟨o, v⟩
                · conv_rhs =>
                    rw [Distribution.restrict, Finsupp.filter_apply, ite_eq_left hy]
                  congr 1
                  rw [Distribution.restrict_fTransform]
                  have htr : ∀ a : S₂, ((a, sy.2).2 = (⟨o, v⟩ : Σ i, A.Y i)) ↔ True := fun _ =>
                    iff_true_intro hy
                  rw [Distribution.restrict_congr _ htr]
                  have hrt : (f sy.1).restrict (fun _ => True) = f sy.1 := by
                    ext a; rw [Distribution.restrict, Finsupp.filter_apply, ite_eq_left trivial]
                  rw [hrt]
                · conv_rhs =>
                    rw [Distribution.restrict, Finsupp.filter_apply, ite_eq_right hy, zero_mul]
                  rw [Distribution.restrict_fTransform]
                  have hfl : ∀ a : S₂, ((a, sy.2).2 = (⟨o, v⟩ : Σ i, A.Y i)) ↔ False := fun _ =>
                    iff_false_intro hy
                  rw [Distribution.restrict_congr _ hfl, Distribution.restrict_false,
                    fTransform_zero, Finsupp.zero_apply, mul_zero]
              · intro sy hsy hnot
                have hneg : sy.2 ≠ ⟨o, v⟩ := by
                  intro hy
                  apply hnot
                  rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply,
                    ite_eq_left hy]
                  exact Finsupp.mem_support_iff.mp hsy
                rw [Distribution.restrict_fTransform]
                have hfl : ∀ a : S₂, ((a, sy.2).2 = (⟨o, v⟩ : Σ i, A.Y i)) ↔ False := fun _ =>
                  iff_false_intro hneg
                rw [Distribution.restrict_congr _ hfl, Distribution.restrict_false,
                  fTransform_zero, Finsupp.zero_apply, mul_zero]
            rw [hcomm, fTransform_bindK]
            apply bindK_congr
            intro sy _
            rw [fTransform_fTransform]
            exact (fTransform_id (f sy.1)).symm
          have hlift_det : ∀ {S₁ S₂ : Type} (μ₁ : ProbDist (S₁ × A.Y o)) (μ₂ : ProbDist (S₂ × A.Y
            o))
              (g : S₁ → S₂),
              μ₁.map (fun sy => (g sy.1, sy.2)) = μ₂ →
              fTransform g (fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩) μ₁.1).restrict
                  fun sy => sy.2 = ⟨o, v⟩)) =
                fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩) μ₂.1).restrict
                  fun sy => sy.2 = ⟨o, v⟩) := by
            intro S₁ S₂ μ₁ μ₂ g hEq
            have hval := congrArg Subtype.val hEq
            rw [ProbDist.map_val] at hval
            rw [← hval, fTransform_fTransform, Distribution.restrict_fTransform,
              Distribution.restrict_fTransform, fTransform_fTransform, fTransform_fTransform]
            rw [Distribution.restrict_fTransform, fTransform_fTransform]
            rfl
          have hstep_i :
              (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u).map
                (fun sy => ((sy.1.1, sy.1.2.1), sy.2)) = stepI (ro, T_pub) o u := by
            rcases o with o | o
            · cases o
              apply Subtype.ext
              simp only [idealGhostStep, stepI, idealFixedROStep, parallelFnProbStep,
                ProbDist.map_val, ProbDist.single, fTransform_single]
            · cases o with
              | forward =>
                simp only [idealGhostStep, stepI, idealFixedROStep, parallelFnProbStep,
                  simFixedROStep]
                cases lookupForwardEdge T_pub u with
                | some y =>
                  apply Subtype.ext
                  simp only [ProbDist.map_val, ProbDist.single, fTransform_single]
                | none =>
                  cases completingMessage p encode T_pub u with
                  | some m => simp only [ProbDist.map_map]; rfl
                  | none => simp only [ProbDist.map_map]; rfl
              | inverse =>
                simp only [idealGhostStep, stepI, idealFixedROStep, parallelFnProbStep,
                  simFixedROStep]
                cases lookupInverseEdge T_pub u with
                | some x =>
                  apply Subtype.ext
                  simp only [ProbDist.map_val, ProbDist.single, fTransform_single]
                | none => simp only [ProbDist.map_map]; rfl
          have h3 := hlift_det (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u)
            (stepI (ro, T_pub) o u) (fun st => (st.1, st.2.1)) hstep_i
          have h2_eq :
              ((idealGhostStep p M spec q_pub (ro, T_pub, keys) o u).bind fun sy =>
                  (sampleHiddenList p M encode sy.1.1 sy.1.2.2).map fun hid =>
                    ((sy.1.1, sy.1.2.1, hid), sy.2)) =
                (sampleHiddenList p M encode ro keys).bind fun hid =>
                  idealPathVisStep p M spec q_pub (ro, T_pub, hid) o u := by
            rcases o with o | o
            · cases o
              dsimp only [idealGhostStep, idealPathVisStep]
              rw [probDist_single_bind]
              have hcongr : (sampleHiddenList p M encode ro keys).bind (fun hid =>
                  (sampleHiddenList p M encode ro (newHiddenPrefixes p T_pub (hid.map Prod.fst)
                    (paddedBlocks p (encode u)))).map fun ext =>
                    ((ro, T_pub, hid ++ ext), ro u)) =
                (sampleHiddenList p M encode ro keys).bind (fun hid =>
                  (sampleHiddenList p M encode ro (newHiddenPrefixes p T_pub keys
                    (paddedBlocks p (encode u)))).map fun ext =>
                    ((ro, T_pub, hid ++ ext), ro u)) := by
                apply Subtype.ext
                simp only [ProbDist.bind_val]
                apply bindK_congr
                intro hid hhid
                rw [sampleHiddenList_keys p M encode ro keys hid hhid]
              rw [hcongr, sampleHiddenList_append, probDist_map_bind]
              apply congrArg (ProbDist.bind _)
              funext hid
              rw [ProbDist.map_map]
              rfl
            · cases o with
              | forward =>
                dsimp only [idealGhostStep, idealPathVisStep]
                cases hlu : lookupForwardEdge T_pub u with
                | some y =>
                  rw [probDist_single_bind]
                  apply Subtype.ext
                  simp only [ProbDist.map_val, ProbDist.bind_val, ProbDist.single]
                  change ((sampleHiddenList p M encode ro keys).1.sum fun hid w =>
                      Finsupp.single ((ro, T_pub, hid), y) w) =
                    (sampleHiddenList p M encode ro keys).1.sum fun hid w =>
                      w • Finsupp.single ((ro, T_pub, hid), y) (1 : ℝ)
                  apply Finsupp.sum_congr
                  intro hid _
                  rw [Finsupp.smul_single, smul_eq_mul, mul_one]
                | none =>
                  cases hrp : rootedPrefix p M encode T_pub u with
                  | some bs =>
                    by_cases hmem : bs ∈ keys
                    · simp only [hmem, ↓reduceIte]
                      have hcongr :
                          (sampleHiddenList p M encode ro keys).bind (fun hid =>
                            if bs ∈ hid.map Prod.fst then
                              let z := (hid.lookup bs).getD (zeroState p.stateBytes)
                              ProbDist.single ((ro, recordForwardEdge T_pub u z,
                                eraseHiddenKey p hid bs), z)
                            else
                              match completingMessage p encode T_pub u with
                              | some m => (𝒰[ByteState (tailBytes p)]).map fun t =>
                                  let y := assembleState p (ro m) t
                                  ((ro, recordForwardEdge T_pub u y, hid), y)
                              | none => (𝒰[ByteState p.stateBytes]).map fun y =>
                                  ((ro, recordForwardEdge T_pub u y, hid), y)) =
                          (sampleHiddenList p M encode ro keys).map fun hid =>
                            let z := (hid.lookup bs).getD (zeroState p.stateBytes)
                            ((ro, recordForwardEdge T_pub u z, eraseHiddenKey p hid bs), z) := by
                        rw [probDist_map_eq_bind]
                        apply Subtype.ext
                        simp only [ProbDist.bind_val]
                        apply bindK_congr
                        intro hid hhid
                        rw [sampleHiddenList_keys p M encode ro keys hid hhid,
                          ite_eq_left hmem]
                      refine Eq.trans ?_ hcongr.symm
                      have hpop := congrArg (ProbDist.map fun p' =>
                        ((ro, recordForwardEdge T_pub u p'.2, p'.1), p'.2))
                        (sampleHiddenList_pop p M encode ro keys hnd bs hmem)
                      rw [ProbDist.map_map, probDist_map_bind] at hpop
                      change _ = (sampleHiddenList p M encode ro keys).map _
                      rw [show (fun hid =>
                            ((ro, recordForwardEdge T_pub u
                              ((hid.lookup bs).getD (zeroState p.stateBytes)),
                              eraseHiddenKey p hid bs),
                              (hid.lookup bs).getD (zeroState p.stateBytes))) =
                          (fun p' => ((ro, recordForwardEdge T_pub u p'.2, p'.1), p'.2)) ∘
                            (fun hid => (eraseHiddenKey p hid bs,
                              (hid.lookup bs).getD (zeroState p.stateBytes))) from rfl]
                      rw [hpop]
                      cases hcm : completingMessage p encode T_pub u with
                      | some m =>
                        have hbs_eq : bs = paddedBlocks p (encode m) := by
                          unfold rootedPrefix at hrp
                          rw [hcm] at hrp
                          exact (Option.some.inj hrp).symm
                        rw [hbs_eq, nodeLaw_paddedBlocks p M hp encode henc ro m,
                          probDist_bind_map, probDist_bind_map]
                        apply congrArg (ProbDist.bind _)
                        funext t
                        rw [ProbDist.map_map]
                        rfl
                      | none =>
                        rw [nodeLaw_rootedPrefix_of_completingMessage_none p M encode ro T_pub u
                          bs hcm hrp, probDist_bind_map]
                        apply congrArg (ProbDist.bind _)
                        funext y
                        rw [ProbDist.map_map]
                        rfl
                    · simp only [hmem, ↓reduceIte]
                      have hcongr :
                          (sampleHiddenList p M encode ro keys).bind (fun hid =>
                            if bs ∈ hid.map Prod.fst then
                              let z := (hid.lookup bs).getD (zeroState p.stateBytes)
                              ProbDist.single ((ro, recordForwardEdge T_pub u z,
                                eraseHiddenKey p hid bs), z)
                            else
                              match completingMessage p encode T_pub u with
                              | some m => (𝒰[ByteState (tailBytes p)]).map fun t =>
                                  let y := assembleState p (ro m) t
                                  ((ro, recordForwardEdge T_pub u y, hid), y)
                              | none => (𝒰[ByteState p.stateBytes]).map fun y =>
                                  ((ro, recordForwardEdge T_pub u y, hid), y)) =
                          (sampleHiddenList p M encode ro keys).bind fun hid =>
                            match completingMessage p encode T_pub u with
                            | some m => (𝒰[ByteState (tailBytes p)]).map fun t =>
                                let y := assembleState p (ro m) t
                                ((ro, recordForwardEdge T_pub u y, hid), y)
                            | none => (𝒰[ByteState p.stateBytes]).map fun y =>
                                ((ro, recordForwardEdge T_pub u y, hid), y) := by
                        apply Subtype.ext
                        simp only [ProbDist.bind_val]
                        apply bindK_congr
                        intro hid hhid
                        rw [sampleHiddenList_keys p M encode ro keys hid hhid,
                          ite_eq_right hmem]
                      refine Eq.trans ?_ hcongr.symm
                      cases completingMessage p encode T_pub u with
                      | some m =>
                        rw [probDist_bind_map]
                        simp_rw [probDist_map_eq_bind]
                        exact probDist_bind_comm _ _ _
                      | none =>
                        rw [probDist_bind_map]
                        simp_rw [probDist_map_eq_bind]
                        exact probDist_bind_comm _ _ _
                  | none =>
                    cases completingMessage p encode T_pub u with
                    | some m =>
                      rw [probDist_bind_map]
                      simp_rw [probDist_map_eq_bind]
                      exact probDist_bind_comm _ _ _
                    | none =>
                      rw [probDist_bind_map]
                      simp_rw [probDist_map_eq_bind]
                      exact probDist_bind_comm _ _ _
              | inverse =>
                dsimp only [idealGhostStep, idealPathVisStep]
                cases lookupInverseEdge T_pub u with
                | some x =>
                  rw [probDist_single_bind, probDist_map_eq_bind]
                | none =>
                  rw [probDist_bind_map]
                  simp_rw [probDist_map_eq_bind]
                  exact probDist_bind_comm _ _ _
          have h2 :
              (fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩)).bindK K_hid =
                (K_hid (ro, T_pub, keys)).bindK fun s_v =>
                  fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩)
                    (idealPathVisStep p M spec q_pub s_v o u).1).restrict
                      fun sy => sy.2 = ⟨o, v⟩) := by
            have h2' := hlift (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u)
              ((sampleHiddenList p M encode ro keys).bind fun hid =>
                idealPathVisStep p M spec q_pub (ro, T_pub, hid) o u) K_hid (by
                have hv := congrArg Subtype.val h2_eq
                simp only [ProbDist.bind_val, ProbDist.map_val] at hv
                rw [bindK_fTransform (ProbStep.tagged ⟨o, u⟩) _ _, ProbDist.bind_val, ← hv,
                  fTransform_bindK]
                apply bindK_congr
                intro sy _
                simp only [Function.comp_def, K_hid, ProbDist.map_val, ProbStep.tagged,
                  fTransform_fTransform])
            rw [h2']
            simp only [K_hid, ProbDist.map_val, bindK_fTransform, ProbDist.bind_val,
              fTransform_bindK, Distribution.restrict_bindK, Function.comp_def]
            rfl
          have h1 : ∀ st' ∈ (fTransform Prod.fst
              ((fTransform (ProbStep.tagged ⟨o, u⟩)
                (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u).1).restrict
                  fun sy => sy.2 = ⟨o, v⟩)).support,
              st'.2.1 = (ghostStep p M spec q_pub (T_pub, keys, a_cnt) ⟨o, u⟩ ⟨o, v⟩).1 ∧
              st'.2.2 = (ghostStep p M spec q_pub (T_pub, keys, a_cnt) ⟨o, u⟩ ⟨o, v⟩).2.1 ∧
              st'.2.2.Nodup := by
            intro st' hst'
            obtain ⟨sy, hsy, hfst_eq⟩ := mem_support_fTransform _ _ hst'
            have hsy' : sy ∈ (fTransform (ProbStep.tagged ⟨o, u⟩)
                (idealGhostStep p M spec q_pub (ro, T_pub, keys) o u).1).support ∧
                sy.2 = ⟨o, v⟩ := by
              rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply] at hsy
              split_ifs at hsy with hcond
              · exact ⟨Finsupp.mem_support_iff.mpr hsy, hcond⟩
              · exact False.elim (hsy rfl)
            obtain ⟨⟨st_raw, y_raw⟩, hraw, htag_eq⟩ := mem_support_fTransform _ _ hsy'.1
            have hst_eq : st_raw = st' := by
              rw [← hfst_eq, ← htag_eq]; rfl
            subst hst_eq
            have hy_eq : y_raw = v := by
              have h2 := hsy'.2
              rw [← htag_eq] at h2
              simp only [ProbStep.tagged, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h2
              exact h2
            subst hy_eq
            have hmap_s : ∀ {α β : Type} (μ : ProbDist α) (f : α → β) (y : β),
                y ∈ (μ.map f).1.support → ∃ a ∈ μ.1.support, f a = y := by
              intro α β μ f y hy
              obtain ⟨a, ha, hfa⟩ := mem_support_fTransform f μ.1 hy
              exact ⟨a, ha, hfa⟩
            have hsing_s : ∀ {α : Type} (a y : α),
                y ∈ (ProbDist.single a).1.support → y = a := by
              intro α a y hy
              change y ∈ (Finsupp.single a (1 : ℝ)).support at hy
              rw [Finsupp.mem_support_iff] at hy
              by_contra hne; exact hy (Finsupp.single_eq_of_ne hne)
            rcases o with o | o
            · cases o
              dsimp only [idealGhostStep, ghostStep] at hraw ⊢
              rcases hsing_s _ _ hraw with hEq
              have hs := congrArg Prod.fst hEq
              dsimp only at hs
              rw [hs]
              exact ⟨rfl, rfl, keys_append_newHiddenPrefixes_nodup p T_pub keys hnd _⟩
            · cases o with
              | forward =>
                dsimp only [idealGhostStep, ghostStep] at hraw ⊢
                cases hlu : lookupForwardEdge T_pub u with
                | some y =>
                  rw [hlu] at hraw
                  dsimp only at hraw ⊢
                  rcases hsing_s _ _ hraw with hEq
                  have hs := congrArg Prod.fst hEq
                  dsimp only at hs
                  rw [hs]
                  exact ⟨rfl, rfl, hnd⟩
                | none =>
                  rw [hlu] at hraw
                  dsimp only at hraw ⊢
                  have hnd' : (match rootedPrefix p M encode T_pub u with
                      | some bs => if bs ∈ keys then keys.erase bs else keys
                      | none => keys).Nodup := by
                    cases rootedPrefix p M encode T_pub u with
                    | none => exact hnd
                    | some bs => dsimp only; split_ifs <;> [exact hnd.erase _; exact hnd]
                  cases hcm : completingMessage p encode T_pub u with
                  | some m =>
                    rw [hcm] at hraw
                    dsimp only at hraw
                    rcases hmap_s _ _ _ hraw with ⟨t, _, hEq⟩
                    have hs := congrArg Prod.fst hEq
                    have hy := congrArg Prod.snd hEq
                    dsimp only at hs hy
                    rw [← hs, ← hy]
                    exact ⟨rfl, rfl, hnd'⟩
                  | none =>
                    rw [hcm] at hraw
                    dsimp only at hraw
                    rcases hmap_s _ _ _ hraw with ⟨y, _, hEq⟩
                    have hs := congrArg Prod.fst hEq
                    have hy := congrArg Prod.snd hEq
                    dsimp only at hs hy
                    rw [← hs, ← hy]
                    exact ⟨rfl, rfl, hnd'⟩
              | inverse =>
                dsimp only [idealGhostStep, ghostStep] at hraw ⊢
                cases hlu : lookupInverseEdge T_pub u with
                | some x =>
                  rw [hlu] at hraw
                  dsimp only at hraw ⊢
                  rcases hsing_s _ _ hraw with hEq
                  have hs := congrArg Prod.fst hEq
                  dsimp only at hs
                  rw [hs]
                  exact ⟨rfl, rfl, hnd⟩
                | none =>
                  rw [hlu] at hraw
                  dsimp only at hraw ⊢
                  rcases hmap_s _ _ _ hraw with ⟨x, _, hEq⟩
                  have hs := congrArg Prod.fst hEq
                  have hy := congrArg Prod.snd hEq
                  dsimp only at hs hy
                  rw [← hs, ← hy]
                  exact ⟨rfl, rfl, hnd⟩
          exact ⟨h1, h2, h3⟩
        refine ⟨?_, ?_, ?_⟩
        · intro st' hst'
          obtain ⟨st, hst, hout⟩ := ProbStep.mem_support_transition (idealGhostStep p M spec q_pub)
            ⟨o, u⟩ ⟨o, v⟩ hst'
          rcases st with ⟨ro, T', k'⟩
          rcases hsupp (ro, T', k') hst with ⟨hTeq, hkeq, hnd⟩
          subst hTeq; subst hkeq
          have hmem' : st' ∈ (fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩)
              (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                fun sy => sy.2 = ⟨o, v⟩)).support := by
            have hst_mem : (st', (⟨o, v⟩ : Σ i, A.Y i)) ∈
                ((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩).support := by
              rw [Finsupp.mem_support_iff, Distribution.restrict, Finsupp.filter_apply,
                ite_eq_left rfl]
              exact Finsupp.mem_support_iff.mp hout
            rw [Finsupp.mem_support_iff]
            intro hzero
            have hge : ((fTransform (ProbStep.tagged ⟨o, u⟩)
                (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                  fun sy => sy.2 = ⟨o, v⟩) (st', ⟨o, v⟩) ≤
                (fTransform Prod.fst ((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩)) st' := by
              change _ ≤ (((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩).sum fun sy w => Finsupp.single sy.1 w) st'
              rw [Finsupp.sum_apply, Finsupp.sum]
              have hnn : ∀ sy ∈ ((fTransform (ProbStep.tagged ⟨o, u⟩)
                  (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                    fun sy => sy.2 = ⟨o, v⟩).support,
                  0 ≤ (Finsupp.single sy.1 (((fTransform (ProbStep.tagged ⟨o, u⟩)
                    (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                      fun sy => sy.2 = ⟨o, v⟩) sy)) st' := by
                intro sy _
                rw [Finsupp.single_apply]
                split_ifs
                · rw [Distribution.restrict, Finsupp.filter_apply]
                  split_ifs
                  · exact Distribution.NonNeg.fTransform
                      (idealGhostStep p M spec q_pub (ro, T', k') o u).2.1 _ sy
                  · exact le_rfl
                · exact le_rfl
              calc _ = (Finsupp.single (st', (⟨o, v⟩ : Σ i, A.Y i)).1
                    (((fTransform (ProbStep.tagged ⟨o, u⟩)
                      (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                        fun sy => sy.2 = ⟨o, v⟩) (st', ⟨o, v⟩))) st' := by
                      simp only [Finsupp.single_eq_same]
                _ ≤ _ := Finset.single_le_sum hnn hst_mem
            have hpos : 0 < ((fTransform (ProbStep.tagged ⟨o, u⟩)
                (idealGhostStep p M spec q_pub (ro, T', k') o u).1).restrict
                  fun sy => sy.2 = ⟨o, v⟩) (st', ⟨o, v⟩) :=
              lt_of_le_of_ne (by
                rw [Distribution.restrict, Finsupp.filter_apply]
                split_ifs
                · exact Distribution.NonNeg.fTransform
                    (idealGhostStep p M spec q_pub (ro, T', k') o u).2.1 _ _
                · exact le_rfl) (Ne.symm (Finsupp.mem_support_iff.mp hst_mem))
            linarith
          exact (hstep_rel ro hnd).1 st' hmem'
        · rw [hproj_vis, ← hvis]
          simp only [ProbStep.transition, ProbStep.outcome]
          rw [bindK_bindK, bindK_bindK]
          apply bindK_congr
          intro ⟨ro, T', k'⟩ hst
          rcases hsupp (ro, T', k') hst with ⟨rfl, rfl, hnd⟩
          exact (hstep_rel ro hnd).2.1
        · rw [← hfix]
          simp only [ProbStep.transition, ProbStep.outcome]
          rw [fTransform_bindK, bindK_fTransform]
          apply bindK_congr
          intro ⟨ro, T', k'⟩ hst
          rcases hsupp (ro, T', k') hst with ⟨rfl, rfl, hnd⟩
          exact (hstep_rel ro hnd).2.2
      · have hzero : ∀ {S : Type} (step : ProbStep S A.I A.X A.Y) (μ : Distribution S),
            step.transition μ ⟨o, u⟩ ⟨o', v⟩ = 0 := by
          intro S step μ
          simp only [ProbStep.transition, ProbStep.outcome]
          have hz : ∀ s : S, fTransform Prod.fst
              ((fTransform (ProbStep.tagged ⟨o, u⟩) (step s o u).1).restrict
                fun sy => sy.2 = ⟨o', v⟩) = 0 := by
            intro s
            rw [Distribution.restrict_fTransform]
            have hf : ∀ q : S × A.Y o,
                ((ProbStep.tagged ⟨o, u⟩ q).2 = (⟨o', v⟩ : Σ i, A.Y i)) ↔ False := fun q => by
              simp only [ProbStep.tagged, iff_false]
              intro hEq; exact ho (congrArg Sigma.fst hEq)
            rw [Distribution.restrict_congr _ hf, Distribution.restrict_false, fTransform_zero,
              fTransform_zero]
          have hfun : (fun s : S => fTransform Prod.fst
              ((fTransform (ProbStep.tagged ⟨o, u⟩) (step s o u).1).restrict
                fun sy => sy.2 = ⟨o', v⟩)) = fun _ => 0 := funext hz
          rw [hfun, bindK_zero_right]
        rw [hzero, hzero, hzero, bindK_zero, fTransform_zero, fTransform_zero]
        exact ⟨fun _ h => False.elim (Finset.notMem_empty _ h), rfl, rfl⟩
    · rw [ite_eq_right hadm, ite_eq_right hadm, ite_eq_right hadm, bindK_zero, fTransform_zero,
        fTransform_zero]
      exact ⟨fun _ h => False.elim (Finset.notMem_empty _ h), rfl, rfl⟩

/-- Hiding the MBO of `idealSpongeGame` recovers `(spec.toInterface ◁ spongeSimulator) •
sharedIdealRO`. -/
theorem idealSpongeGame_visible (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    (idealSpongeGame p M spec q_pub).visible =
      (spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub := by
  have hsam := sample_ofProbAutomaton_eq (A := spec.toInterface ⊗ PrimitiveInterface p q_pub)
    (μ := 𝒰[M → ByteState p.outputBytes]) (fun ro => idealFixedROStep p M spec q_pub ro)
    (fun _ => ProbDist.single [])
  rw [idealSpongeGame, TypedGame.visible_ofProbAutomaton, idealSponge_eq_sample p M hp spec q_pub]
  change _ = TypedSystem.sample (𝒰[M → ByteState p.outputBytes]).1 _
  rw [hsam]
  apply Subtype.ext
  apply Subtype.ext
  funext h
  have hrel := idealGhost_belief_rel p M hp henc spec q_pub h
  rcases hrg : replayGhost p M spec q_pub h with ⟨T_pub, keys, a_cnt⟩
  rw [hrg] at hrel
  rcases hrel with ⟨_, hvis, hfix⟩
  change ((ProbStep.forgetMBO (idealSpongeGameStep p M spec q_pub)).belief
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain
      ((idealGameInit p M).map fun s => (s, false)).1 h).weight = _
  rw [← Distribution.weight_fTransform Prod.fst, ← hvis, Distribution.weight_bindK]
  have hwt_one : ∀ st : (M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) × List (List (ByteState p.rateBytes)),
      (((sampleHiddenList p M encode st.1 st.2.2).map fun hid =>
        (st.1, st.2.1, hid)).1).weight = 1 := fun st =>
    ((sampleHiddenList p M encode st.1 st.2.2).map fun hid => (st.1, st.2.1, hid)).2.2
  simp_rw [hwt_one, mul_one]
  change ((idealGhostStep p M spec q_pub).belief _ _ h).weight = _
  rw [← Distribution.weight_fTransform (fun st => (st.1, st.2.1)), hfix]
  rfl

/-- Unfiltered one-step MBO-set domination bound on `idealSpongeGame`: at every visible transcript
`h` and admitted query `xq`, the unset-MBO probability lost at step `xq` is at most
`gameStepCost h xq * idealSpongeGame.visible h`. -/
theorem idealSpongeGame_loss_le_gameStepCost (hp : p.Valid) {encode : M → List (BitVec 8)}
    (henc : Function.Injective encode) {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (xq : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o)
    (hadm : (spec.toInterface ⊗ PrimitiveInterface p q_pub).inputDomain h xq) :
    (idealSpongeGame p M spec q_pub).1.1 (unsetMBOs h) -
        ∑ y, (idealSpongeGame p M spec q_pub).1.1 (unsetMBOs (h ++ [(xq, y)])) ≤
      gameStepCost p M spec q_pub h xq * (idealSpongeGame p M spec q_pub).visible.1 h := by
  let G := idealSpongeGame p M spec q_pub
  have hsum := G.1.1.sum_unsetMBOs_add_sum_tagMBO hadm
  have hdiff : G.1.1 (unsetMBOs h) - ∑ y, G.1.1 (unsetMBOs (h ++ [(xq, y)])) =
      ∑ y, G.1.1 (unsetMBOs h ++ [(xq, tagMBO true y)]) := by linarith
  change G.1.1 (unsetMBOs h) - ∑ y, G.1.1 (unsetMBOs (h ++ [(xq, y)])) ≤
      gameStepCost p M spec q_pub h xq * G.visible.1 h
  rw [hdiff]
  have htag := ofProbAutomatonGame_sum_tagMBO_true (idealSpongeGameStep p M spec q_pub)
    (idealGameInit p M) (idealSpongeGameStep_flag p M spec q_pub) h xq hadm
  change ∑ y, (TypedGame.ofProbAutomaton (idealSpongeGameStep p M spec q_pub) (idealGameInit p M)
      (idealSpongeGameStep_flag p M spec q_pub)).1.1 (unsetMBOs h ++ [(xq, tagMBO true y)]) ≤ _
  rw [htag]
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  let μ_u := (idealSpongeGameStep p M spec q_pub).belief A.withMBO.inputDomain
    ((idealGameInit p M).map fun s => (s, false)).1 (unsetMBOs h)
  let μ_v := (ProbStep.forgetMBO (idealSpongeGameStep p M spec q_pub)).belief A.inputDomain
    ((idealGameInit p M).map fun s => (s, false)).1 h
  have hble := unsetMBOs_belief_le_visible (idealSpongeGameStep p M spec q_pub) (idealGameInit p M)
    (idealSpongeGameStep_flag p M spec q_pub) h
  let badP : ((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes) × ByteState p.stateBytes)) → ℝ :=
    fun s => (idealSpongeGameStep p M spec q_pub (s, false) xq.1 xq.2).1.mass
      fun q => q.2.2 = true
  have hbadP_nn : ∀ s, 0 ≤ badP s := fun s =>
    Distribution.NonNeg.mass_nonneg (idealSpongeGameStep p M spec q_pub (s, false) xq.1 xq.2).2.1 _
  have hle_fst : μ_u.sum (fun sb w => w *
      (idealSpongeGameStep p M spec q_pub sb xq.1 xq.2).1.mass fun q => q.2.2 = true) ≤
      (fTransform Prod.fst μ_v).sum fun s w => w * badP s := by
    classical
    have h1 : μ_u.sum (fun sb w => w *
        (idealSpongeGameStep p M spec q_pub sb xq.1 xq.2).1.mass fun q => q.2.2 = true) =
        (fTransform Prod.fst μ_u).sum fun s w => w * badP s := by
      have hfst_sum : (fTransform Prod.fst μ_u).sum (fun s w => w * badP s) =
          μ_u.sum fun sb w => w * badP sb.1 := by
        change (μ_u.sum fun sb w => Finsupp.single sb.1 w).sum (fun s w => w * badP s) = _
        rw [Finsupp.sum_sum_index (by intro _; exact zero_mul _) (by intro _ _ _; ring)]
        apply Finsupp.sum_congr
        intro sb _
        rw [Finsupp.sum_single_index (zero_mul _)]
      rw [hfst_sum]
      apply Finsupp.sum_congr
      intro ⟨s, b⟩ hsb
      have hb : b = false := hble.1 (s, b) hsb
      subst hb
      rfl
    rw [h1]
    have hpt : ∀ s, (fTransform Prod.fst μ_u) s ≤ (fTransform Prod.fst μ_v) s := by
      intro s
      change (μ_u.sum fun sb w => Finsupp.single sb.1 w) s ≤
        (μ_v.sum fun sb w => Finsupp.single sb.1 w) s
      rw [Finsupp.sum_apply, Finsupp.sum_apply, Finsupp.sum, Finsupp.sum]
      set S_both := μ_u.support ∪ μ_v.support
      have hs1 : ∑ a ∈ μ_u.support, (Finsupp.single a.1 (μ_u a)) s =
          ∑ a ∈ S_both, (Finsupp.single a.1 (μ_u a)) s :=
        Finset.sum_subset Finset.subset_union_left fun a _ ha => by
          rw [Finsupp.notMem_support_iff.mp ha, Finsupp.single_zero, Finsupp.zero_apply]
      have hs2 : ∑ a ∈ μ_v.support, (Finsupp.single a.1 (μ_v a)) s =
          ∑ a ∈ S_both, (Finsupp.single a.1 (μ_v a)) s :=
        Finset.sum_subset Finset.subset_union_right fun a _ ha => by
          rw [Finsupp.notMem_support_iff.mp ha, Finsupp.single_zero, Finsupp.zero_apply]
      rw [hs1, hs2]
      apply Finset.sum_le_sum
      intro sb _
      by_cases heq : sb.1 = s
      · rw [heq, Finsupp.single_eq_same, Finsupp.single_eq_same]
        exact hble.2 sb
      · rw [Finsupp.single_eq_of_ne (Ne.symm heq), Finsupp.single_eq_of_ne (Ne.symm heq)]
    set S_both := (fTransform Prod.fst μ_u).support ∪ (fTransform Prod.fst μ_v).support
    rw [Finsupp.sum, Finsupp.sum]
    have hs1 : ∑ s ∈ (fTransform Prod.fst μ_u).support, (fTransform Prod.fst μ_u) s * badP s =
        ∑ s ∈ S_both, (fTransform Prod.fst μ_u) s * badP s :=
      Finset.sum_subset Finset.subset_union_left fun s _ hs => by
        rw [Finsupp.notMem_support_iff.mp hs, zero_mul]
    have hs2 : ∑ s ∈ (fTransform Prod.fst μ_v).support, (fTransform Prod.fst μ_v) s * badP s =
        ∑ s ∈ S_both, (fTransform Prod.fst μ_v) s * badP s :=
      Finset.sum_subset Finset.subset_union_right fun s _ hs => by
        rw [Finsupp.notMem_support_iff.mp hs, zero_mul]
    rw [hs1, hs2]
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hpt s) (hbadP_nn s)
  have hrel := idealGhost_belief_rel p M hp henc spec q_pub h
  have hbds := replayGhost_bounds p M spec q_pub h
  rcases hrg : replayGhost p M spec q_pub h with ⟨T_pub, keys, a_cnt⟩
  rw [hrg] at hrel hbds
  rcases hrel with ⟨hsupp, hvis, _⟩
  set initG : ProbDist ((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes)) ×
      List (List (ByteState p.rateBytes))) :=
    (𝒰[M → ByteState p.outputBytes]).map fun ro => (ro, [], [])
  set μ_g := (idealGhostStep p M spec q_pub).belief A.inputDomain initG.1 h
  have hμg_nn : μ_g.NonNeg := by
    have hstep_nn : ∀ h',
      ((idealGhostStep p M spec q_pub).belief A.inputDomain initG.1 h').NonNeg := by
      intro h'
      induction h' using List.reverseRecOn with
      | nil =>
        simp only [ProbStep.belief, ProbStep.beliefRev, List.reverse_nil]
        exact initG.2.1
      | append_singleton h' z ih' =>
        rw [ProbStep.belief_snoc]
        split_ifs
        · intro st
          simp only [ProbStep.transition, ProbStep.outcome]
          rw [bindK_apply, Finsupp.sum]
          exact Finset.sum_nonneg fun a _ => mul_nonneg (ih' a)
            (Distribution.NonNeg.fTransform (fun sy => by
              rw [Distribution.restrict, Finsupp.filter_apply]
              split_ifs
              · exact Distribution.NonNeg.fTransform
                  (idealGhostStep p M spec q_pub a z.1.1 z.1.2).2.1 _ sy
              · exact le_rfl) _ st)
        · intro _; exact le_rfl
    exact hstep_nn h
  have hexp_bound : ∀ (ro : M → ByteState p.outputBytes)
      (xq' : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o),
      ((sampleHiddenList p M encode ro keys).map fun hid => (ro, T_pub, hid)).1.sum
        (fun s w => w * (idealSpongeGameStep p M spec q_pub (s, false) xq'.1 xq'.2).1.mass
          fun q => q.2.2 = true) ≤
        gameStepCost p M spec q_pub h xq' := by
    intro ro xq'
    have hmap_sum : ((sampleHiddenList p M encode ro keys).map fun hid =>
        (ro, T_pub, hid)).1.sum
          (fun s w => w * (idealSpongeGameStep p M spec q_pub (s, false) xq'.1 xq'.2).1.mass
            fun q => q.2.2 = true) =
        (sampleHiddenList p M encode ro keys).1.sum fun hid w =>
          w * (idealSpongeGameStep p M spec q_pub ((ro, T_pub, hid), false) xq'.1 xq'.2).1.mass
            fun q => q.2.2 = true := by
      rw [ProbDist.map_val]
      change ((sampleHiddenList p M encode ro keys).1.sum fun hid w =>
        Finsupp.single (ro, T_pub, hid) w).sum _ = _
      rw [Finsupp.sum_sum_index (by intro _; exact zero_mul _) (by intro _ _ _; ring)]
      apply Finsupp.sum_congr
      intro hid _
      rw [Finsupp.sum_single_index (zero_mul _)]
    rw [hmap_sum]
    have hfresh_draw : ∀ (c_q : ByteState p.capacityBytes)
        (draw : ProbDist (ByteState p.stateBytes))
        (hdraw : ∀ caps : List (ByteState p.capacityBytes),
          draw.1.mass (fun z => capacityPart p z ∈ caps) ≤
            (caps.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ)),
        (sampleHiddenList p M encode ro keys).1.sum
          (fun hid w => w * draw.1.mass (fun z =>
            (false || decide (c_q ∈ hiddenCapsList p hid) ||
              decide (capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)) =
              true)) ≤
        ((2 * a_cnt + 2 * keys.length + 1 : ℕ) : ℝ) /
          (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
      intro c_q draw hdraw
      have hpt_hid : ∀ hid ∈ (sampleHiddenList p M encode ro keys).1.support,
          draw.1.mass (fun z =>
            (false || decide (c_q ∈ hiddenCapsList p hid) ||
              decide (capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)) =
              true) ≤
          (if c_q ∈ hiddenCapsList p hid then (1 : ℝ) else 0) +
            ((2 * a_cnt + keys.length + 1 : ℕ) : ℝ) /
              (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
        intro hid hhid
        have hlen_hid : hid.length = keys.length := by
          have hk := sampleHiddenList_keys p M encode ro keys hid hhid
          have := congrArg List.length hk
          simp only [List.length_map] at this
          exact this
        by_cases hc : c_q ∈ hiddenCapsList p hid
        · rw [ite_eq_left hc]
          have h1 : draw.1.mass (fun z =>
              (false || decide (c_q ∈ hiddenCapsList p hid) ||
                decide (capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)) =
                true) ≤ 1 :=
            (Distribution.mass_le_weight draw.2.1 _).trans_eq draw.2.2
          have h0 : (0 : ℝ) ≤ ((2 * a_cnt + keys.length + 1 : ℕ) : ℝ) /
              (Fintype.card (ByteState p.capacityBytes) : ℝ) := by positivity
          linarith
        · rw [ite_eq_right hc, zero_add]
          have hEq : draw.1.mass (fun z =>
              (false || decide (c_q ∈ hiddenCapsList p hid) ||
                decide (capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)) =
                true) =
              draw.1.mass (fun z =>
                capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid) := by
            apply Distribution.mass_congr
            intro z
            simp only [Bool.false_or, decide_eq_false hc, decide_eq_true_eq]
          rw [hEq]
          calc draw.1.mass (fun z =>
                capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)
              ≤ ((occupiedCapsList p T_pub ++ hiddenCapsList p hid).length : ℝ) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ) := hdraw _
            _ ≤ ((2 * a_cnt + keys.length + 1 : ℕ) : ℝ) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                apply Nat.cast_le.mpr
                simp only [List.length_append, length_occupiedCapsList, length_hiddenCapsList]
                omega
      calc (sampleHiddenList p M encode ro keys).1.sum
            (fun hid w => w * draw.1.mass (fun z =>
              (false || decide (c_q ∈ hiddenCapsList p hid) ||
                decide (capacityPart p z ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)) =
                true))
          ≤ (sampleHiddenList p M encode ro keys).1.sum
              (fun hid w => w * ((if c_q ∈ hiddenCapsList p hid then (1 : ℝ) else 0) +
                ((2 * a_cnt + keys.length + 1 : ℕ) : ℝ) /
                  (Fintype.card (ByteState p.capacityBytes) : ℝ))) := by
            simp only [Finsupp.sum]
            exact Finset.sum_le_sum fun hid hhid =>
              mul_le_mul_of_nonneg_left (hpt_hid hid hhid)
                ((sampleHiddenList p M encode ro keys).2.1 hid)
        _ = (sampleHiddenList p M encode ro keys).1.mass (fun hid => c_q ∈ hiddenCapsList p hid) +
              ((2 * a_cnt + keys.length + 1 : ℕ) : ℝ) /
                (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
            simp only [Finsupp.sum, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
            have hw : ∑ hid ∈ (sampleHiddenList p M encode ro keys).1.support,
                (sampleHiddenList p M encode ro keys).1 hid = 1 :=
              (sampleHiddenList p M encode ro keys).2.2
            rw [hw, one_mul]
            congr 1
            rw [Distribution.mass_eq_sum_of_support_subset _ Finset.Subset.rfl, Finset.sum_filter]
            exact Finset.sum_congr rfl fun hid _ => by split_ifs <;> ring
        _ ≤ (keys.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) +
              ((2 * a_cnt + keys.length + 1 : ℕ) : ℝ) /
                (Fintype.card (ByteState p.capacityBytes) : ℝ) :=
            add_le_add (sampleHiddenList_cap_mem_mass p M hp encode ro keys c_q) le_rfl
        _ = ((2 * a_cnt + 2 * keys.length + 1 : ℕ) : ℝ) /
              (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
            rw [← add_div]; push_cast; ring
    have hdraw_unif : ∀ caps : List (ByteState p.capacityBytes),
        (𝒰[ByteState p.stateBytes]).1.mass (fun z => capacityPart p z ∈ caps) ≤
          (caps.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
      intro caps
      have hEq : (𝒰[ByteState p.stateBytes]).1.mass (fun z => capacityPart p z ∈ caps) =
          (𝒰[ByteState p.stateBytes]).1.mass (fun z => capacityPart p z ∈ caps.toFinset) :=
        Distribution.mass_congr _ fun z => by simp only [List.mem_toFinset]
      rw [hEq]
      change (uniform (ByteState p.stateBytes)).mass (fun z => capacityPart p z ∈ caps.toFinset) ≤ _
      rw [uniform_mass_cap_mem p hp caps.toFinset]
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (List.toFinset_card_le caps)) (by
        positivity)
    have hdraw_tail : ∀ (d : ByteState p.outputBytes) (caps : List (ByteState p.capacityBytes)),
        ((𝒰[ByteState (tailBytes p)]).map fun t => assembleState p d t).1.mass
            (fun z => capacityPart p z ∈ caps) ≤
          (caps.length : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
      intro d caps
      rw [ProbDist.map_val, mass_fTransform]
      have hEq : (𝒰[ByteState (tailBytes p)]).1.mass
            (fun t => capacityPart p (assembleState p d t) ∈ caps) =
          (𝒰[ByteState (tailBytes p)]).1.mass
            (fun t => capacityPart p (assembleState p d t) ∈ caps.toFinset) :=
        Distribution.mass_congr _ fun t => by simp only [List.mem_toFinset]
      rw [hEq]
      change (uniform (ByteState (tailBytes p))).mass
        (fun t => capacityPart p (assembleState p d t) ∈ caps.toFinset) ≤ _
      rw [uniform_tail_mass_cap_mem p hp d caps.toFinset]
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (List.toFinset_card_le caps)) (by
        positivity)
    rcases xq' with ⟨o, u⟩
    unfold gameStepCost
    rw [hrg]
    rcases o with o | o
    · cases o
      dsimp only [idealSpongeGameStep]
      calc (sampleHiddenList p M encode ro keys).1.sum
            (fun hid w => w * ((sampleHiddenPrefixesWithBad p (nodeLaw p M encode ro) T_pub hid
              false (newHiddenPrefixes p T_pub (hid.map Prod.fst)
                (paddedBlocks p (encode u)))).map
                  fun p' => (((ro, T_pub, p'.1), p'.2), (ro u, p'.2))).1.mass
                fun q => q.2.2 = true)
          ≤ (sampleHiddenList p M encode ro keys).1.sum
              (fun hid w => w * (((spongePotential2 a_cnt (keys.length +
                (newHiddenPrefixes p T_pub keys (paddedBlocks p (encode u))).length) -
                spongePotential2 a_cnt keys.length : ℕ) : ℝ) /
                  (2 * (Fintype.card (ByteState p.capacityBytes) : ℝ)))) := by
            simp only [Finsupp.sum]
            apply Finset.sum_le_sum
            intro hid hhid
            apply mul_le_mul_of_nonneg_left _ ((sampleHiddenList p M encode ro keys).2.1 hid)
            rw [ProbDist.map_val, mass_fTransform]
            have hk := sampleHiddenList_keys p M encode ro keys hid hhid
            have hlen : hid.length = keys.length := by
              have := congrArg List.length hk
              simp only [List.length_map] at this; exact this
            rw [hk]
            simpa only [hlen] using
              sampleHiddenPrefixesWithBad_bad_mass_le p M hp encode ro T_pub hbds.1 hid
                (newHiddenPrefixes p T_pub keys (paddedBlocks p (encode u)))
        _ = _ := by
            simp only [Finsupp.sum, ← Finset.sum_mul]
            have hw : ∑ hid ∈ (sampleHiddenList p M encode ro keys).1.support,
                (sampleHiddenList p M encode ro keys).1 hid = 1 :=
              (sampleHiddenList p M encode ro keys).2.2
            rw [hw, one_mul]
    · cases o with
      | forward =>
        dsimp only [idealSpongeGameStep]
        cases hlu : lookupForwardEdge T_pub u with
        | some y =>
          dsimp only
          have hz : ∀ hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes),
              (ProbDist.single (((ro, T_pub, hid), false), (y, false))).1.mass
                (fun q => q.2.2 = true) = 0 := fun hid => by
            rw [ProbDist.single, Distribution.mass_single]
            simp only [Bool.false_eq_true, ↓reduceIte]
          apply le_of_eq
          simp only [Finsupp.sum]
          exact Finset.sum_eq_zero fun hid _ => (congrArg (_ * ·) (hz hid)).trans (mul_zero _)
        | none =>
          dsimp only
          cases hrp : rootedPrefix p M encode T_pub u with
          | some bs =>
            dsimp only
            by_cases hmem : bs ∈ keys
            · simp only [hmem, ↓reduceIte]
              apply le_of_eq
              simp only [Finsupp.sum]
              apply Finset.sum_eq_zero
              intro hid hhid
              rw [sampleHiddenList_keys p M encode ro keys hid hhid, ite_eq_left hmem]
              have hz : (ProbDist.single (((ro, recordForwardEdge T_pub u
                  ((hid.lookup bs).getD (zeroState p.stateBytes)), eraseHiddenKey p hid bs), false),
                  ((hid.lookup bs).getD (zeroState p.stateBytes), false))).1.mass
                  (fun q => q.2.2 = true) = 0 := by
                rw [ProbDist.single, Distribution.mass_single]
                simp only [Bool.false_eq_true, ↓reduceIte]
              exact (congrArg (_ * ·) hz).trans (mul_zero _)
            · simp only [hmem, ↓reduceIte]
              have hcongr : (sampleHiddenList p M encode ro keys).1.sum (fun hid w => w *
                  (if bs ∈ hid.map Prod.fst then
                    ProbDist.single (((ro, recordForwardEdge T_pub u
                      ((hid.lookup bs).getD (zeroState p.stateBytes)), eraseHiddenKey p hid bs),
                      false), ((hid.lookup bs).getD (zeroState p.stateBytes), false))
                  else
                    match completingMessage p encode T_pub u with
                    | some m => (𝒰[ByteState (tailBytes p)]).map fun t =>
                        let y := assembleState p (ro m) t
                        let bad' := false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p y ∈ occupiedCapsList p T_pub ++
                            hiddenCapsList p hid)
                        (((ro, recordForwardEdge T_pub u y, hid), bad'), (y, bad'))
                    | none => (𝒰[ByteState p.stateBytes]).map fun y =>
                        let bad' := false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p y ∈ occupiedCapsList p T_pub ++
                            hiddenCapsList p hid)
                        (((ro, recordForwardEdge T_pub u y, hid), bad'), (y, bad'))).1.mass
                    fun q => q.2.2 = true) =
                (sampleHiddenList p M encode ro keys).1.sum fun hid w => w *
                  (match completingMessage p encode T_pub u with
                  | some m => ((𝒰[ByteState (tailBytes p)]).map fun t =>
                      assembleState p (ro m) t).1.mass fun z =>
                        (false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p z ∈ occupiedCapsList p T_pub ++
                            hiddenCapsList p hid)) = true
                  | none => (𝒰[ByteState p.stateBytes]).1.mass fun z =>
                        (false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                          decide (capacityPart p z ∈ occupiedCapsList p T_pub ++
                            hiddenCapsList p hid)) = true) := by
                apply Finsupp.sum_congr
                intro hid hhid
                rw [sampleHiddenList_keys p M encode ro keys hid hhid, ite_eq_right hmem]
                cases completingMessage p encode T_pub u with
                | some m =>
                  congr 1; simp only [ProbDist.map_val, mass_fTransform]
                | none =>
                  congr 1; simp only [ProbDist.map_val, mass_fTransform]
              refine (le_of_eq hcongr).trans ?_
              cases completingMessage p encode T_pub u with
              | some m => exact hfresh_draw (capacityPart p u) _ (hdraw_tail (ro m))
              | none => exact hfresh_draw (capacityPart p u) _ hdraw_unif
          | none =>
            dsimp only
            cases completingMessage p encode T_pub u with
            | some m =>
              have hEq : (sampleHiddenList p M encode ro keys).1.sum (fun hid w => w *
                  ((𝒰[ByteState (tailBytes p)]).map fun t =>
                    let y := assembleState p (ro m) t
                    let bad' := false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p y ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)
                    (((ro, recordForwardEdge T_pub u y, hid), bad'), (y, bad'))).1.mass
                    fun q => q.2.2 = true) =
                (sampleHiddenList p M encode ro keys).1.sum fun hid w => w *
                  ((𝒰[ByteState (tailBytes p)]).map fun t => assembleState p (ro m) t).1.mass
                    fun z => (false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p z ∈ occupiedCapsList p T_pub ++
                        hiddenCapsList p hid)) = true := by
                apply Finsupp.sum_congr; intro hid _; congr 1
                simp only [ProbDist.map_val, mass_fTransform]
              exact (le_of_eq hEq).trans (hfresh_draw (capacityPart p u) _ (hdraw_tail (ro m)))
            | none =>
              have hEq : (sampleHiddenList p M encode ro keys).1.sum (fun hid w => w *
                  ((𝒰[ByteState p.stateBytes]).map fun y =>
                    let bad' := false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p y ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)
                    (((ro, recordForwardEdge T_pub u y, hid), bad'), (y, bad'))).1.mass
                    fun q => q.2.2 = true) =
                (sampleHiddenList p M encode ro keys).1.sum fun hid w => w *
                  (𝒰[ByteState p.stateBytes]).1.mass fun z =>
                    (false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                      decide (capacityPart p z ∈ occupiedCapsList p T_pub ++
                        hiddenCapsList p hid)) = true := by
                apply Finsupp.sum_congr; intro hid _; congr 1
                simp only [ProbDist.map_val, mass_fTransform]
              exact (le_of_eq hEq).trans (hfresh_draw (capacityPart p u) _ hdraw_unif)
      | inverse =>
        dsimp only [idealSpongeGameStep]
        cases hlu : lookupInverseEdge T_pub u with
        | some x =>
          dsimp only
          have hz : ∀ hid : List (List (ByteState p.rateBytes) × ByteState p.stateBytes),
              (ProbDist.single (((ro, T_pub, hid), false), (x, false))).1.mass
                (fun q => q.2.2 = true) = 0 := fun hid => by
            rw [ProbDist.single, Distribution.mass_single]
            simp only [Bool.false_eq_true, ↓reduceIte]
          apply le_of_eq
          simp only [Finsupp.sum]
          exact Finset.sum_eq_zero fun hid _ => (congrArg (_ * ·) (hz hid)).trans (mul_zero _)
        | none =>
          dsimp only
          have hEq : (sampleHiddenList p M encode ro keys).1.sum (fun hid w => w *
              ((𝒰[ByteState p.stateBytes]).map fun x =>
                let bad' := false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                  decide (capacityPart p x ∈ occupiedCapsList p T_pub ++ hiddenCapsList p hid)
                (((ro, recordInverseEdge T_pub x u, hid), bad'), (x, bad'))).1.mass
                fun q => q.2.2 = true) =
            (sampleHiddenList p M encode ro keys).1.sum fun hid w => w *
              (𝒰[ByteState p.stateBytes]).1.mass fun z =>
                (false || decide (capacityPart p u ∈ hiddenCapsList p hid) ||
                  decide (capacityPart p z ∈ occupiedCapsList p T_pub ++
                    hiddenCapsList p hid)) = true := by
            apply Finsupp.sum_congr; intro hid _; congr 1
            simp only [ProbDist.map_val, mass_fTransform]
          exact (le_of_eq hEq).trans (hfresh_draw (capacityPart p u) _ hdraw_unif)
  calc μ_u.sum (fun sb w => w *
          (idealSpongeGameStep p M spec q_pub sb xq.1 xq.2).1.mass fun q => q.2.2 = true)
      ≤ (fTransform Prod.fst μ_v).sum fun s w => w * badP s := hle_fst
    _ = (μ_g.bindK fun st =>
          ((sampleHiddenList p M encode st.1 st.2.2).map fun hid =>
            (st.1, st.2.1, hid)).1).sum fun s w => w * badP s := by rw [← hvis]
    _ = μ_g.sum fun st w => w *
          (((sampleHiddenList p M encode st.1 st.2.2).map fun hid =>
            (st.1, st.2.1, hid)).1.sum fun s w' => w' * badP s) := by
          change (μ_g.sum fun st w => w • ((sampleHiddenList p M encode st.1 st.2.2).map
            fun hid => (st.1, st.2.1, hid)).1).sum (fun s w' => w' * badP s) = _
          rw [Finsupp.sum_sum_index (by intro _; exact zero_mul _) (by intro _ _ _; ring)]
          apply Finsupp.sum_congr
          intro st _
          rw [Finsupp.sum_smul_index' (by intro _; exact zero_mul _)]
          simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul, mul_assoc]
    _ ≤ μ_g.sum fun _ w => w * gameStepCost p M spec q_pub h xq := by
          simp only [Finsupp.sum]
          apply Finset.sum_le_sum
          intro ⟨ro, T', k'⟩ hst
          rcases hsupp (ro, T', k') hst with ⟨rfl, rfl, _⟩
          exact mul_le_mul_of_nonneg_left (hexp_bound ro xq) (hμg_nn (ro, T', k'))
    _ = gameStepCost p M spec q_pub h xq * G.visible.1 h := by
          simp only [Finsupp.sum, ← Finset.sum_mul]
          have hwt : μ_g.weight = G.visible.1 h := by
            have hgv : G.visible.1 h = μ_v.weight := by
              change ((idealSpongeGame p M spec q_pub).visible.1 h) = _
              rw [idealSpongeGame, TypedGame.visible_ofProbAutomaton]
              rfl
            rw [hgv, ← Distribution.weight_fTransform Prod.fst μ_v, ← hvis,
              Distribution.weight_bindK]
            have h1 : ∀ st : (M → ByteState p.outputBytes) ×
                List (PermutationEdge (ByteState p.stateBytes)) ×
                List (List (ByteState p.rateBytes)),
                (((sampleHiddenList p M encode st.1 st.2.2).map
                  fun hid => (st.1, st.2.1, hid)).1).weight = 1 := fun st =>
              ((sampleHiddenList p M encode st.1 st.2.2).map fun hid => (st.1, st.2.1, hid)).2.2
            simp_rw [h1, mul_one]
            rfl
          change μ_g.weight * gameStepCost p M spec q_pub h xq = _
          rw [hwt, mul_comm]


end GameEquivalenceProof

end Commons.Sponge
