module

public import Commons.Definitions.BidirectionalSwitching
public import Commons.Schemes.Sponge.Uniform
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Tests for `Commons.Definitions.BidirectionalSwitching`

Exercises `LazyBidirectionalRF`, `lazyBidirectionalRFGame`, `strongURPRejectionGame`, exact
transcript mass formulas (`strongURP_mass_of_bijective_table` and `lazyBidirectionalRF_unset_mass`),
equivalence as games (`strongURPRejectionGame_gameEquivalent_lazyBidirectionalRFGame`), and the
bidirectional RP/RF switching lemma (`strongURP_dist_lazyBidirectionalRF_le`,
`strongURP_attach_dist_lazyBidirectionalRF_le`, `strongURP_substitutesWithin_lazyBidirectionalRF`)
on `Fin 8` and `ByteState 200` (Keccak 1600-bit state), verifies `cc_normalize` and
`cc_calc statistical` compatibility under CC custom notation (`Δ`, `•`, `≫`, `≃[...]`), and
audits `#print axioms`.
-/

@[expose] public section

namespace Tests.BidirectionalSwitching

open CategoryTheory SystemAlgebra Commons Commons.BidirectionalSwitching Commons.Sponge
open scoped SystemAlgebra

/-! ## Concrete `Fin 8` contracts -/

/-- Visible systems recover `StrongURP (Fin 8)` and `LazyBidirectionalRF (Fin 8) 4`. -/
example :
    (strongURPRejectionGame (Fin 8) 4).visible = StrongURP (Fin 8) (q := 4) ∧
      (lazyBidirectionalRFGame (Fin 8) 4).visible = LazyBidirectionalRF (Fin 8) 4 :=
  ⟨strongURPRejectionGame_visible (Fin 8) 4, lazyBidirectionalRFGame_visible (Fin 8) 4⟩

/-- Exact bidirectional switching bound on `Fin 8` with `q = 4`: `C(4, 2) / 8 = 6 / 8`. -/
example :
    Δ (StrongURP (Fin 8) (q := 4)) (LazyBidirectionalRF (Fin 8) 4) ≤
      ENNReal.ofReal (6 / 8 : ℝ) := by
  have h := strongURP_dist_lazyBidirectionalRF_le (Fin 8) 4
  have hval : ((Nat.choose 4 2 : ℝ) / Fintype.card (Fin 8)) = (6 / 8 : ℝ) := by
    rw [Fintype.card_fin]
    norm_num [Nat.choose]
  rwa [hval] at h

/-- Exact 2-edge mixed forward+inverse transcript masses on `Fin 8`:
`1 / (8 * 7) = 1 / 56` for `StrongURP` vs `1 / 8^2 = 1 / 64` for `lazyBidirectionalRFGame`. -/
example :
    let h : List ((Σ i, (Bidirectional (Fin 8) 4).X i) × Σ i, (Bidirectional (Fin 8) 4).Y i) :=
      [(⟨.forward, (0 : Fin 8)⟩, ⟨.forward, (1 : Fin 8)⟩),
       (⟨.inverse, (3 : Fin 8)⟩, ⟨.inverse, (2 : Fin 8)⟩)]
    (StrongURP (Fin 8) (q := 4)).1 h = 1 / 56 ∧
      (lazyBidirectionalRFGame (Fin 8) 4).1.1 (unsetMBOs h) = 1 / 64 ∧
      (strongURPRejectionGame (Fin 8) 4).1.1 (unsetMBOs h) = 1 / 64 := by
  intro h
  set table : List (Fin 8 × Fin 8) := [(0, 1), (2, 3)]
  have hadm : h = [] ∨ (Bidirectional (Fin 8) 4).domain (h.map Prod.fst) :=
    Or.inr ⟨by simp only [h, List.map_cons, List.map_nil, ne_eq, reduceCtorEq, not_false_eq_true],
      by simp only [h, List.length_map, List.length_cons, List.length_nil]; omega⟩
  have hne02 : (0 : Fin 8) ≠ 2 := by intro hc; exact absurd (congrArg Fin.val hc) (by omega)
  have hne13 : (1 : Fin 8) ≠ 3 := by intro hc; exact absurd (congrArg Fin.val hc) (by omega)
  have hb : IsPartialBijection table := by
    refine ⟨?_, ?_⟩
    · simp only [table, List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, List.nodup_nil, hne02, not_false_eq_true, and_self]
    · simp only [table, List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
        List.not_mem_nil, List.nodup_nil, hne13, not_false_eq_true, and_self]
  have hiff : ∀ π : Equiv.Perm (Fin 8), (∀ z ∈ h, permEval 4 π z.1 = z.2) ↔ Agrees table π := by
    intro π
    simp only [h, table, Agrees, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, permEval, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact and_congr_right fun _ =>
      ⟨fun hsym => by rw [← hsym, π.apply_symm_apply],
        fun h23 => by rw [← h23, π.symm_apply_apply]⟩
  have hurp := strongURP_mass_of_bijective_table (Fin 8) 4 h hadm hb hiff
  have hdesc : ((Fintype.card (Fin 8)).descFactorial table.length : ℝ) = 56 := by
    rw [Fintype.card_fin]
    norm_num [table, Nat.descFactorial]
  rw [hdesc] at hurp
  have ht : transcriptBijection 4 h = some table := by
    have hfresh1 : (1 : Fin 8) ∉ ([] : List (Fin 8 × Fin 8)).map Prod.snd := by
      simp only [List.map_nil, List.not_mem_nil, not_false_eq_true]
    have hl2 : lookupInverse ([(0, 1)] : List (Fin 8 × Fin 8)) (3 : Fin 8) = none := by
      rw [lookupInverse_eq_none_iff]
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      exact hne13.symm
    have hfresh2 : (2 : Fin 8) ∉ ([(0, 1)] : List (Fin 8 × Fin 8)).map Prod.fst := by
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      exact hne02.symm
    have hstep1 : stepBijection 4 ([] : List (Fin 8 × Fin 8))
        (⟨.forward, (0 : Fin 8)⟩, ⟨.forward, (1 : Fin 8)⟩) = some [(0, 1)] := by
      unfold stepBijection
      dsimp only
      have hl1 : lookupForward ([] : List (Fin 8 × Fin 8)) (0 : Fin 8) = none := by
        rw [lookupForward_eq_none_iff]
        simp only [List.map_nil, List.not_mem_nil, not_false_eq_true]
      rw [hl1]
      dsimp only
      rw [ite_eq_left hfresh1]
      rfl
    have hstep2 : stepBijection 4 ([(0, 1)] : List (Fin 8 × Fin 8))
        (⟨.inverse, (3 : Fin 8)⟩, ⟨.inverse, (2 : Fin 8)⟩) = some table := by
      unfold stepBijection
      dsimp only
      rw [hl2]
      dsimp only
      rw [ite_eq_left hfresh2]
      rfl
    simp only [transcriptBijection, h, List.foldl_cons, List.foldl_nil, Option.bind_some, hstep1,
      hstep2]
  have hrf := lazyBidirectionalRF_unset_mass (Fin 8) 4 h hadm ht
  have hpow : (Fintype.card (Fin 8) : ℝ) ^ table.length = 64 := by
    rw [Fintype.card_fin]
    norm_num [table]
  rw [hpow] at hrf
  have hrej : (strongURPRejectionGame (Fin 8) 4).1.1 (unsetMBOs h) = 1 / 64 :=
    (strongURPRejectionGame_gameEquivalent_lazyBidirectionalRFGame (Fin 8) 4 h).trans hrf
  exact ⟨hurp, hrf, hrej⟩

/-! ## Keccak 1600-bit (`ByteState 200`) switching, `cc_normalize`, and `cc_calc statistical` -/

/-- Exact bidirectional switching bound on Keccak's 1600-bit state `ByteState 200`. -/
lemma keccak_switching_dist_le (q : ℕ) :
    Δ (StrongURP (ByteState 200) (q := q)) (LazyBidirectionalRF (ByteState 200) q) ≤
      ENNReal.ofReal ((q.choose 2 : ℝ) / (256 ^ 200 : ℕ)) := by
  have h := strongURP_dist_lazyBidirectionalRF_le (ByteState 200) q
  rwa [card_byteState] at h

/-- Compatibility with `cc_normalize` and `cc_calc statistical` under CC custom notation (`Δ`, `•`,
`≫`): attaching `α ≫ β` to `StrongURP (ByteState 200)` transports the switching bound and chains
with a second statistical hop. -/
lemma keccak_cc_calc_attach (q : ℕ)
    {A B : Interface} (α : A ⟶ B) (β : B ⟶ Bidirectional (ByteState 200) q)
    {U : TypedSystem A} {δ : ENNReal}
    (hnext : Δ ((α ≫ β) • LazyBidirectionalRF (ByteState 200) q) U ≤ δ) :
    Δ (α • (β • StrongURP (ByteState 200) (q := q))) U ≤
      ENNReal.ofReal ((q.choose 2 : ℝ) / (256 ^ 200 : ℕ)) + δ := by
  have hnorm : α • (β • StrongURP (ByteState 200) (q := q)) =
      (α ≫ β) • StrongURP (ByteState 200) (q := q) := by
    cc_normalize
  rw [hnorm]
  cc_calc statistical
    (α ≫ β) • StrongURP (ByteState 200) (q := q)
      ≈[ENNReal.ofReal ((q.choose 2 : ℝ) / (256 ^ 200 : ℕ))]
        (α ≫ β) • LazyBidirectionalRF (ByteState 200) q := by
          have h := strongURP_attach_dist_lazyBidirectionalRF_le (ByteState 200) q (α ≫ β)
          rwa [card_byteState] at h
    _ ≈[δ] U := hnext

/-- Substitution-relation corollary (`≃[...]`) on `ByteState 200` against any admissible
distinguisher class. -/
lemma keccak_switching_substitutesWithin
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher] (q : ℕ) :
    StrongURP (ByteState 200) (q := q) ≃[fun _ =>
      ENNReal.ofReal ((q.choose 2 : ℝ) / (256 ^ 200 : ℕ))]
      LazyBidirectionalRF (ByteState 200) q := by
  have h := strongURP_substitutesWithin_lazyBidirectionalRF (ByteState 200) q
  rwa [card_byteState] at h

/-! ## Axiom audit of key exported theorems -/

#print axioms Commons.BidirectionalSwitching.lazyStrongURP_eq_strongURP
#print axioms Commons.lazyBidirectionalRFGame_visible
#print axioms Commons.strongURPRejectionGame_visible
#print axioms Commons.strongURPRejectionGame_gameEquivalent_lazyBidirectionalRFGame
#print axioms Commons.lazyBidirectionalRF_unset_mass
#print axioms Commons.strongURP_mass_of_bijective_table
#print axioms Commons.lazyBidirectionalRFGame_win_le
#print axioms Commons.strongURPRejectionGame_win_le
#print axioms Commons.strongURP_dist_lazyBidirectionalRF_le
#print axioms Commons.strongURP_attach_dist_lazyBidirectionalRF_le
#print axioms Commons.strongURP_substitutesWithin_lazyBidirectionalRF

open Probability Probability.Distribution in
/-- A colliding reply keeps the table unchanged, so the same query can sample a new reply. -/
example : lazyBidirectionalRFStep (X := Bool) 3 [(false, false)] .forward true =
    (𝒰[Bool]).map (fun y => if y then ([(false, false), (true, true)], true)
      else ([(false, false)], false)) := by
  have fresh : lookupForward [(false, false)] true = none := by
    rw [lookupForward_eq_none_iff]
    simp only [List.map_cons, List.map_nil, List.mem_singleton, Bool.true_eq_false,
      not_false_eq_true]
  rw [lazyBidirectionalRFStep, fresh]
  apply congrArg (fun f : Bool → List (Bool × Bool) × Bool => (𝒰[Bool]).map f)
  funext y
  cases y <;> simp only [List.map_cons, List.map_nil, List.mem_singleton,
    not_true_eq_false, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, ↓reduceIte]
  rfl

open Probability Probability.Distribution in
/-- Once the non-colliding pair is recorded, the query replays its retained answer. -/
example : lazyBidirectionalRFStep (X := Bool) 3 [(true, true)] .forward true =
    ProbDist.single ([(true, true)], true) := by
  simp only [lazyBidirectionalRFStep, lookupForward, List.lookup_cons, beq_self_eq_true]

end Tests.BidirectionalSwitching
