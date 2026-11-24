module

public import ConstructiveCryptography
public import RandomSystems.Typed.AutomatonGame
public import RandomSystems.Typed.DSL.Converters

/-!
# Transport of equivalence as games through converter attachment

Checks the optional `GameEquivalence` / `CompatibleGameEquivalence` contracts for identity and
two serial converters with explicit solver admission, verifies `cc_normalize` and `cc_calc`
compatibility on visible resources, and proves the regression separating game equivalence from
conditional equivalence under adaptive converter attachment.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.GameEquivalenceTransport

open CategoryTheory ConstructiveCryptography Probability SystemAlgebra
open scoped SystemAlgebra NNReal

section Abstract

universe u v w x

variable {C : Type u} [Category.{v} C]
variable {Phi : C → Type w} [ResourceTheory C Phi]
variable {Game : C → Type x} [DistinctionGames C Phi Game]
variable [GameAction C Game ℝ] [DistinctionGameAction C Phi Game]
variable [GameEquivalence C Phi Game] [CompatibleGameEquivalence C Phi Game]

/-- Identity attachment preserves equivalence as games with explicit solver admission. -/
example {A : C} {G H : Game A} (hGH : G ≡g H)
    {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ DistinctionGames.solvers A) :
    ((𝟙 A) • G : Game A) ≡g ((𝟙 A) • H : Game A) ∧
      DistinctionGames.absorb s (𝟙 A) ∈ DistinctionGames.solvers A ∧
      s.2 ((𝟙 A) • G) = s.2 ((𝟙 A) • H) := by
  refine ⟨GameEquivalence.attach_id_gameEquivalent hGH, DistinctionGames.absorb_mem (𝟙 A) hs, ?_⟩
  exact GameEquivalence.win_attach_eq (𝟙 A) hGH (DistinctionGames.solvers_winner hs)

/-- Two serial converters transport equivalence as games and bound the advantage of an explicitly
admitted solver, keeping solver admission explicit along both absorption steps. -/
example {A B D : C} (α : A ⟶ B) (β : B ⟶ D) {G H : Game D} (hGH : G ≡g H)
    {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ DistinctionGames.solvers A) :
    ((α ≫ β) • G : Game A) ≡g ((α ≫ β) • H : Game A) ∧
      (α • (β • G) : Game A) ≡g (α • (β • H) : Game A) ∧
      DistinctionGames.absorb (DistinctionGames.absorb s α) β ∈ DistinctionGames.solvers D ∧
      s.2 ((α ≫ β) • G) = s.2 ((α ≫ β) • H) ∧
      |s.1 ((α ≫ β) • DistinctionGames.visible G) -
          s.1 ((α ≫ β) • DistinctionGames.visible H)| ≤
        s.2 ((α ≫ β) • G) := by
  refine ⟨GameEquivalence.attach_comp_gameEquivalent α β hGH,
    GameEquivalence.attach_gameEquivalent α (GameEquivalence.attach_gameEquivalent β hGH),
    DistinctionGames.absorb_mem β (DistinctionGames.absorb_mem α hs),
    GameEquivalence.win_attach_eq (α ≫ β) hGH (DistinctionGames.solvers_winner hs),
    GameEquivalence.advantage_attach_le_win (α ≫ β) hGH hs⟩

end Abstract

section TypedContracts

/-- Typed identity and two serial converters preserve `≡g`, compose with `cc_normalize` on
visible resources, and interact cleanly with `cc_calc statistical`. -/
example {A B D : Interface} (α : A ⟶ B) (β : B ⟶ D) {G H : TypedGame D} (hGH : G ≡g H)
    {s : (TypedSystem A → ℝ) × (TypedGame A → ℝ)} (hs : s ∈ DistinctionGames.solvers A)
    {ε : ℝ≥0} (hε : Δ G.visible H.visible ≤ ε) :
    ((𝟙 D) • G : TypedGame D) ≡g ((𝟙 D) • H : TypedGame D) ∧
      ((α ≫ β) • G : TypedGame A) ≡g ((α ≫ β) • H : TypedGame A) ∧
      ((α ≫ β) • G.visible : TypedSystem A) = α • (β • G.visible) ∧
      Δ ((α ≫ β) • G.visible) ((α ≫ β) • H.visible) ≤ ε ∧
      |s.1 ((α ≫ β) • G.visible) - s.1 ((α ≫ β) • H.visible)| ≤ s.2 ((α ≫ β) • G) := by
  refine ⟨GameEquivalence.attach_id_gameEquivalent hGH,
    GameEquivalence.attach_comp_gameEquivalent α β hGH,
    by cc_normalize,
    ?_,
    GameEquivalence.advantage_attach_le_win (α ≫ β) hGH hs⟩
  cc_calc statistical
    (α ≫ β) • G.visible ≈[ε] (α ≫ β) • H.visible := hε

end TypedContracts

section Regression

/-- Single-port interface allowing up to `q` queries with query type `Q` and Boolean replies. -/
abbrev unitBoolInterface (Q : Type) [Fintype Q] (q : ℕ) : Interface :=
  { I := Unit
    X := fun _ => Q
    Y := fun _ => Bool
    «domain» := fun h => h ≠ [] ∧ h.length ≤ q
    nonempty_prefix := ⟨fun h => h.1 rfl, fun hp hne h => ⟨hne, hp.length_le.trans h.2⟩⟩
    bound := q
    length_le := fun _ h => h.2 }

/-- Outer interface: one query `()` returning a bit. -/
abbrev outerInterface : Interface := unitBoolInterface Unit 1

/-- Inner interface: up to two queries (`false` = `a`, `true` = `b`) returning bits. -/
abbrev innerInterface : Interface := unitBoolInterface Bool 2

/-- Retained random coins: `(r₁, r₂)` are fair bit replies for the first and second queries,
and `(f₁, f₂)` are independent fair flag coins for queries to `a`. -/
abbrev CoinState := (Bool × Bool) × (Bool × Bool)

/-- Uniform law over the 16 coin states. -/
noncomputable def coinLaw : Distribution.ProbDist CoinState :=
  Distribution.ProbDist.uniform CoinState

/-- Step returning `r₁` on the first query and `r₂` on the second query. -/
def fairBitStep : (Bool × CoinState) → (i : innerInterface.I) → innerInterface.X i →
    (Bool × CoinState) × innerInterface.Y i
  | (false, s), (), _ => ((true, s), s.1.1)
  | (true, s), (), _ => ((true, s), s.1.2)

/-- Hidden condition: query `a` (`false`) at step 0 is flagged iff `f₁ = true`, and at step 1
iff `f₂ = true`; query `b` (`true`) is never flagged. -/
def flagAtA (s : CoinState) : MC (Σ _ : Unit, Bool) :=
  ⟨fun xs => ∃ k : Fin xs.length, (xs[k]).2 = false ∧ (if k.1 = 0 then s.2.1 else s.2.2) = true,
    by
      intro p h hp ⟨k, hq, hf⟩
      have hlt : k.1 < h.length := lt_of_lt_of_le k.2 hp.length_le
      refine ⟨⟨k.1, hlt⟩, ?_, hf⟩
      simpa [hp.getElem k.2] using hq⟩

/-- Initial automaton law starting at step 0 (`false`) with uniform coins. -/
noncomputable def initLaw : Distribution.ProbDist (Bool × CoinState) :=
  coinLaw.map fun s => (false, s)

/-- Reference system `T`: independent fair bits on queries `a` and `b`. -/
noncomputable def innerRefT : TypedSystem innerInterface :=
  TypedSystem.ofAutomaton innerInterface fairBitStep initLaw

/-- Game `G`: independent fair bits on `a, b`, independently flagging each `a` with prob `1/2`. -/
noncomputable def innerGameG : TypedGame innerInterface :=
  TypedGame.ofAutomaton innerInterface fairBitStep initLaw (fun st => flagAtA st.2)

/-- Deterministic step for `H`: agrees with `G` on unflagged queries, but forces reply `false`
on the second query once the first query flagged. -/
def alteredStep : (Bool × CoinState) → (i : innerInterface.I) → innerInterface.X i →
    (Bool × CoinState) × innerInterface.Y i
  | (false, s), (), false => ((true, ((s.1.1, if s.2.1 then false else s.1.2), s.2)), s.1.1)
  | (false, s), (), true => ((true, s), s.1.1)
  | (true, s), (), _ => ((true, s), s.1.2)

/-- Game `H`: agrees with `G` whenever the MBO is unset, but differs once raised on query 1. -/
noncomputable def innerGameH : TypedGame innerInterface :=
  TypedGame.ofAutomaton innerInterface alteredStep initLaw (fun st => flagAtA st.2)

/-- Adaptive converter `α`: ask `b` (`true`) for bit `c`, then ask `a` (`false`) if `c = false`
and `b` (`true`) if `c = true`, and return `c`. -/
def adaptiveProgram :
    Program Unit outerInterface.I innerInterface.I outerInterface.X outerInterface.Y
      innerInterface.X innerInterface.Y :=
  fun _ _ _ ex => match ex with
    | [] => .inr ⟨(), true⟩
    | [(_, ⟨(), c⟩)] => .inr ⟨(), c⟩
    | (_, ⟨(), c⟩) :: _ :: _ => .inl ((), c)

lemma adaptiveProgram_bounded : adaptiveProgram.Bounded 2 := by
  intro _ _ _ ex q _ hq
  rcases ex with _ | ⟨⟨_, ⟨⟨⟩, c₁⟩⟩, _ | ⟨e₂, rest⟩⟩ <;> simp [adaptiveProgram] at hq ⊢

/-- Typed adaptive converter `α : outerInterface ⟶ innerInterface`. -/
noncomputable def adaptiveConverter : outerInterface ⟶ innerInterface :=
  TypedConverter.ofProgram () adaptiveProgram adaptiveProgram_bounded
    (fun _ hne hlen =>
      ⟨hne, by simpa [outerInterface, innerInterface, unitBoolInterface] using hlen⟩)

lemma coinLaw_mass (P : CoinState → Prop) [DecidablePred P] :
    coinLaw.1.mass P =
      (∑ r₁ : Bool, ∑ r₂ : Bool, ∑ f₁ : Bool, ∑ f₂ : Bool,
        if P ((r₁, r₂), (f₁, f₂)) then (1 : ℝ) else 0) / 16 := by
  rw [coinLaw, Distribution.ProbDist.uniform, Distribution.uniform_mass_eq_card_filter]
  have hcard : (Fintype.card CoinState : ℝ) = 16 := by norm_num
  rw [hcard, Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]

lemma replies_fairBitStep (s : CoinState)
    (h : List ((Σ _ : Unit, Bool) × Σ _ : Unit, Bool)) :
    Replies (filterDom innerInterface.domain (automatonSystem fairBitStep (false, s)))
        (h.map Prod.fst) (h.map Prod.snd) ↔
      match h with
      | [] => True
      | [(_, ⟨(), y₁⟩)] => s.1.1 = y₁
      | [(_, ⟨(), y₁⟩), (_, ⟨(), y₂⟩)] => s.1.1 = y₁ ∧ s.1.2 = y₂
      | _ :: _ :: _ :: _ => False := by
  match h with
  | [] =>
    exact iff_true_intro (replies_nil _)
  | [(⟨(), q₁⟩, ⟨(), y₁⟩)] =>
    simp only [List.map_cons, List.map_nil]
    rw [show ([⟨(), q₁⟩] : List (Σ _ : Unit, Bool)) = [] ++ [⟨(), q₁⟩] from rfl,
      show ([⟨(), y₁⟩] : List (Σ _ : Unit, Bool)) = [] ++ [⟨(), y₁⟩] from rfl, replies_snoc]
    simp [filterDom, automatonSystem, fairBitStep, stateAfter]
  | [(⟨(), q₁⟩, ⟨(), y₁⟩), (⟨(), q₂⟩, ⟨(), y₂⟩)] =>
    simp only [List.map_cons, List.map_nil]
    rw [show ([⟨(), q₁⟩, ⟨(), q₂⟩] : List (Σ _ : Unit, Bool)) = [⟨(), q₁⟩] ++ [⟨(), q₂⟩] from rfl,
      show ([⟨(), y₁⟩, ⟨(), y₂⟩] : List (Σ _ : Unit, Bool)) = [⟨(), y₁⟩] ++ [⟨(), y₂⟩] from rfl,
      replies_snoc,
      show ([⟨(), q₁⟩] : List (Σ _ : Unit, Bool)) = [] ++ [⟨(), q₁⟩] from rfl,
      show ([⟨(), y₁⟩] : List (Σ _ : Unit, Bool)) = [] ++ [⟨(), y₁⟩] from rfl, replies_snoc]
    simp [filterDom, automatonSystem, fairBitStep, stateAfter]
  | (⟨(), q₁⟩, ⟨(), y₁⟩) :: (⟨(), q₂⟩, ⟨(), y₂⟩) :: z :: zs =>
    constructor
    · intro hr
      have h3 := hr.2 2 (by simp)
      simp [filterDom] at h3
    · intro hf; exact hf.elim

lemma replies_alteredStep (s : CoinState)
    (h : List ((Σ _ : Unit, Bool) × Σ _ : Unit, Bool)) :
    Replies (filterDom innerInterface.domain (automatonSystem alteredStep (false, s)))
        (h.map Prod.fst) (h.map Prod.snd) ↔
      match h with
      | [] => True
      | [(_, ⟨(), y₁⟩)] => s.1.1 = y₁
      | [(⟨(), q₁⟩, ⟨(), y₁⟩), (_, ⟨(), y₂⟩)] =>
          s.1.1 = y₁ ∧ (if !q₁ && s.2.1 then false else s.1.2) = y₂
      | _ :: _ :: _ :: _ => False := by
  match h with
  | [] =>
    exact iff_true_intro (replies_nil _)
  | [(⟨(), q₁⟩, ⟨(), y₁⟩)] =>
    simp only [List.map_cons, List.map_nil]
    rw [show ([⟨(), q₁⟩] : List (Σ _ : Unit, Bool)) = [] ++ [⟨(), q₁⟩] from rfl,
      show ([⟨(), y₁⟩] : List (Σ _ : Unit, Bool)) = [] ++ [⟨(), y₁⟩] from rfl, replies_snoc]
    cases q₁ <;>
      simp [filterDom, automatonSystem, alteredStep, stateAfter]
  | [(⟨(), q₁⟩, ⟨(), y₁⟩), (⟨(), q₂⟩, ⟨(), y₂⟩)] =>
    simp only [List.map_cons, List.map_nil]
    rw [show ([⟨(), q₁⟩, ⟨(), q₂⟩] : List (Σ _ : Unit, Bool)) = [⟨(), q₁⟩] ++ [⟨(), q₂⟩] from rfl,
      show ([⟨(), y₁⟩, ⟨(), y₂⟩] : List (Σ _ : Unit, Bool)) = [⟨(), y₁⟩] ++ [⟨(), y₂⟩] from rfl,
      replies_snoc,
      show ([⟨(), q₁⟩] : List (Σ _ : Unit, Bool)) = [] ++ [⟨(), q₁⟩] from rfl,
      show ([⟨(), y₁⟩] : List (Σ _ : Unit, Bool)) = [] ++ [⟨(), y₁⟩] from rfl, replies_snoc]
    cases q₁ <;>
      simp [filterDom, automatonSystem, alteredStep, stateAfter]
  | (⟨(), q₁⟩, ⟨(), y₁⟩) :: (⟨(), q₂⟩, ⟨(), y₂⟩) :: z :: zs =>
    constructor
    · intro hr
      have h3 := hr.2 2 (by simp)
      simp [filterDom] at h3
    · intro hf; exact hf.elim

lemma flagAtA_nil (s : CoinState) : ¬ (flagAtA s).1 [] := by
  rintro ⟨⟨k, hk⟩, -⟩
  exact Nat.not_lt_zero _ hk

lemma flagAtA_singleton (s : CoinState) (q : Bool) :
    (flagAtA s).1 [⟨(), q⟩] ↔ q = false ∧ s.2.1 = true := by
  constructor
  · rintro ⟨⟨k, hk⟩, hq, hf⟩
    obtain rfl : k = 0 := by simp at hk; omega
    exact ⟨hq, by simpa using hf⟩
  · rintro ⟨hq, hf⟩
    exact ⟨⟨0, by simp⟩, hq, by simpa using hf⟩

lemma flagAtA_pair (s : CoinState) (q₁ q₂ : Bool) :
    (flagAtA s).1 [⟨(), q₁⟩, ⟨(), q₂⟩] ↔
      (q₁ = false ∧ s.2.1 = true) ∨ (q₂ = false ∧ s.2.2 = true) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hq, hf⟩
    simp only [List.length_cons, List.length_nil] at hk
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl
    · exact Or.inl ⟨hq, by simpa using hf⟩
    · exact Or.inr ⟨hq, by simpa using hf⟩
  · rintro (⟨hq, hf⟩ | ⟨hq, hf⟩)
    · exact ⟨⟨0, by simp⟩, hq, by simpa using hf⟩
    · exact ⟨⟨1, by simp⟩, hq, by simpa using hf⟩

/-- `G` and `H` are equivalent as games (`G ≡g H`), because they diverge only after query 1
raises the flag. -/
lemma innerGameG_gameEquivalent_innerGameH : innerGameG ≡g innerGameH := by
  intro h
  change innerGameG.1.1 (unsetMBOs h) = innerGameH.1.1 (unsetMBOs h)
  have hzero : ∀ st ∈ initLaw.1.support, ¬ (flagAtA st.2).1 [] := fun st _ => flagAtA_nil st.2
  rw [innerGameG, innerGameH,
    TypedGame.ofAutomaton_mass_unsetMBOs _ _ _ _ hzero,
    TypedGame.ofAutomaton_mass_unsetMBOs _ _ _ _ hzero,
    initLaw, Distribution.ProbDist.map_val, Distribution.mass_fTransform,
    Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro s
  rw [replies_fairBitStep, replies_alteredStep]
  match h with
  | [] => simp
  | [(⟨(), _⟩, ⟨(), _⟩)] => simp
  | [(⟨(), q₁⟩, ⟨(), _⟩), (⟨(), _⟩, ⟨(), _⟩)] =>
    simp only [List.map_cons, List.map_nil, flagAtA_pair]
    cases q₁ <;> simp only [Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, true_and]
    · constructor <;> rintro ⟨⟨h1, h2⟩, hnf⟩
      · have hf1 : s.2.1 = false := Bool.eq_false_iff.mpr fun h => hnf (Or.inl h)
        exact ⟨⟨h1, by simpa [hf1] using h2⟩, hnf⟩
      · have hf1 : s.2.1 = false := Bool.eq_false_iff.mpr fun h => hnf (Or.inl h)
        exact ⟨⟨h1, by simpa [hf1] using h2⟩, hnf⟩
    · rfl
  | _ :: _ :: _ :: _ => simp

/-- `G` and `H` are genuinely distinct games (`G.visible ≠ H.visible`, hence `G ≠ H`). -/
lemma innerGameG_ne_innerGameH : innerGameG ≠ innerGameH := by
  intro heq
  have hvis : innerGameG.visible.1 [(⟨(), false⟩, ⟨(), false⟩), (⟨(), true⟩, ⟨(), true⟩)] =
      innerGameH.visible.1 [(⟨(), false⟩, ⟨(), false⟩), (⟨(), true⟩, ⟨(), true⟩)] := by
    rw [heq]
  rw [innerGameG, innerGameH, TypedGame.visible_ofAutomaton, TypedGame.visible_ofAutomaton,
    TypedSystem.ofAutomaton_mass, TypedSystem.ofAutomaton_mass,
    initLaw, Distribution.ProbDist.map_val, Distribution.mass_fTransform,
    Distribution.mass_fTransform] at hvis
  have h1 : coinLaw.1.mass (fun s => Replies (filterDom innerInterface.domain
      (automatonSystem fairBitStep (false, s))) [⟨(), false⟩, ⟨(), true⟩]
      [⟨(), false⟩, ⟨(), true⟩]) = 1 / 4 := by
    have hcongr : ∀ s, Replies (filterDom innerInterface.domain
        (automatonSystem fairBitStep (false, s))) [⟨(), false⟩, ⟨(), true⟩]
        [⟨(), false⟩, ⟨(), true⟩] ↔ s.1.1 = false ∧ s.1.2 = true :=
      fun s => replies_fairBitStep s [(⟨(), false⟩, ⟨(), false⟩), (⟨(), true⟩, ⟨(), true⟩)]
    rw [Distribution.mass_congr _ hcongr, coinLaw_mass]
    simp only [Fintype.sum_bool]
    norm_num
  have h2 : coinLaw.1.mass (fun s => Replies (filterDom innerInterface.domain
      (automatonSystem alteredStep (false, s))) [⟨(), false⟩, ⟨(), true⟩]
      [⟨(), false⟩, ⟨(), true⟩]) = 1 / 8 := by
    have hcongr : ∀ s, Replies (filterDom innerInterface.domain
        (automatonSystem alteredStep (false, s))) [⟨(), false⟩, ⟨(), true⟩]
        [⟨(), false⟩, ⟨(), true⟩] ↔
        s.1.1 = false ∧ (if s.2.1 then false else s.1.2) = true :=
      fun s => by
        simpa using replies_alteredStep s [(⟨(), false⟩, ⟨(), false⟩), (⟨(), true⟩, ⟨(), true⟩)]
    rw [Distribution.mass_congr _ hcongr, coinLaw_mass]
    simp only [Fintype.sum_bool]
    norm_num
  simp only [List.map_cons, List.map_nil] at hvis
  rw [h1, h2] at hvis
  norm_num at hvis

/-- `G` is conditionally equivalent to the fair-bit reference system `T` (`G |≡ T`). -/
lemma innerGameG_conditionallyEquivalent_innerRefT : innerGameG |≡ innerRefT := by
  intro h
  have hzero : ∀ st ∈ initLaw.1.support, ¬ (flagAtA st.2).1 [] := fun st _ => flagAtA_nil st.2
  match h with
  | [] => simp [unsetMBOs, RandomSystem.unsetProbability_nil, RandomSystem.mass_nil]
  | [(⟨(), q₁⟩, ⟨(), y₁⟩)] =>
    have hadm : innerInterface.domain [⟨(), q₁⟩] := by
      simp [innerInterface, unitBoolInterface]
    simp only [List.map_cons, List.map_nil]
    rw [innerGameG, innerRefT, TypedGame.ofAutomaton_mass_unsetMBOs _ _ _ _ hzero,
      TypedGame.ofAutomaton_unsetProbability _ _ _ _ hadm, TypedSystem.ofAutomaton_mass,
      initLaw, Distribution.ProbDist.map_val, Distribution.mass_fTransform,
      Distribution.mass_fTransform, Distribution.mass_fTransform]
    simp only [List.map_cons, List.map_nil]
    have hL : ∀ s,
        (Replies (filterDom innerInterface.domain (automatonSystem fairBitStep (false, s)))
          [⟨(), q₁⟩] [⟨(), y₁⟩] ∧ ¬ (flagAtA s).1 [⟨(), q₁⟩]) ↔
        s.1.1 = y₁ ∧ ¬ (q₁ = false ∧ s.2.1 = true) :=
      fun s => by
        have hr : Replies (filterDom innerInterface.domain (automatonSystem fairBitStep (false, s)))
            [⟨(), q₁⟩] [⟨(), y₁⟩] ↔ s.1.1 = y₁ := by
          simpa using replies_fairBitStep s [(⟨(), q₁⟩, ⟨(), y₁⟩)]
        rw [hr, flagAtA_singleton]
    have hU : ∀ s, (flagAtA s).1 [⟨(), q₁⟩] ↔ q₁ = false ∧ s.2.1 = true :=
      fun s => flagAtA_singleton s q₁
    have hR : ∀ s,
        Replies (filterDom innerInterface.domain (automatonSystem fairBitStep (false, s)))
          [⟨(), q₁⟩] [⟨(), y₁⟩] ↔ s.1.1 = y₁ :=
      fun s => by simpa using replies_fairBitStep s [(⟨(), q₁⟩, ⟨(), y₁⟩)]
    rw [Distribution.mass_congr _ hL, Distribution.mass_congr _ hU, Distribution.mass_congr _ hR,
      coinLaw_mass, coinLaw_mass, coinLaw_mass]
    cases q₁ <;> cases y₁ <;> simp only [Fintype.sum_bool] <;> norm_num
  | [(⟨(), q₁⟩, ⟨(), y₁⟩), (⟨(), q₂⟩, ⟨(), y₂⟩)] =>
    have hadm : innerInterface.domain [⟨(), q₁⟩, ⟨(), q₂⟩] := by
      simp [innerInterface, unitBoolInterface]
    simp only [List.map_cons, List.map_nil]
    rw [innerGameG, innerRefT, TypedGame.ofAutomaton_mass_unsetMBOs _ _ _ _ hzero,
      TypedGame.ofAutomaton_unsetProbability _ _ _ _ hadm, TypedSystem.ofAutomaton_mass,
      initLaw, Distribution.ProbDist.map_val, Distribution.mass_fTransform,
      Distribution.mass_fTransform, Distribution.mass_fTransform]
    simp only [List.map_cons, List.map_nil]
    have hL : ∀ s,
        (Replies (filterDom innerInterface.domain (automatonSystem fairBitStep (false, s)))
          [⟨(), q₁⟩, ⟨(), q₂⟩] [⟨(), y₁⟩, ⟨(), y₂⟩] ∧ ¬ (flagAtA s).1 [⟨(), q₁⟩, ⟨(), q₂⟩]) ↔
        (s.1.1 = y₁ ∧ s.1.2 = y₂) ∧
          ¬ ((q₁ = false ∧ s.2.1 = true) ∨ (q₂ = false ∧ s.2.2 = true)) :=
      fun s => by
        have hr : Replies (filterDom innerInterface.domain (automatonSystem fairBitStep (false, s)))
            [⟨(), q₁⟩, ⟨(), q₂⟩] [⟨(), y₁⟩, ⟨(), y₂⟩] ↔ s.1.1 = y₁ ∧ s.1.2 = y₂ := by
          simpa using replies_fairBitStep s [(⟨(), q₁⟩, ⟨(), y₁⟩), (⟨(), q₂⟩, ⟨(), y₂⟩)]
        rw [hr, flagAtA_pair]
    have hU : ∀ s, (flagAtA s).1 [⟨(), q₁⟩, ⟨(), q₂⟩] ↔
        (q₁ = false ∧ s.2.1 = true) ∨ (q₂ = false ∧ s.2.2 = true) :=
      fun s => flagAtA_pair s q₁ q₂
    have hR : ∀ s,
        Replies (filterDom innerInterface.domain (automatonSystem fairBitStep (false, s)))
          [⟨(), q₁⟩, ⟨(), q₂⟩] [⟨(), y₁⟩, ⟨(), y₂⟩] ↔ s.1.1 = y₁ ∧ s.1.2 = y₂ :=
      fun s => by simpa using replies_fairBitStep s [(⟨(), q₁⟩, ⟨(), y₁⟩), (⟨(), q₂⟩, ⟨(), y₂⟩)]
    rw [Distribution.mass_congr _ hL, Distribution.mass_congr _ hU, Distribution.mass_congr _ hR,
      coinLaw_mass, coinLaw_mass, coinLaw_mass]
    cases q₁ <;> cases y₁ <;> cases q₂ <;> cases y₂ <;> simp only [Fintype.sum_bool] <;> norm_num
  | (⟨(), q₁⟩, ⟨(), y₁⟩) :: (⟨(), q₂⟩, ⟨(), y₂⟩) :: z :: zs =>
    have hlen : innerInterface.bound <
        ((⟨(), q₁⟩, ⟨(), y₁⟩) :: (⟨(), q₂⟩, ⟨(), y₂⟩) :: z :: zs).length := by
      simp
    have hG0 : innerGameG.1.1
        (unsetMBOs ((⟨(), q₁⟩, ⟨(), y₁⟩) :: (⟨(), q₂⟩, ⟨(), y₂⟩) :: z :: zs)) = 0 :=
      innerGameG.1.1.mass_eq_zero_of_bound_lt (by rw [unsetMBOs, List.length_map]; exact hlen)
    have hT0 : innerRefT.1
        ((⟨(), q₁⟩, ⟨(), y₁⟩) :: (⟨(), q₂⟩, ⟨(), y₂⟩) :: z :: zs) = 0 :=
      innerRefT.1.mass_eq_zero_of_bound_lt hlen
    rw [hG0, hT0, mul_zero]

/-- Deterministic discrete game for one coin realization `s`. -/
noncomputable def coinDDG (s : CoinState) :
    DDG (Σ i, innerInterface.X i) (Σ i, innerInterface.Y i) :=
  (⟨(innerInterface.automatonDDS fairBitStep (false, s)).1,
    (innerInterface.automatonDDS fairBitStep (false, s)).2.1⟩, flagAtA s)

open scoped Classical in
/-- Exact reply of `liftMBO adaptiveProgram` attached to one deterministic realization of `G`:
returns `(r₁, if r₁ then false else f₂)`. -/
lemma apply_liftMBO_adaptive_single (s : CoinState) :
    trim (apply (liftMBO (DDC.ofProgramOn () adaptiveProgram outerInterface.domain))
      (DDG.withMBO (coinDDG s)).1) [⟨(), ()⟩] =
    Part.some ⟨(), (s.1.1, if s.1.1 then false else s.2.2)⟩ := by
  let a := DDC.ofProgramOn () adaptiveProgram outerInterface.domain
  let g := (DDG.withMBO (coinDDG s)).1
  have h1 : (⟨⟨some (), ()⟩, true⟩ : Σ l, twoFam (withMBO outerInterface.Y) innerInterface.X l) ∈
      liftMBO a [⟨⟨none, ()⟩, ()⟩] := by
    rw [mem_liftMBO]
    refine ⟨?_, rfl⟩
    simp [a, DDC.ofProgramOn, DDC.ofProgram, filterDom, outsideInputs, outsideMap, insideMap,
      splitIn, SystemAlgebra.restrict, Program.after, Program.step, adaptiveProgram, Program.emit]
  have h2 : (⟨(), (s.1.1, false)⟩ : Σ i, withMBO innerInterface.Y i) ∈ g [⟨(), true⟩] := by
    have hnf : ¬ (flagAtA s).1 [⟨(), true⟩] := by
      rw [flagAtA_singleton]; simp
    have hraw : (⟨(), s.1.1⟩ : Σ i, innerInterface.Y i) ∈ (coinDDG s).1.1 [⟨(), true⟩] := by
      simp [coinDDG, Interface.automatonDDS, filterDom, automatonSystem, fairBitStep, stateAfter]
    exact (Part.mem_map_iff _).mpr ⟨⟨(), s.1.1⟩, hraw, by
      change tagMBO (Y := innerInterface.Y) (decide ((flagAtA s).1 [⟨(), true⟩])) ⟨(), s.1.1⟩ = _
      simp [tagMBO, hnf]⟩
  have h3 : (⟨⟨some (), ()⟩, s.1.1⟩ : Σ l, twoFam (withMBO outerInterface.Y) innerInterface.X l) ∈
      liftMBO a [⟨⟨none, ()⟩, ()⟩, ⟨⟨some (), ()⟩, (s.1.1, false)⟩] := by
    rw [mem_liftMBO]
    refine ⟨?_, rfl⟩
    simp [a, DDC.ofProgramOn, DDC.ofProgram, filterDom, outsideInputs, outsideMap, insideMap,
      forgetMBO, splitIn, SystemAlgebra.restrict, Program.after, Program.run, Program.step,
      adaptiveProgram, Program.emit]
  have h4 : (⟨(), (s.1.2, if s.1.1 then false else s.2.2)⟩ : Σ i, withMBO innerInterface.Y i) ∈
      g [⟨(), true⟩, ⟨(), s.1.1⟩] := by
    have hflag : decide ((flagAtA s).1 [⟨(), true⟩, ⟨(), s.1.1⟩]) =
        if s.1.1 then false else s.2.2 := by
      rw [flagAtA_pair]
      cases s.1.1 <;> cases s.2.2 <;> simp
    have hraw : (⟨(), s.1.2⟩ : Σ i, innerInterface.Y i) ∈
        (coinDDG s).1.1 [⟨(), true⟩, ⟨(), s.1.1⟩] := by
      simp [coinDDG, Interface.automatonDDS, filterDom, automatonSystem, fairBitStep, stateAfter]
    exact (Part.mem_map_iff _).mpr ⟨⟨(), s.1.2⟩, hraw, by
      change tagMBO (Y := innerInterface.Y) (decide ((flagAtA s).1 [⟨(), true⟩, ⟨(), s.1.1⟩]))
        ⟨(), s.1.2⟩ = _
      rw [hflag]; rfl⟩
  have h5 : (⟨⟨none, ()⟩, (s.1.1, if s.1.1 then false else s.2.2)⟩ :
      Σ l, twoFam (withMBO outerInterface.Y) innerInterface.X l) ∈
      liftMBO a [⟨⟨none, ()⟩, ()⟩, ⟨⟨some (), ()⟩, (s.1.1, false)⟩,
        ⟨⟨some (), ()⟩, (s.1.2, if s.1.1 then false else s.2.2)⟩] := by
    rw [mem_liftMBO]
    refine ⟨?_, ?_⟩
    · simp [a, DDC.ofProgramOn, DDC.ofProgram, filterDom, outsideInputs, outsideMap, insideMap,
        forgetMBO, splitIn, SystemAlgebra.restrict, Program.after, Program.run, Program.step,
        adaptiveProgram, Program.emit]
    · rfl
  have hex : Exchange (pair (liftMBO a) g) resourceRoute [resourceInput ⟨(), ()⟩]
      (some ⟨(), (s.1.1, if s.1.1 then false else s.2.2)⟩)
      [resourceInput ⟨(), ()⟩, ⟨some (), ⟨(), true⟩⟩, ⟨none, ⟨⟨some (), ()⟩, (s.1.1, false)⟩⟩,
        ⟨some (), ⟨(), s.1.1⟩⟩,
        ⟨none, ⟨⟨some (), ()⟩, (s.1.2, if s.1.1 then false else s.2.2)⟩⟩] := by
    refine Exchange.feed _ ⟨none, ⟨⟨some (), ()⟩, true⟩⟩ ⟨some (), ⟨(), true⟩⟩ _ _ ?_ rfl ?_
    · change _ ∈ pair (liftMBO a) g ([] ++ [⟨none, ⟨⟨none, ()⟩, ()⟩⟩])
      rw [pair_left]
      exact Part.mem_map _ h1
    refine Exchange.feed _ ⟨some (), ⟨(), (s.1.1, false)⟩⟩
      ⟨none, ⟨⟨some (), ()⟩, (s.1.1, false)⟩⟩ _ _ ?_ rfl ?_
    · rw [pair_right]
      simpa [resourceInput, SystemAlgebra.restrict] using h2
    refine Exchange.feed _ ⟨none, ⟨⟨some (), ()⟩, s.1.1⟩⟩ ⟨some (), ⟨(), s.1.1⟩⟩ _ _ ?_ rfl ?_
    · rw [pair_left]
      simpa [resourceInput, SystemAlgebra.restrict] using h3
    refine Exchange.feed _ ⟨some (), ⟨(), (s.1.2, if s.1.1 then false else s.2.2)⟩⟩
      ⟨none, ⟨⟨some (), ()⟩, (s.1.2, if s.1.1 then false else s.2.2)⟩⟩ _ _ ?_ rfl ?_
    · rw [pair_right]
      simpa [resourceInput, SystemAlgebra.restrict] using h4
    refine Exchange.out _ ⟨none, ⟨⟨none, ()⟩, (s.1.1, if s.1.1 then false else s.2.2)⟩⟩ _ ?_ rfl
    rw [pair_left]
    simpa [resourceInput, SystemAlgebra.restrict] using h5
  have happly : (⟨(), (s.1.1, if s.1.1 then false else s.2.2)⟩ : Σ i, withMBO outerInterface.Y i) ∈
      apply (liftMBO a) g [⟨(), ()⟩] := by
    rw [apply_eq, mem_interconnect]
    exact ⟨_, Induces.snoc [] (⟨(), ()⟩ : Σ i, outerInterface.X i) none [] _ _ Induces.nil hex⟩
  have hreach : Reach (apply (liftMBO a) g) [⟨(), ()⟩] :=
    reach_snoc_iff.mpr ⟨reach_nil _, Part.dom_iff_mem.mpr ⟨_, happly⟩⟩
  exact Part.eq_some_iff.mpr (by rw [trim, ite_eq_left hreach]; exact happly)

/-- Exact mass of `adaptiveConverter • innerGameG` at one outer reply `(c, b)`. -/
lemma attach_adaptive_innerGameG_mass (c b : Bool) :
    (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
        [(⟨(), ()⟩, ⟨(), (c, b)⟩)] =
      coinLaw.1.mass (fun s => s.1.1 = c ∧ (if s.1.1 then false else s.2.2) = b) := by
  let a := DDC.ofProgramOn () adaptiveProgram outerInterface.domain
  have ha : IsDDCFrom innerInterface.domain outerInterface.domain 2 a :=
    DDC.ofProgramOn_isDDCFrom adaptiveProgram_bounded outerInterface.nonempty_prefix.2
      (fun h hr hF => by
        by_cases hne : insideQueries (h.map Prod.snd) = []
        · exact Or.inl hne
        · exact Or.inr ⟨hne, by
            simpa [outerInterface, innerInterface, unitBoolInterface] using
              DDC.insideQueries_length_le_of_budget adaptiveProgram_bounded
                outerInterface.length_le hr hF⟩)
  let P : Distribution.ProbDist {x // IsDDCFrom innerInterface.domain outerInterface.domain 2 x} :=
    Distribution.ProbDist.single ⟨a, ha⟩
  have hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = adaptiveConverter.1 h := by
    intro h
    simp [P, behaviorMass, Distribution.ProbDist.single, Distribution.mass_single,
      adaptiveConverter, TypedConverter.ofProgram, TypedConverter.ofDDC, PDCBehavior.ofDDC_apply, a]
  let Q : Distribution.ProbDist
      {s : InterfaceSystem innerInterface.I innerInterface.X (withMBO innerInterface.Y) //
        IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ innerInterface.domain h} :=
    coinLaw.map fun s =>
      ⟨(DDG.withMBO (coinDDG s)).1,
        ⟨(DDG.withMBO (coinDDG s)).2,
          by
            intro h q y hy
            obtain ⟨y₀, hy₀, rfl⟩ := (Part.mem_map_iff _).mp hy
            exact (innerInterface.automatonDDS fairBitStep (false, s)).2.2.1 h q y₀ hy₀,
          fun h => by
            simpa [DDG.withMBO, coinDDG] using
              (innerInterface.automatonDDS fairBitStep (false, s)).2.2.2 h⟩⟩
  have hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = innerGameG.1.1 h := by
    intro h
    change behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) =
      (PDG.behavior (PDG.ofAutomaton innerInterface fairBitStep initLaw
        (fun st => flagAtA st.2)).1
        (PDG.ofAutomaton innerInterface fairBitStep initLaw (fun st => flagAtA st.2)).2) h
    simp [Q, coinDDG, behaviorMass, PDG.behavior_apply, PDG.ofAutomaton, initLaw,
      Distribution.ProbDist.map_val, Distribution.mass_fTransform]
  change (PDCBehavior.attach innerInterface.nonempty_prefix outerInterface.nonempty_prefix
    (PDCBehavior.liftMBO adaptiveConverter) innerGameG.1.1 innerGameG.1.2)
    [(⟨(), ()⟩, ⟨(), (c, b)⟩)] = _
  rw [PDCBehavior.attach_presents innerInterface.nonempty_prefix outerInterface.nonempty_prefix
    (PDCBehavior.liftMBO adaptiveConverter) innerGameG.1.1 innerGameG.1.2
    (liftPresentation P) Q (PDCBehavior.liftMBO_presents adaptiveConverter P hP) hQ,
    behaviorMass_attachPDS]
  simp only [liftPresentation, P, Q, Distribution.ProbDist.single, Distribution.ProbDist.map_val,
    Distribution.fTransform_single, Distribution.prod_single_left, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro s
  have hrep : Replies (trim (apply (liftMBO a) (DDG.withMBO (coinDDG s)).1))
      ([⟨(), ()⟩] : List (Σ i, outerInterface.X i))
      ([⟨(), (c, b)⟩] : List (Σ i, withMBO outerInterface.Y i)) ↔
      s.1.1 = c ∧ (if s.1.1 then false else s.2.2) = b := by
    rw [show ([⟨(), ()⟩] : List (Σ i, outerInterface.X i)) = [] ++ [⟨(), ()⟩] from rfl,
      show ([⟨(), (c, b)⟩] : List (Σ i, withMBO outerInterface.Y i)) = [] ++ [⟨(), (c, b)⟩]
        from rfl,
      replies_snoc, List.nil_append, apply_liftMBO_adaptive_single s]
    simp [Part.some_inj, Prod.mk.injEq]
  simpa using hrep

/-- Regression: attaching `adaptiveConverter` preserves `G ≡g H`, yet breaks conditional
equivalence because the unset-to-reference ratio is `1/2` at reply `false` and `1` at reply
`true` for the same outer query `()`. -/
theorem regression_gameEquivalent_not_conditionallyEquivalent :
    (innerGameG |≡ innerRefT) ∧
      (innerGameG ≡g innerGameH) ∧
      innerGameG ≠ innerGameH ∧
      ((adaptiveConverter • innerGameG : TypedGame outerInterface) ≡g
        (adaptiveConverter • innerGameH : TypedGame outerInterface)) ∧
      (adaptiveConverter • innerRefT : TypedSystem outerInterface).1
        [(⟨(), ()⟩, ⟨(), false⟩)] = 1 / 2 ∧
      (adaptiveConverter • innerRefT : TypedSystem outerInterface).1
        [(⟨(), ()⟩, ⟨(), true⟩)] = 1 / 2 ∧
      (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
        (unsetMBOs [(⟨(), ()⟩, ⟨(), false⟩)]) = 1 / 4 ∧
      (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
        (unsetMBOs [(⟨(), ()⟩, ⟨(), true⟩)]) = 1 / 2 ∧
      ¬ ((adaptiveConverter • innerGameG : TypedGame outerInterface) |≡
        (adaptiveConverter • innerRefT : TypedSystem outerInterface)) := by
  have hunset0 : (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
      (unsetMBOs [(⟨(), ()⟩, ⟨(), false⟩)]) = 1 / 4 := by
    change (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
      [(⟨(), ()⟩, ⟨(), (false, false)⟩)] = 1 / 4
    rw [attach_adaptive_innerGameG_mass false false, coinLaw_mass]
    simp only [Fintype.sum_bool]
    norm_num
  have hunset1 : (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
      (unsetMBOs [(⟨(), ()⟩, ⟨(), true⟩)]) = 1 / 2 := by
    change (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
      [(⟨(), ()⟩, ⟨(), (true, false)⟩)] = 1 / 2
    rw [attach_adaptive_innerGameG_mass true false, coinLaw_mass]
    simp only [Fintype.sum_bool]
    norm_num
  have hset0 : (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
      [(⟨(), ()⟩, ⟨(), (false, true)⟩)] = 1 / 4 := by
    rw [attach_adaptive_innerGameG_mass false true, coinLaw_mass]
    simp only [Fintype.sum_bool]
    norm_num
  have hset1 : (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1
      [(⟨(), ()⟩, ⟨(), (true, true)⟩)] = 0 := by
    rw [attach_adaptive_innerGameG_mass true true, coinLaw_mass]
    simp only [Fintype.sum_bool]
    norm_num
  have hvis : (adaptiveConverter • innerRefT : TypedSystem outerInterface) =
      (adaptiveConverter • innerGameG : TypedGame outerInterface).visible := by
    have hvisG : innerGameG.visible = innerRefT := TypedGame.visible_ofAutomaton _ _ _ _
    rw [← hvisG]
    exact (DistinctionGameAction.visible_attachGame adaptiveConverter innerGameG).symm
  have href0 : (adaptiveConverter • innerRefT : TypedSystem outerInterface).1
      [(⟨(), ()⟩, ⟨(), false⟩)] = 1 / 2 := by
    rw [hvis]
    change (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1.visible
      [(⟨(), ()⟩, ⟨(), false⟩)] = 1 / 2
    rw [RandomSystem.visible_apply]
    simp only [sumMBO, tagMBO]
    have h0 := hunset0
    simp only [unsetMBOs, List.map_cons, List.map_nil, tagMBO] at h0
    linarith [h0, hset0]
  have href1 : (adaptiveConverter • innerRefT : TypedSystem outerInterface).1
      [(⟨(), ()⟩, ⟨(), true⟩)] = 1 / 2 := by
    rw [hvis]
    change (adaptiveConverter • innerGameG : TypedGame outerInterface).1.1.visible
      [(⟨(), ()⟩, ⟨(), true⟩)] = 1 / 2
    rw [RandomSystem.visible_apply]
    simp only [sumMBO, tagMBO]
    have h1 := hunset1
    simp only [unsetMBOs, List.map_cons, List.map_nil, tagMBO] at h1
    linarith [h1, hset1]
  refine ⟨innerGameG_conditionallyEquivalent_innerRefT, innerGameG_gameEquivalent_innerGameH,
    innerGameG_ne_innerGameH,
    GameEquivalence.attach_gameEquivalent adaptiveConverter innerGameG_gameEquivalent_innerGameH,
    href0, href1, hunset0, hunset1, ?_⟩
  intro hce
  have h0 := hce [(⟨(), ()⟩, ⟨(), false⟩)]
  have h1 := hce [(⟨(), ()⟩, ⟨(), true⟩)]
  simp only [List.map_cons, List.map_nil] at h0 h1
  rw [hunset0, href0] at h0
  rw [hunset1, href1] at h1
  linarith

end Regression

#print axioms SystemAlgebra.RandomSystem.GameEquivalent.attach_liftMBO
#print axioms SystemAlgebra.TypedConverter.attachGame_gameEquivalent
#print axioms ConstructiveCryptography.GameEquivalence.attach_gameEquivalent
#print axioms ConstructiveCryptography.GameEquivalence.attach_id_gameEquivalent
#print axioms ConstructiveCryptography.GameEquivalence.attach_comp_gameEquivalent
#print axioms ConstructiveCryptography.GameEquivalence.win_attach_eq
#print axioms ConstructiveCryptography.GameEquivalence.advantage_attach_le_win
#print axioms SystemAlgebra.Interface.gameEquivalence
#print axioms SystemAlgebra.Interface.compatibleGameEquivalence
#print axioms Tests.GameEquivalenceTransport.regression_gameEquivalent_not_conditionallyEquivalent

end Tests.GameEquivalenceTransport
