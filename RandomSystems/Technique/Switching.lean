/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Technique.BlindWinning
import RandomSystems.System.RandomObjects

/-!
# The URF--URP switching lemma

CR18-FALLBACK application: Cachin--Renner(--Maurer), *Lecture Notes on
Cryptography*, Section 4.11.3, Definition 4.22 and Lemmas 4.18--4.19,
printed p. 111, read on the rendered page.

The proof follows the printed comparison spine: adjoin the output-collision
condition to the uniform random function, establish conditional equivalence
with the uniform random permutation, reduce distinguishing advantage to blind
winning, and apply the birthday bound.  The named objects are the internal
\`PDS.urf\` and \`PDS.urp\`; the query cap is the internal
\`System.filterQueries\`; and the distance is \`PDS.advFullyDefined\`.
No external Random Systems library enters.

The final theorem proves the sharper \`q(q-1)/(2|X|)\` form, hence CR18's
displayed \`q^2/(2|X|)\` bound.  It needs no public \`q <= |X|\` side
condition: the actual queried set has size \`k <= |X|\`, so the birthday
bound applies at \`k\` and is then lifted along \`k <= q\`.
-/


namespace RandomSystems.Switching

open Probability (Distribution)

noncomputable section

/-- The collision mass of a uniform function on a finite queried set is at
most the sharp birthday bound for the size of that set. -/
theorem uniform_function_collision_on_finset_le
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (S : Finset X) :
    (Distribution.uniform (X → X)).mass
        (fun f => ¬ Set.InjOn f (fun x => x ∈ S)) ≤
      (S.card : ℝ) * ((S.card : ℝ) - 1) /
        (2 * (Fintype.card X : ℝ)) := by
  classical
  let N := Fintype.card X
  let k := S.card
  have hN : 0 < N := Fintype.card_pos
  have hk : k ≤ N := by
    dsimp [k, N]
    exact Finset.card_le_univ S
  have hgoodCard := Probability.Counting.card_function_injOn_finset (Y := X) S
  have hgood :
      (Distribution.uniform (X → X)).mass
          (fun f => Set.InjOn f (fun x => x ∈ S)) =
        (N.descFactorial k : ℝ) / (N : ℝ) ^ k := by
    rw [Distribution.uniform_mass_eq_card_filter, hgoodCard, Fintype.card_fun]
    push_cast
    dsimp [N, k] at *
    have hpow : (Fintype.card X : ℝ) ^ Fintype.card X =
        (Fintype.card X : ℝ) ^ (Fintype.card X - S.card) *
          (Fintype.card X : ℝ) ^ S.card := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [hpow]
    field_simp
  have hsplit := Distribution.mass_add_compl
    (Distribution.uniform (X → X)) (fun f => Set.InjOn f (fun x => x ∈ S))
  have hweight : (Distribution.uniform (X → X)).weight = 1 :=
    Distribution.uniform_isProbDist.weight_eq
  rw [hweight] at hsplit
  have hbad :
      (Distribution.uniform (X → X)).mass
          (fun f => ¬ Set.InjOn f (fun x => x ∈ S)) =
        1 - (N.descFactorial k : ℝ) / (N : ℝ) ^ k := by
    rw [hgood] at hsplit
    linarith
  rw [hbad]
  rw [Probability.Counting.cast_descFactorial_eq_prod hk]
  exact Probability.Counting.birthday_bound hk hN

/-- CR18 Example 4.15's monotone condition: two distinct queried inputs have
the same output. -/
noncomputable def collisionCondition {X : Type*} [DecidableEq X]
    (s : System.DDS X X) :
    System.MonotoneCondition X :=
  ⟨{l | ¬ Set.InjOn (fun x => System.answer s [] x) (fun x => x ∈ l.toFinset)}, by
    intro l l' hpre hbad hinj
    apply hbad
    exact hinj.mono fun x hx => by
      change x ∈ l.toFinset at hx
      change x ∈ l'.toFinset
      rw [List.mem_toFinset] at hx ⊢
      exact hpre.subset hx⟩

/-- On a function evaluator, the collision condition is precisely failure of
injectivity on the queried finite set. -/
@[simp] theorem collisionCondition_functionEvaluator_mem_iff
    {X : Type*} [DecidableEq X] (f : X → X) (l : List X) :
    l ∈ (collisionCondition (System.functionEvaluator f)).1 ↔
      ¬ Set.InjOn f (fun x => x ∈ l.toFinset) := by
  classical
  simp only [collisionCondition, Set.mem_setOf_eq, PDS.answer_functionEvaluator]
  constructor
  · intro h hf
    apply h
    intro a ha b hb hab
    exact hf ha hb (Option.some.inj hab)
  · intro h hsome
    apply h
    intro a ha b hb hab
    exact hsome ha hb (congrArg some hab)

/-- A uniform function conditioned to be injective on the queried set has the
same queried-set fiber law as a uniform permutation.  Using a finite set
rather than a tuple handles repeated queries without a separate case. -/
theorem uniform_function_agree_and_injOn_eq_perm_agree_mul_injOn
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (S : Finset X) (g : S → X) :
    (Distribution.uniform (X → X)).mass
        (fun f => (∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S)) =
      (Distribution.uniform (Equiv.Perm X)).mass (fun σ => ∀ x : S, σ x.1 = g x) *
        (Distribution.uniform (X → X)).mass
          (fun f => Set.InjOn f (fun x => x ∈ S)) := by
  classical
  rw [Distribution.uniform_mass_eq_card_filter,
    Distribution.uniform_mass_eq_card_filter,
    Distribution.uniform_mass_eq_card_filter]
  by_cases hg : Function.Injective g
  · have hleft_set : ((Finset.univ : Finset (X → X)).filter
        (fun f => (∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S))) =
      ((Finset.univ : Finset (X → X)).filter (fun f => ∀ x : S, f x.1 = g x)) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact h.1
      · intro h
        refine ⟨h, ?_⟩
        intro a ha b hb hab
        have hgab : g ⟨a, ha⟩ = g ⟨b, hb⟩ := by
          rw [← h ⟨a, ha⟩, ← h ⟨b, hb⟩, hab]
        exact congrArg Subtype.val (hg hgab)
    have hperm_card : ((Finset.univ : Finset (Equiv.Perm X)).filter
          (fun σ => ∀ x : S, σ x.1 = g x)).card =
        (Fintype.card X - S.card).factorial := by
      simpa using Probability.Counting.card_perm_fiber_finset S ⟨g, hg⟩
    rw [hleft_set, Probability.Counting.card_function_fiber_finset S g,
      hperm_card, Probability.Counting.card_function_injOn_finset S]
    rw [Fintype.card_fun, Fintype.card_perm]
    have hle : S.card ≤ Fintype.card X := Finset.card_le_univ S
    have hfact : (Fintype.card X - S.card).factorial *
        (Fintype.card X).descFactorial S.card = (Fintype.card X).factorial :=
      Nat.factorial_mul_descFactorial hle
    have hfact_ne : (((Fintype.card X - S.card).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos (Fintype.card X - S.card)).ne'
    have hdesc_ne : (((Fintype.card X).descFactorial S.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hle).ne'
    rw [← hfact]
    field_simp [hfact_ne, hdesc_ne]
    push_cast
    ring
  · have hnoneF : ∀ f : X → X,
        ¬ ((∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S)) := by
      intro f hf
      apply hg
      intro x y hxy
      apply Subtype.ext
      exact hf.2 x.2 y.2 (by rw [hf.1 x, hf.1 y, hxy])
    have hL : ((Finset.univ : Finset (X → X)).filter
        (fun f => (∀ x : S, f x.1 = g x) ∧ Set.InjOn f (fun x => x ∈ S))).card = 0 := by
      rw [Finset.card_eq_zero]
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hf
        exact False.elim (hnoneF f hf)
      · intro hf
        simp at hf
    have hnoneP : ∀ σ : Equiv.Perm X, ¬ (∀ x : S, σ x.1 = g x) := by
      intro σ hσ
      apply hg
      intro x y hxy
      apply Subtype.ext
      exact σ.injective (by rw [hσ x, hσ y, hxy])
    have hP : ((Finset.univ : Finset (Equiv.Perm X)).filter
        (fun σ => ∀ x : S, σ x.1 = g x)).card = 0 := by
      rw [Finset.card_eq_zero]
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hσ
        exact False.elim (hnoneP σ hσ)
      · intro hσ
        simp at hσ
    rw [hL, hP]
    simp

/-- CR18 Example 4.15: before an output collision, the URF is conditionally
equivalent to the URP. -/
theorem urf_collision_condEquiv_urp
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] :
    PDG.CondEquiv
      (PDS.adjoin (PDS.urf X X) collisionCondition).1
      (PDS.urp X) := by
  classical
  intro l
  ext t
  rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
    PDS.isProbDist_urp X |>.weight_eq, one_mul,
    PDG.notWonLaw_apply, PDG.notWonMass_playQueries_eq_mass,
    PDS.trLawFullyDefined]
  simp only [PDS.coe_adjoin, PDS.urf, PDS.urp]
  rw [Distribution.mass_fTransform, Distribution.mass_fTransform,
    Distribution.fTransform_fTransform, Distribution.fTransform_apply_eq_mass]
  rw [Distribution.mass_fTransform, Distribution.mass_fTransform]
  simp only [Function.comp_apply, System.Won,
    System.keptPrefix_functionEvaluator,
    collisionCondition_functionEvaluator_mem_iff,
    System.transcript_functionEvaluator_playQueries_length]
  simp only [not_not]
  simp only [System.answeredQueries, List.filterMap_map]
  simp only [Function.comp_apply, Option.map_some, List.filterMap_some]
  by_cases ht : ∃ f₀ : X → X, l.map (fun x => (x, some (f₀ x))) = t
  · obtain ⟨f₀, rfl⟩ := ht
    let S : Finset X := l.toFinset
    let g : S → X := fun x => f₀ x.1
    have htranscript_iff : ∀ f : X → X,
        l.map (fun x => (x, some (f x))) = l.map (fun x => (x, some (f₀ x))) ↔
          ∀ x : S, f x.1 = g x := by
      intro f
      constructor
      · intro h x
        have hx : x.1 ∈ l := by
          exact List.mem_toFinset.mp x.2
        have hp := List.map_inj_left.mp h x.1 hx
        exact Option.some.inj (congrArg Prod.snd hp)
      · intro h
        apply List.map_inj_left.mpr
        intro x hx
        exact Prod.ext rfl (congrArg some (h ⟨x, List.mem_toFinset.mpr hx⟩))
    calc
      (Distribution.uniform (X → X)).mass
          (fun f => Set.InjOn f (fun x => x ∈ l.toFinset) ∧
            l.map (fun x => (x, some (f x))) = l.map (fun x => (x, some (f₀ x)))) =
        (Distribution.uniform (X → X)).mass
          (fun f => (∀ x : S, f x.1 = g x) ∧
            Set.InjOn f (fun x => x ∈ S)) := by
              apply Distribution.mass_congr
              intro f
              dsimp [S]
              rw [and_comm, htranscript_iff f]
      _ = (Distribution.uniform (Equiv.Perm X)).mass
            (fun σ => ∀ x : S, σ x.1 = g x) *
          (Distribution.uniform (X → X)).mass
            (fun f => Set.InjOn f (fun x => x ∈ S)) :=
        uniform_function_agree_and_injOn_eq_perm_agree_mul_injOn S g
      _ = (Distribution.uniform (X → X)).mass
            (fun f => Set.InjOn f (fun x => x ∈ l.toFinset)) *
          (Distribution.uniform (Equiv.Perm X)).mass
            (fun σ => l.map (fun x => (x, some (σ x))) =
              l.map (fun x => (x, some (f₀ x)))) := by
        rw [mul_comm]
        dsimp [S]
        congr 1
        apply Distribution.mass_congr
        intro σ
        exact (htranscript_iff (σ : X → X)).symm
  · have hF : (Distribution.uniform (X → X)).mass
        (fun f => Set.InjOn f (fun x => x ∈ l.toFinset) ∧
          l.map (fun x => (x, some (f x))) = t) = 0 := by
      apply Distribution.mass_eq_zero_of_forall_not
      intro f hf
      exact ht ⟨f, hf.2⟩
    have hP : (Distribution.uniform (Equiv.Perm X)).mass
        (fun σ => l.map (fun x => (x, some (σ x))) = t) = 0 := by
      apply Distribution.mass_eq_zero_of_forall_not
      intro σ hσ
      exact ht ⟨fun x => σ x, hσ⟩
    rw [hF, hP, mul_zero]

/-- CR18 Definition 3.10's query restriction, lifted to a typed PDS. -/
def limit {X : Type*} (q : ℕ) (S : PDS X X) : PDS X X :=
  Distribution.fTransform (System.filterQueries q) S

/-- Query restriction on a game, retaining the same monotone condition. -/
def limitGame {X : Type*} (q : ℕ) (G : PDG X X) : PDG X X :=
  Distribution.fTransform
    (fun γ : System.DDG X X => (System.filterQueries q γ.1, γ.2)) G

/-- The blind winning probability of the filtered URF collision game is at
most the birthday bound. -/
theorem blindSupWinProb_limit_urf_collision_le
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    PDG.blindSupWinProb
        (limitGame q (PDS.adjoin (PDS.urf X X) collisionCondition).1) ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * (Fintype.card X : ℝ)) := by
  classical
  refine PDG.blindSupWinProb_le_of_forall ?_
  intro e he n
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  let f₀ : X → X := fun _ => x₀
  let L : List X := System.answeredQueries
    (System.DDE.Total.transcript
      (System.filterQueries q (System.functionEvaluator f₀)) e n)
  have hqueries : ∀ f : X → X,
      System.answeredQueries
          (System.DDE.Total.transcript
            (System.filterQueries q (System.functionEvaluator f)) e n) = L := by
    intro f
    dsimp [L]
    rw [System.DDE.Total.answeredQueries_transcript,
      System.DDE.Total.answeredQueries_transcript,
      System.keptPrefix_filterQueries, System.keptPrefix_filterQueries,
      System.keptPrefix_functionEvaluator, System.keptPrefix_functionEvaluator,
      System.transcriptInputs_congr_of_nonAdaptive he]
  have hLlen : L.length ≤ q := by
    dsimp [L]
    rw [System.DDE.Total.answeredQueries_transcript,
      System.keptPrefix_filterQueries, System.keptPrefix_functionEvaluator]
    exact List.length_take_le q _
  have hmass :
      PDG.winningMass e n
          (limitGame q (PDS.adjoin (PDS.urf X X) collisionCondition).1) =
        (Distribution.uniform (X → X)).mass
          (fun f => ¬ Set.InjOn f (fun x => x ∈ L.toFinset)) := by
    unfold PDG.winningMass limitGame
    simp only [PDS.coe_adjoin, PDS.urf]
    rw [Distribution.mass_fTransform, Distribution.mass_fTransform,
      Distribution.mass_fTransform]
    apply Distribution.mass_congr
    intro f
    simp only [System.Won]
    rw [hqueries f, collisionCondition_functionEvaluator_mem_iff]
  rw [hmass]
  refine le_trans (uniform_function_collision_on_finset_le L.toFinset) ?_
  have hkq : L.toFinset.card ≤ q :=
    (List.toFinset_card_le L).trans hLlen
  have hnum : (L.toFinset.card : ℝ) * ((L.toFinset.card : ℝ) - 1) ≤
      (q : ℝ) * ((q : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos L.toFinset.card with hk | hk
    · rw [hk]
      rcases q with _ | q
      · norm_num
      · have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
        push_cast
        nlinarith
    · have hkR : (1 : ℝ) ≤ L.toFinset.card := by exact_mod_cast hk
      have hkqR : (L.toFinset.card : ℝ) ≤ q := by exact_mod_cast hkq
      nlinarith
  gcongr

/-- Filtering preserves the URF/URP conditional equivalence because every
unfiltered URF and URP atom answers every query. -/
theorem limit_urf_collision_condEquiv_limit_urp
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    PDG.CondEquiv
      (limitGame q (PDS.adjoin (PDS.urf X X) collisionCondition).1)
      (limit q (PDS.urp X)) := by
  classical
  refine PDG.condEquiv_filterQueries q ?_ ?_ (urf_collision_condEquiv_urp X)
  · intro γ hγ l x
    simp only [PDS.coe_adjoin, PDS.urf] at hγ
    obtain ⟨s, hs, rfl⟩ :=
      Distribution.exists_mem_support_of_mem_support_fTransform _ _ hγ
    obtain ⟨f, _hf, rfl⟩ :=
      Distribution.exists_mem_support_of_mem_support_fTransform _ _ hs
    rw [PDS.answer_functionEvaluator]
    simp
  · intro s hs l x
    simp only [PDS.urp] at hs
    obtain ⟨π, _hπ, rfl⟩ :=
      Distribution.exists_mem_support_of_mem_support_fTransform _ _ hs
    rw [PDS.answer_functionEvaluator]
    simp

/-- Forgetting the condition after filtering an adjoined game gives exactly
the filtered underlying system. -/
theorem forget_limitGame_adjoin
    {X : Type*} (q : ℕ) (S : PDS X X)
    (A : System.DDS X X → System.MonotoneCondition X) :
    PDG.forget (limitGame q (PDS.adjoin S A).1) = limit q S := by
  unfold PDG.forget limitGame limit
  simp only [PDS.coe_adjoin, Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  intro s _hs
  rfl

/-- **CR18 Lemma 4.19, general finite-alphabet form.**  A uniform random
function and uniform random permutation, each restricted to `q` queries, have
distinguishing advantage at most `q(q-1)/(2|X|)`. -/
theorem urf_urp_switching
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : ℕ) :
    PDS.advFullyDefined
        (Distribution.fTransform (System.filterQueries q) (PDS.urf X X))
        (Distribution.fTransform (System.filterQueries q) (PDS.urp X)) ≤
      ENNReal.ofReal
        ((q : ℝ) * ((q : ℝ) - 1) / (2 * (Fintype.card X : ℝ))) := by
  classical
  change PDS.advFullyDefined (limit q (PDS.urf X X)) (limit q (PDS.urp X)) ≤ _
  let G : PDG X X := (PDS.adjoin (PDS.urf X X) collisionCondition).1
  let Gq : PDG X X := limitGame q G
  let Pq : PDS X X := limit q (PDS.urp X)
  have hG : Gq.NonNeg := by
    dsimp [Gq, G, limitGame]
    exact (PDS.nonNeg_adjoin (PDS.isProbDist_urf X X).nonNeg collisionCondition).fTransform _
  have hP : Pq.NonNeg := by
    dsimp [Pq, limit]
    exact (PDS.isProbDist_urp X).nonNeg.fTransform _
  have hw : Gq.weight = Pq.weight := by
    dsimp [Gq, G, Pq, limitGame, limit]
    simp only [Distribution.weight_fTransform]
    rw [PDS.isProbDist_urf X X |>.weight_eq, PDS.isProbDist_urp X |>.weight_eq]
  have hCE : PDG.CondEquiv Gq Pq := by
    exact limit_urf_collision_condEquiv_limit_urp X q
  calc
    PDS.advFullyDefined (limit q (PDS.urf X X)) Pq =
        PDS.advFullyDefined (PDG.forget Gq) Pq := by
      rw [show PDG.forget Gq = limit q (PDS.urf X X) by
        exact forget_limitGame_adjoin q (PDS.urf X X) collisionCondition]
    _ ≤ ENNReal.ofReal (PDG.blindSupWinProb Gq) :=
      PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv hG hP hw hCE
    _ ≤ ENNReal.ofReal
          ((q : ℝ) * ((q : ℝ) - 1) / (2 * (Fintype.card X : ℝ))) :=
      ENNReal.ofReal_le_ofReal (blindSupWinProb_limit_urf_collision_le X q)

end

end RandomSystems.Switching
