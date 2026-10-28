import RandomSystems.Cumulative.CumulativeOperations

/-!
# Finite independent parallel random systems

A finite family of systems with disjoint tagged alphabets has the product mass on each
consistent interleaving. The component domain checks the selected query and bounds every
other component. This is the cumulative systems layer of n-ary parallel composition.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” The ordered component tags here make that finite parallel view
explicit at the random-system carrier.

## Main definitions

* `Domain.parallelAll`: the tagged component domain
* `RandomSystem.parallelAll`: independent cumulative product
* `parallelAllInputs`: the corresponding input-history domain

## Main results

* `RandomSystem.parallelAll_mass`: the product mass of a consistent interleaving
* `RandomSystem.replies_parAll_iff`: a complete transcript is an interleaving of
  component transcripts
-/

namespace SystemAlgebra

open Probability
open scoped NNReal

variable {K : Type} [Fintype K] [DecidableEq K]


/-! ## Random systems -/

namespace RandomSystem

variable {A B : K → Type}

open Classical in
/-- The exchanges of component `k` of a history, with their tags removed. -/
noncomputable def restrictExchanges (k : K) (h : List ((Σ k, A k) × (Σ k, B k))) :
    List (A k × B k) :=
  h.filterMap fun z =>
    if hx : z.1.1 = k then
      if hy : z.2.1 = k then some (hx ▸ z.1.2, hy ▸ z.2.2) else none
    else none


open Classical in
/-- Every exchange is with one component: its input and its reply carry the same tag. -/
def parallelAllConsistent (h : List ((Σ k, A k) × (Σ k, B k))) : Prop :=
  ∀ z ∈ h, z.1.1 = z.2.1

omit [Fintype K] in
open Classical in
lemma restrictExchanges_cons_self (k : K) (h : List ((Σ k, A k) × (Σ k, B k))) (a : A k)
    (b : B k) : restrictExchanges k ((⟨k, a⟩, ⟨k, b⟩) :: h) = (a, b) :: restrictExchanges k h := by
  simp [restrictExchanges]

omit [Fintype K] in
open Classical in
lemma restrictExchanges_cons_of_ne {k k₀ : K} (hk : k₀ ≠ k)
    (h : List ((Σ k, A k) × (Σ k, B k))) (a : A k₀) (b : B k₀) :
    restrictExchanges k ((⟨k₀, a⟩, ⟨k₀, b⟩) :: h) = restrictExchanges k h := by
  simp [restrictExchanges, hk]


omit [Fintype K] [DecidableEq K] in
open Classical in
lemma parallelAllConsistent_snoc {h : List ((Σ k, A k) × (Σ k, B k))} {z} :
    parallelAllConsistent (h ++ [z]) ↔ parallelAllConsistent h ∧ z.1.1 = z.2.1 := by
  simp [parallelAllConsistent, or_imp, forall_and]

open Classical in
/-- A consistent history splits into the exchanges of its components. -/
lemma length_eq_sum_of_parallelAllConsistent {h : List ((Σ k, A k) × (Σ k, B k))}
    (hh : parallelAllConsistent h) :
    h.length = ∑ k, (restrictExchanges k h).length := by
  induction h with
  | nil => simp [restrictExchanges]
  | cons z h ih =>
    have hz := hh z List.mem_cons_self
    have ht : parallelAllConsistent h := fun a ha => hh a (List.mem_cons_of_mem _ ha)
    have hk : ∀ k, (restrictExchanges k (z :: h)).length =
        (restrictExchanges k h).length + if z.1.1 = k then 1 else 0 := by
      intro k
      by_cases hx : z.1.1 = k
      · have hy : z.2.1 = k := hz ▸ hx
        simp [restrictExchanges, hx, hy]
      · simp [restrictExchanges, hx]
    rw [List.length_cons, ih ht]
    simp only [hk, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [Fintype K] in
open Classical in
/-- On a consistent history, the queries of component `k`'s exchanges are the history's
inputs restricted to `k`. -/
lemma restrictExchanges_queries {h : List ((Σ k, A k) × (Σ k, B k))}
    (hh : parallelAllConsistent h) (k : K) :
    (restrictExchanges k h).map Prod.fst = restrict k (h.map Prod.fst) := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    have hz := hh z List.mem_cons_self
    have ht : parallelAllConsistent h := fun a ha => hh a (List.mem_cons_of_mem _ ha)
    obtain ⟨⟨kx, x⟩, ⟨ky, y⟩⟩ := z
    simp only at hz
    subst hz
    by_cases hk : kx = k
    · subst hk
      simp [restrictExchanges, restrict_cons_self, ← ih ht]
    · simp only [restrictExchanges] at ih ⊢
      simp [restrict_cons_ne hk, hk, ih ht]

end RandomSystem

open Classical in
/-- The domain of an n-ary parallel composition: a consistent transcript, the queried
component admitting the query, and every other component within its bound. Jost, Thesis,
printed p. 17: “A finite set of resources with disjoint interface sets can be viewed as a
single one.” The tagged family keeps the component domain of each query explicit. -/
noncomputable def Domain.parallelAll {A B : K → Type} (D : ∀ k, Domain (A k) (B k)) :
    Domain (Σ k, A k) (Σ k, B k) where
  admits h x := RandomSystem.parallelAllConsistent h ∧
    (∀ k, k ≠ x.1 → (RandomSystem.restrictExchanges k h).length ≤ (D k).bound) ∧
    D x.1 (RandomSystem.restrictExchanges x.1 h) x.2
  bound := ∑ k, (D k).bound
  length_lt h x hx := by
    -- The queried component is strictly below its bound; every other one is at most its bound.
    rw [RandomSystem.length_eq_sum_of_parallelAllConsistent hx.1]
    apply Finset.sum_lt_sum
    · intro k _
      by_cases hk : k = x.1
      · subst hk
        exact le_of_lt ((D _).length_lt _ _ hx.2.2)
      · exact hx.2.1 k hk
    · exact ⟨x.1, Finset.mem_univ _, (D x.1).length_lt _ _ hx.2.2⟩

namespace RandomSystem

variable {A B : K → Type} [∀ k, Fintype (A k)] [∀ k, Fintype (B k)]
  {D : ∀ k, Domain (A k) (B k)}

open Classical in
/-- **Independent n-ary parallel composition** of random systems: on a consistent history,
the product of the components' masses on their restrictions. Jost, Thesis, printed p. 17:
“A finite set of resources with disjoint interface sets can be viewed as a single one.”
Independence is the chosen product construction, not implied by disjoint labels alone. -/
noncomputable def parallelAll (R : ∀ k, RandomSystem (A k) (B k) (D k)) :
    RandomSystem (Σ k, A k) (Σ k, B k) (Domain.parallelAll D) :=
  ⟨fun h => if parallelAllConsistent h then ∏ k, R k (restrictExchanges k h) else 0, by
    refine ⟨?_, ?_, fun h x => ?_⟩
    -- Empty mass and nonnegativity are inherited from the component masses.
    · simp [parallelAllConsistent, restrictExchanges, RandomSystem.mass_nil]
    · intro h
      dsimp only
      split_ifs
      · exact Finset.prod_nonneg fun k _ => (R k).mass_nonneg _
      · exact le_rfl
    · by_cases hh : parallelAllConsistent h
      swap
      -- An inconsistent history stays inconsistent after another exchange.
      · refine ⟨0, fun y => ?_, ?_⟩
        · have hn : ¬ parallelAllConsistent (h ++ [(x, y)]) :=
            fun h' => hh fun z hz => h' z (List.mem_append_left _ hz)
          simp [hn]
        · simp [hh, Distribution.weight]
      obtain ⟨k₀, x₀⟩ := x
      -- Extend only component `k₀`; all other masses are fixed scalar factors.
      refine ⟨(∏ k ∈ Finset.univ.erase k₀, R k (restrictExchanges k h)) •
          Distribution.fTransform (fun y : B k₀ => (⟨k₀, y⟩ : Σ k, B k))
            ((R k₀).extensionLaw (restrictExchanges k₀ h) x₀), ?_, ?_⟩
      · rintro ⟨k₁, y₁⟩
        by_cases hk : k₁ = k₀
        -- A correctly tagged reply extends exactly the selected component history.
        · subst hk
          rw [Finsupp.smul_apply, smul_eq_mul,
            Distribution.fTransform_injective_apply _ _ (by intro a b h; simpa using h),
            extensionLaw_apply]
          have hc : parallelAllConsistent (h ++ [((⟨k₁, x₀⟩ : Σ k, A k), (⟨k₁, y₁⟩ : Σ k, B k))])
            := by
            intro z hz
            rcases List.mem_append.mp hz with hz | hz
            · exact hh z hz
            · rw [List.mem_singleton.mp hz]
          beta_reduce
          rw [if_pos hc, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k₁)]
          congr 1
          · refine Finset.prod_congr rfl fun k hk' => ?_
            have hne : k₁ ≠ k := fun he => (Finset.mem_erase.mp hk').1 he.symm
            simp [restrictExchanges, List.filterMap_append, hne]
          · simp [restrictExchanges, List.filterMap_append]
        -- A reply tagged with another component has zero mass.
        · have hz : Distribution.fTransform (fun y : B k₀ => (⟨k₀, y⟩ : Σ k, B k))
              ((R k₀).extensionLaw (restrictExchanges k₀ h) x₀) ⟨k₁, y₁⟩ = 0 :=
            Finsupp.mapDomain_of_notMem_range _ _ (by
              rintro ⟨b, hb⟩
              exact hk (congrArg Sigma.fst hb).symm)
          have hn : ¬ parallelAllConsistent
              (h ++ [((⟨k₀, x₀⟩ : Σ k, A k), (⟨k₁, y₁⟩ : Σ k, B k))]) :=
            fun h' => hk (h' _ (List.mem_append_right _ (List.mem_singleton_self _))).symm
          rw [Finsupp.smul_apply, smul_eq_mul, hz, mul_zero]
          simp [hn]
      -- The extension weight is the previous product on admitted queries.
      · unfold Distribution.weight at ⊢
        rw [Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]
        change (∏ k ∈ Finset.univ.erase k₀, R k (restrictExchanges k h)) *
          (Distribution.fTransform (fun y : B k₀ => (⟨k₀, y⟩ : Σ k, B k))
            ((R k₀).extensionLaw (restrictExchanges k₀ h) x₀)).weight = _
        rw [Distribution.weight_fTransform, extensionLaw_weight]
        by_cases hb : ∀ k, k ≠ k₀ → (restrictExchanges k h).length ≤ (D k).bound
        · have hadm : (Domain.parallelAll D).admits h ⟨k₀, x₀⟩ ↔
              D k₀ (restrictExchanges k₀ h) x₀ :=
            ⟨fun h' => h'.2.2, fun h' => ⟨hh, hb, h'⟩⟩
          by_cases hd : D k₀ (restrictExchanges k₀ h) x₀
          · beta_reduce
            rw [if_pos hd, if_pos (hadm.mpr hd), if_pos hh,
              ← Finset.prod_erase_mul _ _ (Finset.mem_univ k₀)]
          · rw [if_neg hd, if_neg (fun h' => hd (hadm.mp h'))]
            simp
        -- An exhausted other component already has zero cumulative mass.
        · push Not at hb
          obtain ⟨k, hk, hlt⟩ := hb
          rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
              ((R k).mass_eq_zero_of_bound_lt hlt), zero_mul,
            if_neg (fun h' => (not_le.mpr hlt) (h'.2.1 k hk))]⟩

open Classical in
lemma parallelAll_mass (R : ∀ k, RandomSystem (A k) (B k) (D k))
    (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelAll R h =
      if parallelAllConsistent h then ∏ k, R k (restrictExchanges k h) else 0 := rfl

end RandomSystem

/-! ## Domains -/

open Classical in
/-- The n-ary parallel input domain: a nonempty history whose restriction to each component
is empty or lies in that component's domain. Jost, Thesis, printed p. 17: “A finite set of
resources with disjoint interface sets can be viewed as a single one.” -/
def parallelAllInputs {I : K → Type} {F : ∀ k, I k → Type}
    (E : ∀ k, List (Σ i, F k i) → Prop) (h : List (Σ l : Σ k, I k, F l.1 l.2)) : Prop :=
  h ≠ [] ∧ ∀ k,
    restrict k (h.map (Equiv.sigmaAssoc F)) = [] ∨ E k (restrict k (h.map (Equiv.sigmaAssoc F)))

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma parallelAllInputs_nonempty_prefix {I : K → Type} {F : ∀ k, I k → Type}
    {E : ∀ k, List (Σ i, F k i) → Prop}
    (hE : ∀ k, ∀ {p h}, p <+: h → p ≠ [] → E k h → E k p) :
    ¬ parallelAllInputs E [] ∧
      ∀ {p h}, p <+: h → p ≠ [] → parallelAllInputs E h → parallelAllInputs E p := by
  refine ⟨fun h => h.1 rfl, fun {p h} hp hn hd => ⟨hn, fun k => ?_⟩⟩
  have hpre := restrict_prefix k (hp.map (Equiv.sigmaAssoc F))
  by_cases he : restrict k (p.map (Equiv.sigmaAssoc F)) = []
  · exact Or.inl he
  · exact Or.inr (hE k hpre he
      ((hd.2 k).resolve_left fun hz => he (List.eq_nil_of_prefix_nil (hz ▸ hpre))))

omit [DecidableEq K] in
open Classical in
lemma parallelAllInputs_length_le {I : K → Type} {F : ∀ k, I k → Type}
    {E : ∀ k, List (Σ i, F k i) → Prop} {m : K → ℕ} (hE : ∀ k h, E k h → h.length ≤ m k) :
    ∀ h, parallelAllInputs E h → h.length ≤ ∑ k, m k := by
  intro h hh
  have hl := (length_eq_sum_restrict (h.map (Equiv.sigmaAssoc F))).symm
  rw [List.length_map] at hl
  rw [← hl]
  refine Finset.sum_le_sum fun k _ => ?_
  rcases hh.2 k with he | he
  · rw [he]
    exact Nat.zero_le _
  · exact hE k _ he

/-! ## Transcripts of `parAll` -/

namespace RandomSystem

variable {A B : K → Type}

omit [Fintype K] in
open Classical in
/-- On a consistent history, the replies of component `k`'s exchanges are the history's
replies restricted to `k`. -/
lemma restrictExchanges_snd {h : List ((Σ k, A k) × (Σ k, B k))}
    (hh : parallelAllConsistent h) (k : K) :
    (restrictExchanges k h).map Prod.snd = restrict k (h.map Prod.snd) := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    have hz := hh z List.mem_cons_self
    have ht : parallelAllConsistent h := fun a ha => hh a (List.mem_cons_of_mem _ ha)
    obtain ⟨⟨kx, x⟩, ⟨ky, y⟩⟩ := z
    simp only at hz
    subst hz
    by_cases hk : kx = k
    · subst hk
      simp [restrictExchanges, restrict_cons_self, ← ih ht]
    · simp only [restrictExchanges] at ih ⊢
      simp [restrict_cons_ne hk, hk, ih ht]

omit [Fintype K] in
open Classical in
/-- **The transcripts of `parAll`** are exactly the interleavings of the components'
transcripts. The n-ary form of `replies_pair_iff`. -/
lemma replies_parAll_iff (s : ∀ k, System (A k) (B k)) (h : List ((Σ k, A k) × (Σ k, B k))) :
    Replies (parAll s) (h.map Prod.fst) (h.map Prod.snd) ↔
      parallelAllConsistent h ∧
        ∀ k, Replies (s k) ((restrictExchanges k h).map Prod.fst)
          ((restrictExchanges k h).map Prod.snd) := by
  induction h using List.reverseRecOn with
  | nil => simp [parallelAllConsistent, restrictExchanges]
  | append_singleton h z ih =>
    -- A final tagged exchange changes one component and leaves every other projection fixed.
    obtain ⟨⟨kx, x⟩, ⟨ky, y⟩⟩ := z
    have hc : parallelAllConsistent (h ++ [((⟨kx, x⟩ : Σ k, A k), (⟨ky, y⟩ : Σ k, B k))]) ↔
        parallelAllConsistent h ∧ kx = ky := by
      simp [parallelAllConsistent, or_imp, forall_and]
    simp only [List.map_append, List.map_cons, List.map_nil, replies_snoc, ih, hc]
    by_cases hh : parallelAllConsistent h
    swap
    · simp [hh]
    by_cases hk : kx = ky
    · subst hk
      have hne : ∀ k, k ≠ kx →
          restrictExchanges k (h ++ [((⟨kx, x⟩ : Σ k, A k), (⟨kx, y⟩ : Σ k, B k))]) =
            restrictExchanges k h := by
        intro k hk
        simp [restrictExchanges, List.filterMap_append, Ne.symm hk]
      have hself : restrictExchanges kx (h ++ [((⟨kx, x⟩ : Σ k, A k), (⟨kx, y⟩ : Σ k, B k))]) =
          restrictExchanges kx h ++ [(x, y)] := by
        simp [restrictExchanges, List.filterMap_append]
      have hmap : parAll s (h.map Prod.fst ++ [⟨kx, x⟩]) = Part.some ⟨kx, y⟩ ↔
          s kx ((restrictExchanges kx h).map Prod.fst ++ [x]) = Part.some y := by
        rw [parAll_snoc, ← restrictExchanges_queries hh kx]
        simp [Part.eq_some_iff, Part.mem_map_iff]
      rw [hmap]
      constructor
      · rintro ⟨⟨-, hall⟩, hs⟩
        refine ⟨⟨hh, rfl⟩, fun k => ?_⟩
        by_cases hkk : k = kx
        · subst hkk
          rw [hself, List.map_append, List.map_append, List.map_singleton, List.map_singleton]
          exact replies_snoc.mpr ⟨hall k, hs⟩
        · rw [hne k hkk]
          exact hall k
      · rintro ⟨-, hall⟩
        have hkx := hall kx
        rw [hself, List.map_append, List.map_append, List.map_singleton, List.map_singleton] at hkx
        obtain ⟨hkx, hs⟩ := replies_snoc.mp hkx
        refine ⟨⟨hh, fun k => ?_⟩, hs⟩
        by_cases hkk : k = kx
        · subst hkk
          exact hkx
        · have hk' := hall k
          rw [hne k hkk] at hk'
          exact hk'
    · have hn : ¬ parAll s (h.map Prod.fst ++ [⟨kx, x⟩]) = Part.some ⟨ky, y⟩ := by
        rw [parAll_snoc]
        intro he
        obtain ⟨w, -, hw⟩ := (Part.mem_map_iff _).mp (Part.eq_some_iff.mp he)
        exact hk (congrArg Sigma.fst hw)
      simp [hn, hk]

end RandomSystem

end SystemAlgebra
