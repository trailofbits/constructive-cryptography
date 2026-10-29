import RandomSystems.Cumulative.CumulativeOperations

/-!
# Finite independent parallel random systems

The independent parallel composition of a finite family `R k : RandomSystem (A k) (B k) (D k)`,
`k ∈ K`, on the tagged alphabets `Σ k, A k` and `Σ k, B k`. A tag names a component; `K` carries
no order. Writing `h|k` for the exchanges of `h` tagged `k`, with the tags removed,

  `(parallelAll R) h = ∏ k, R k (h|k)` if every exchange of `h` has equal input and reply tags,
  `(parallelAll R) h = 0` otherwise.

```text
        k₁(x) ──▶ ┌──────┐
       k₁ ⇒ y ◀── │ R k₁ │   sees h|k₁
                  └──────┘
  D        ⋮          ⋮       one box per tag k ∈ K, no shared randomness
        k₂(x') ─▶ ┌──────┐
      k₂ ⇒ y' ◀── │ R k₂ │   sees h|k₂
                  └──────┘

  h     = (k₁(a₁), k₁ ⇒ b₁) (k₂(a₂), k₂ ⇒ b₂) (k₁(a₃), k₁ ⇒ b₃)
  h|k₁  = (a₁, b₁) (a₃, b₃)          h|k₂ = (a₂, b₂)
  mass  = R k₁ (h|k₁) · R k₂ (h|k₂)
```

Independence is the chosen product formula; disjoint tags alone do not imply it. Each `A k`
and `B k` is finite, as the `RandomSystem` carrier requires; `K` is finite because the product
and the sum of the component query bounds range over it.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” The independent product is this repository's specialization of that
view to random systems.

## Main definitions

* `RandomSystem.restrictExchanges k h`: the projection `h|k`
* `Domain.parallelAll D`: query `⟨k, x⟩` admitted when `D k` admits `x` after `h|k` and every
  other component is within its bound; total bound `∑ k, (D k).bound`
* `RandomSystem.parallelAll R`: the independent product above
* `parallelAllInputs E`: nonempty input histories whose every projection is empty or in `E k`

## Main results

* `RandomSystem.parallelAll_mass`: the defining product equation
* `RandomSystem.replies_parAll_iff`: a transcript of the deterministic `parAll s` is a
  tag-consistent interleaving of transcripts of the components `s k`
-/

namespace SystemAlgebra

open Probability
open scoped NNReal

variable {K : Type} [Fintype K] [DecidableEq K]


/-! ## Random systems -/

namespace RandomSystem

variable {A B : K → Type}

open Classical in
/-- **The projection `h|k`**: the exchanges `(⟨k, a⟩, ⟨k, b⟩)` of `h`, in order, as `(a, b)`.
An exchange whose input and reply tags differ is dropped; such histories have mass zero. -/
noncomputable def restrictExchanges (k : K) (h : List ((Σ k, A k) × (Σ k, B k))) :
    List (A k × B k) :=
  h.filterMap fun z =>
    if hx : z.1.1 = k then
      if hy : z.2.1 = k then some (hx ▸ z.1.2, hy ▸ z.2.2) else none
    else none


open Classical in
/-- **Tag consistency**: every exchange `(⟨k, x⟩, ⟨k', y⟩)` of `h` has `k = k'`, so each reply
comes from the queried component. -/
def parallelAllConsistent (h : List ((Σ k, A k) × (Σ k, B k))) : Prop :=
  ∀ z ∈ h, z.1.1 = z.2.1

omit [Fintype K] in
open Classical in
/-- `((⟨k, a⟩, ⟨k, b⟩) :: h)|k = (a, b) :: h|k`. -/
lemma restrictExchanges_cons_self (k : K) (h : List ((Σ k, A k) × (Σ k, B k))) (a : A k)
    (b : B k) : restrictExchanges k ((⟨k, a⟩, ⟨k, b⟩) :: h) = (a, b) :: restrictExchanges k h := by
  simp [restrictExchanges]

omit [Fintype K] in
open Classical in
/-- For `k₀ ≠ k`, `((⟨k₀, a⟩, ⟨k₀, b⟩) :: h)|k = h|k`. -/
lemma restrictExchanges_cons_of_ne {k k₀ : K} (hk : k₀ ≠ k)
    (h : List ((Σ k, A k) × (Σ k, B k))) (a : A k₀) (b : B k₀) :
    restrictExchanges k ((⟨k₀, a⟩, ⟨k₀, b⟩) :: h) = restrictExchanges k h := by
  simp [restrictExchanges, hk]


omit [Fintype K] [DecidableEq K] in
open Classical in
/-- `h ++ [z]` is consistent iff `h` is and `z` has equal input and reply tags. -/
lemma parallelAllConsistent_snoc {h : List ((Σ k, A k) × (Σ k, B k))} {z} :
    parallelAllConsistent (h ++ [z]) ↔ parallelAllConsistent h ∧ z.1.1 = z.2.1 := by
  simp [parallelAllConsistent, or_imp, forall_and]

open Classical in
/-- A consistent history splits into its projections: `|h| = ∑ k, |h|k|`. -/
lemma length_eq_sum_of_parallelAllConsistent {h : List ((Σ k, A k) × (Σ k, B k))}
    (hh : parallelAllConsistent h) :
    h.length = ∑ k, (restrictExchanges k h).length := by
  induction h with
  | nil => simp [restrictExchanges]
  | cons z h ih =>
    -- The consistent head exchange `z` adds one to the projection of its tag only.
    have hz := hh z List.mem_cons_self
    have ht : parallelAllConsistent h := fun a ha => hh a (List.mem_cons_of_mem _ ha)
    have hk : ∀ k, (restrictExchanges k (z :: h)).length =
        (restrictExchanges k h).length + if z.1.1 = k then 1 else 0 := by
      intro k
      by_cases hx : z.1.1 = k
      · have hy : z.2.1 = k := hz ▸ hx
        simp [restrictExchanges, hx, hy]
      · simp [restrictExchanges, hx]
    -- `|h| + 1 = ∑ k, |h|k| + ∑ k, [z.1.1 = k]`, and the indicator sum is `1`.
    rw [List.length_cons, ih ht]
    simp only [hk, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

omit [Fintype K] in
open Classical in
/-- On a consistent history, the inputs of `h|k` are the inputs of `h` restricted to `k`. -/
lemma restrictExchanges_queries {h : List ((Σ k, A k) × (Σ k, B k))}
    (hh : parallelAllConsistent h) (k : K) :
    (restrictExchanges k h).map Prod.fst = restrict k (h.map Prod.fst) := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    -- The head exchange has one tag `kx`; both sides keep it iff `kx = k`.
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
/-- **The domain of n-ary parallel composition.** After `h`, the query `⟨k₀, x⟩` is admitted iff
`h` is tag consistent, `|h|k| ≤ (D k).bound` for every `k ≠ k₀`, and `D k₀ (h|k₀) x`.
The bound is `∑ k, (D k).bound`: the queried projection is below its bound, the others are at
most theirs, and `|h| = ∑ k, |h|k|`. -/
noncomputable def Domain.parallelAll {A B : K → Type} (D : ∀ k, Domain (A k) (B k)) :
    Domain (Σ k, A k) (Σ k, B k) where
  admits h x := RandomSystem.parallelAllConsistent h ∧
    (∀ k, k ≠ x.1 → (RandomSystem.restrictExchanges k h).length ≤ (D k).bound) ∧
    D x.1 (RandomSystem.restrictExchanges x.1 h) x.2
  bound := ∑ k, (D k).bound
  length_lt h x hx := by
    -- `|h| = ∑ k, |h|k| < ∑ k, (D k).bound`: termwise `≤`, strict at the queried `x.1`.
    rw [RandomSystem.length_eq_sum_of_parallelAllConsistent hx.1]
    apply Finset.sum_lt_sum
    -- Termwise: the queried projection is below its bound, every other one at most its bound.
    · intro k _
      by_cases hk : k = x.1
      · subst hk
        exact le_of_lt ((D _).length_lt _ _ hx.2.2)
      · exact hx.2.1 k hk
    -- Strict at the queried component, since `D x.1` admits `x.2` after `h|x.1`.
    · exact ⟨x.1, Finset.mem_univ _, (D x.1).length_lt _ _ hx.2.2⟩

namespace RandomSystem

variable {A B : K → Type} [∀ k, Fintype (A k)] [∀ k, Fintype (B k)]
  {D : ∀ k, Domain (A k) (B k)}

open Classical in
/-- **Independent n-ary parallel composition** of random systems, on `Σ k, A k` and `Σ k, B k`
with domain `Domain.parallelAll D`: each query `⟨k, x⟩` goes to `R k`, which answers `⟨k, y⟩`
from its own history `h|k` and its own randomness, so
`(parallelAll R) h = ∏ k, R k (h|k)` on a tag-consistent `h`, and `0` otherwise.
Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” Independence is the chosen product; disjoint tags alone do not
imply it. -/
noncomputable def parallelAll (R : ∀ k, RandomSystem (A k) (B k) (D k)) :
    RandomSystem (Σ k, A k) (Σ k, B k) (Domain.parallelAll D) :=
  ⟨fun h => if parallelAllConsistent h then ∏ k, R k (restrictExchanges k h) else 0, by
    -- Normalization: mass `1` at `[]`, nonnegative masses, and for each `h` and query `x` a
    -- reply law `μ` with `μ y = mass (h ++ [(x, y)])` and weight `[x admitted after h] · mass h`.
    refine ⟨?_, ?_, fun h x => ?_⟩
    -- Empty mass: every projection of `[]` is `[]`, and `∏ k, R k [] = 1`.
    · simp [parallelAllConsistent, restrictExchanges, RandomSystem.mass_nil]
    -- Nonnegativity: a product of nonnegative component masses, or `0`.
    · intro h
      dsimp only
      split_ifs
      · exact Finset.prod_nonneg fun k _ => (R k).mass_nonneg _
      · exact le_rfl
    · by_cases hh : parallelAllConsistent h
      swap
      -- Inconsistent `h`: it stays inconsistent after any exchange, so the reply law is `0`,
      -- of weight `0 = mass h`.
      · refine ⟨0, fun y => ?_, ?_⟩
        · have hn : ¬ parallelAllConsistent (h ++ [(x, y)]) :=
            fun h' => hh fun z hz => h' z (List.mem_append_left _ hz)
          simp [hn]
        · simp [hh, Distribution.weight]
      obtain ⟨k₀, x₀⟩ := x
      -- Consistent `h`, query `⟨k₀, x₀⟩`: only component `k₀` moves. The reply law is
      --   μ = (∏ k ≠ k₀, R k (h|k)) · ⟨k₀, ·⟩₊ (extension law of `R k₀` at `h|k₀`, `x₀`),
      -- the finite reply law of `R k₀`, tagged `k₀`, times the fixed other masses.
      refine ⟨(∏ k ∈ Finset.univ.erase k₀, R k (restrictExchanges k h)) •
          Distribution.fTransform (fun y : B k₀ => (⟨k₀, y⟩ : Σ k, B k))
            ((R k₀).extensionLaw (restrictExchanges k₀ h) x₀), ?_, ?_⟩
      · rintro ⟨k₁, y₁⟩
        by_cases hk : k₁ = k₀
        -- Reply `⟨k₁, y₁⟩` with `k₁ = k₀`: `μ` gives
        --   (∏ k ≠ k₁, R k (h|k)) · R k₁ (h|k₁ ++ [(x₀, y₁)]),
        -- the product mass of the consistent `h ++ [(⟨k₁, x₀⟩, ⟨k₁, y₁⟩)]`.
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
          -- Split the extended product into the factors `k ≠ k₁` and the factor `k₁`.
          beta_reduce
          rw [if_pos hc, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k₁)]
          congr 1
          -- For `k ≠ k₁` the new exchange is not in `h|k`, so the factor is unchanged.
          · refine Finset.prod_congr rfl fun k hk' => ?_
            have hne : k₁ ≠ k := fun he => (Finset.mem_erase.mp hk').1 he.symm
            simp [restrictExchanges, List.filterMap_append, hne]
          -- For `k₁`: `(h ++ [(⟨k₁, x₀⟩, ⟨k₁, y₁⟩)])|k₁ = h|k₁ ++ [(x₀, y₁)]`.
          · simp [restrictExchanges, List.filterMap_append]
        -- Reply `⟨k₁, y₁⟩` with `k₁ ≠ k₀`: outside the image of the tagging `⟨k₀, ·⟩`, so
        -- `μ` gives `0`; the extended history is inconsistent, so its mass is `0`.
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
      -- Weight: tagging preserves weight, so
      --   weight μ = (∏ k ≠ k₀, R k (h|k)) · [D k₀ (h|k₀) x₀] · R k₀ (h|k₀),
      -- to be compared with `[⟨k₀, x₀⟩ admitted after h] · ∏ k, R k (h|k)`.
      · unfold Distribution.weight at ⊢
        rw [Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]
        change (∏ k ∈ Finset.univ.erase k₀, R k (restrictExchanges k h)) *
          (Distribution.fTransform (fun y : B k₀ => (⟨k₀, y⟩ : Σ k, B k))
            ((R k₀).extensionLaw (restrictExchanges k₀ h) x₀)).weight = _
        rw [Distribution.weight_fTransform, extensionLaw_weight]
        by_cases hb : ∀ k, k ≠ k₀ → (restrictExchanges k h).length ≤ (D k).bound
        -- Every other component within its bound: admission is exactly `D k₀ (h|k₀) x₀`.
        · have hadm : (Domain.parallelAll D).admits h ⟨k₀, x₀⟩ ↔
              D k₀ (restrictExchanges k₀ h) x₀ :=
            ⟨fun h' => h'.2.2, fun h' => ⟨hh, hb, h'⟩⟩
          by_cases hd : D k₀ (restrictExchanges k₀ h) x₀
          -- Admitted: the other factors and `R k₀ (h|k₀)` reassemble `∏ k, R k (h|k)`.
          · beta_reduce
            rw [if_pos hd, if_pos (hadm.mpr hd), if_pos hh,
              ← Finset.prod_erase_mul _ _ (Finset.mem_univ k₀)]
          -- Not admitted: both sides are `0`.
          · rw [if_neg hd, if_neg (fun h' => hd (hadm.mp h'))]
            simp
        -- Some `k ≠ k₀` has `|h|k| > (D k).bound`: then `R k (h|k) = 0`, so `weight μ = 0`, and
        -- `⟨k₀, x₀⟩` is not admitted, so the required weight is `0` too.
        · push Not at hb
          obtain ⟨k, hk, hlt⟩ := hb
          rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)
              ((R k).mass_eq_zero_of_bound_lt hlt), zero_mul,
            if_neg (fun h' => (not_le.mpr hlt) (h'.2.1 k hk))]⟩

open Classical in
/-- The defining equation: `(parallelAll R) h = ∏ k, R k (h|k)` if `h` is tag consistent,
`0` otherwise. -/
lemma parallelAll_mass (R : ∀ k, RandomSystem (A k) (B k) (D k))
    (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelAll R h =
      if parallelAllConsistent h then ∏ k, R k (restrictExchanges k h) else 0 := rfl

end RandomSystem

/-! ## Domains -/

open Classical in
/-- **The n-ary parallel input domain.** Component `k` has ports `i : I k` with alphabets
`F k i`; an input `⟨⟨k, i⟩, x⟩` is regrouped as `⟨k, ⟨i, x⟩⟩`, and `h|k` is the regrouped
history restricted to `k`. Then `parallelAllInputs E h` iff `h ≠ []` and, for every `k`,
`h|k = []` or `E k (h|k)`. -/
def parallelAllInputs {I : K → Type} {F : ∀ k, I k → Type}
    (E : ∀ k, List (Σ i, F k i) → Prop) (h : List (Σ l : Σ k, I k, F l.1 l.2)) : Prop :=
  h ≠ [] ∧ ∀ k,
    restrict k (h.map (Equiv.sigmaAssoc F)) = [] ∨ E k (restrict k (h.map (Equiv.sigmaAssoc F)))

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- If every `E k` is closed under nonempty prefixes, so is `parallelAllInputs E`, which
excludes `[]`. -/
lemma parallelAllInputs_nonempty_prefix {I : K → Type} {F : ∀ k, I k → Type}
    {E : ∀ k, List (Σ i, F k i) → Prop}
    (hE : ∀ k, ∀ {p h}, p <+: h → p ≠ [] → E k h → E k p) :
    ¬ parallelAllInputs E [] ∧
      ∀ {p h}, p <+: h → p ≠ [] → parallelAllInputs E h → parallelAllInputs E p := by
  refine ⟨fun h => h.1 rfl, fun {p h} hp hn hd => ⟨hn, fun k => ?_⟩⟩
  -- `p <+: h` gives `p|k <+: h|k`.
  have hpre := restrict_prefix k (hp.map (Equiv.sigmaAssoc F))
  by_cases he : restrict k (p.map (Equiv.sigmaAssoc F)) = []
  · exact Or.inl he
  -- `p|k ≠ []` forces `h|k ≠ []`, so `E k (h|k)`, and `E k (p|k)` by prefix closure.
  · exact Or.inr (hE k hpre he
      ((hd.2 k).resolve_left fun hz => he (List.eq_nil_of_prefix_nil (hz ▸ hpre))))

omit [DecidableEq K] in
open Classical in
/-- If `E k` bounds lengths by `m k`, then `parallelAllInputs E` bounds them by `∑ k, m k`. -/
lemma parallelAllInputs_length_le {I : K → Type} {F : ∀ k, I k → Type}
    {E : ∀ k, List (Σ i, F k i) → Prop} {m : K → ℕ} (hE : ∀ k h, E k h → h.length ≤ m k) :
    ∀ h, parallelAllInputs E h → h.length ≤ ∑ k, m k := by
  intro h hh
  -- `|h| = ∑ k, |h|k|`, and each `|h|k|` is `0` or at most `m k`.
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
/-- On a consistent history, the replies of `h|k` are the replies of `h` restricted to `k`. -/
lemma restrictExchanges_snd {h : List ((Σ k, A k) × (Σ k, B k))}
    (hh : parallelAllConsistent h) (k : K) :
    (restrictExchanges k h).map Prod.snd = restrict k (h.map Prod.snd) := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    -- The head exchange has one tag `kx`; both sides keep its reply iff `kx = k`.
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
/-- **The transcripts of `parAll`.** The deterministic `parAll s` answers `⟨k, x⟩` by
`⟨k, y⟩`, where `s k` answers `y` on the inputs tagged `k` so far. Then `h` is a transcript of
`parAll s` iff `h` is tag consistent and each `h|k` is a transcript of `s k`. No finiteness of
`K` is used. The n-ary analogue of `replies_pair_iff`. -/
lemma replies_parAll_iff (s : ∀ k, System (A k) (B k)) (h : List ((Σ k, A k) × (Σ k, B k))) :
    Replies (parAll s) (h.map Prod.fst) (h.map Prod.snd) ↔
      parallelAllConsistent h ∧
        ∀ k, Replies (s k) ((restrictExchanges k h).map Prod.fst)
          ((restrictExchanges k h).map Prod.snd) := by
  -- Induction on the history from the right.
  induction h using List.reverseRecOn with
  -- Empty history: both sides hold trivially.
  | nil => simp [parallelAllConsistent, restrictExchanges]
  | append_singleton h z ih =>
    -- Last exchange `(⟨kx, x⟩, ⟨ky, y⟩)`. By the hypothesis on `h`, the left side becomes
    --   (consistent h ∧ ∀ k, Replies (s k) on h|k) ∧ parAll s answers ⟨ky, y⟩ to ⟨kx, x⟩,
    -- and the right side is `(consistent h ∧ kx = ky) ∧ ∀ k, Replies (s k) on (h ++ [z])|k`.
    obtain ⟨⟨kx, x⟩, ⟨ky, y⟩⟩ := z
    have hc : parallelAllConsistent (h ++ [((⟨kx, x⟩ : Σ k, A k), (⟨ky, y⟩ : Σ k, B k))]) ↔
        parallelAllConsistent h ∧ kx = ky := by
      simp [parallelAllConsistent, or_imp, forall_and]
    simp only [List.map_append, List.map_cons, List.map_nil, replies_snoc, ih, hc]
    by_cases hh : parallelAllConsistent h
    swap
    -- Inconsistent `h`: both sides are false.
    · simp [hh]
    by_cases hk : kx = ky
    -- Matching tags `kx = ky`: only component `kx` gains the exchange `(x, y)`.
    · subst hk
      -- Other projections are unchanged: `(h ++ [z])|k = h|k` for `k ≠ kx`.
      have hne : ∀ k, k ≠ kx →
          restrictExchanges k (h ++ [((⟨kx, x⟩ : Σ k, A k), (⟨kx, y⟩ : Σ k, B k))]) =
            restrictExchanges k h := by
        intro k hk
        simp [restrictExchanges, List.filterMap_append, Ne.symm hk]
      -- The queried projection gains the exchange: `(h ++ [z])|kx = h|kx ++ [(x, y)]`.
      have hself : restrictExchanges kx (h ++ [((⟨kx, x⟩ : Σ k, A k), (⟨kx, y⟩ : Σ k, B k))]) =
          restrictExchanges kx h ++ [(x, y)] := by
        simp [restrictExchanges, List.filterMap_append]
      -- `parAll s` answers `⟨kx, y⟩` iff `s kx` answers `y` on the inputs of `h|kx`, then `x`.
      have hmap : parAll s (h.map Prod.fst ++ [⟨kx, x⟩]) = Part.some ⟨kx, y⟩ ↔
          s kx ((restrictExchanges kx h).map Prod.fst ++ [x]) = Part.some y := by
        rw [parAll_snoc, ← restrictExchanges_queries hh kx]
        simp [Part.eq_some_iff, Part.mem_map_iff]
      rw [hmap]
      constructor
      -- (→) Each `s k` replies on `h|k`, and `s kx` answers `y` to `x`.
      · rintro ⟨⟨-, hall⟩, hs⟩
        refine ⟨⟨hh, rfl⟩, fun k => ?_⟩
        by_cases hkk : k = kx
        -- Component `kx`: its transcript on `h|kx` extended by the new reply `(x, y)`.
        · subst hkk
          rw [hself, List.map_append, List.map_append, List.map_singleton, List.map_singleton]
          exact replies_snoc.mpr ⟨hall k, hs⟩
        -- Component `k ≠ kx`: its projection, hence its transcript, is unchanged.
        · rw [hne k hkk]
          exact hall k
      -- (←) Each `s k` replies on `(h ++ [z])|k`.
      · rintro ⟨-, hall⟩
        -- Component `kx`: its transcript on `h|kx ++ [(x, y)]` splits into a transcript on
        -- `h|kx` and the answer `y` to `x`, which is the last reply of `parAll s`.
        have hkx := hall kx
        rw [hself, List.map_append, List.map_append, List.map_singleton, List.map_singleton] at hkx
        obtain ⟨hkx, hs⟩ := replies_snoc.mp hkx
        refine ⟨⟨hh, fun k => ?_⟩, hs⟩
        by_cases hkk : k = kx
        · subst hkk
          exact hkx
        -- Component `k ≠ kx`: `(h ++ [z])|k = h|k`, so the hypothesis is already on `h|k`.
        · have hk' := hall k
          rw [hne k hkk] at hk'
          exact hk'
    -- Mismatched tags `kx ≠ ky`: `parAll s` tags its reply `kx`, so it never answers
    -- `⟨ky, y⟩`; the right side fails consistency.
    · have hn : ¬ parAll s (h.map Prod.fst ++ [⟨kx, x⟩]) = Part.some ⟨ky, y⟩ := by
        rw [parAll_snoc]
        intro he
        obtain ⟨w, -, hw⟩ := (Part.mem_map_iff _).mp (Part.eq_some_iff.mp he)
        exact hk (congrArg Sigma.fst hw)
      simp [hn, hk]

end RandomSystem

end SystemAlgebra
