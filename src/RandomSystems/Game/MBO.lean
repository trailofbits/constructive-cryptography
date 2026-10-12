import RandomSystems.Distance.Distinguisher

/-!
# Games with a monotone binary output

A game is a random system whose replies carry a bit, the MBO, which once set stays set; the
game is won when the MBO is set. Its visible system ignores the MBO: the probability of a
transcript, whatever the MBOs. A probabilistic distinguisher, used as a winner, does not see the
MBO; its winning probability is the probability that the MBO of the last reply is set when it
stops, which on a game is the probability that the MBO has been set.

A game is conditionally equivalent to a random system `T` when, as long as the MBO is unset,
it replies as `T`: the probability of a transcript with the MBO unset is the probability that
the MBO is unset after its queries times the probability of the transcript under `T`. Each
distinguisher's advantage between the visible system and `T` is then at most its winning
probability. Its replies before the MBO is set are those of `T`, so the winner learns nothing
about the MBO: if the MBO is set with probability at most `ε` on every fixed sequence of
queries, every winner wins with probability at most `ε`, and the visible system is within `ε`
of `T`.

Sources: CR18, §3.7.1 (games), Definition 4.5 (the winning probability), Definition 4.18 (the
visible system `S⁻`), Definition 4.19 (conditional equivalence), Lemma 4.16 and Theorem 4.17.

## Main definitions

* `withMBO Y`, `forgetMBO`, `tagMBO`: replies with the MBO
* `RandomSystem.MonotoneMBO`: the MBO, once set, stays set
* `sumMBO`, `RandomSystem.visible`: the visible system of a game
* `DDE.blindMBO`, `finalMBO`, `RandomSystem.winProbability`,
  `Domain.Distinguisher.winProbability`: winning
* `RandomSystem.unsetProbability`, `RandomSystem.ConditionallyEquivalent`

## Main results

* `RandomSystem.visible`: the visible system is a random system on the input domain
* `RandomSystem.abs_decisionProbability_sub_le_winProbability`,
  `Domain.Distinguisher.advantage_le_winProbability`: conditional equivalence bounds the
  advantage by the winning probability
* `RandomSystem.winProbability_le_of_unsetProbability`,
  `Domain.Distinguisher.winProbability_le_of_unsetProbability`: under conditional equivalence,
  the probability that the MBO is set on fixed queries bounds the winning probability
* `RandomSystem.transcriptDistance_visible_le_of_unsetProbability`: it then bounds the
  transcript distance between the visible system and the random system
-/

namespace SystemAlgebra

open Probability

/-! ## Replies with the MBO -/

section Replies

variable {J : Type} {Y : J → Type}

/-- Replies with the MBO: a reply and whether the game has been won. -/
abbrev withMBO (Y : J → Type) : J → Type := fun j => Y j × Bool

/-- A reply without its MBO. -/
def forgetMBO (y : Σ j, withMBO Y j) : Σ j, Y j := ⟨y.1, y.2.1⟩

/-- A reply with the MBO `b`. -/
def tagMBO (b : Bool) (y : Σ j, Y j) : Σ j, withMBO Y j := ⟨y.1, (y.2, b)⟩

@[simp] theorem forgetMBO_tagMBO (b : Bool) (y : Σ j, Y j) : forgetMBO (tagMBO b y) = y := rfl

@[simp] theorem tagMBO_fst (b : Bool) (y : Σ j, Y j) : (tagMBO b y).1 = y.1 := rfl

end Replies

/-! ## Games and their visible systems -/

section Visible

variable {A : Type} {J : Type} {Y : J → Type}

/-- The sum of `f` over the transcripts with the queries and replies of a transcript, for every
choice of MBOs. -/
def sumMBO (f : List (A × Σ j, withMBO Y j) → ℝ) : List (A × Σ j, Y j) → ℝ
  | [] => f []
  | z :: t => sumMBO (fun k => f ((z.1, tagMBO false z.2) :: k)) t +
      sumMBO (fun k => f ((z.1, tagMBO true z.2) :: k)) t

theorem sumMBO_snoc (f : List (A × Σ j, withMBO Y j) → ℝ) (h : List (A × Σ j, Y j))
    (z : A × Σ j, Y j) :
    sumMBO f (h ++ [z]) =
      sumMBO (fun k => f (k ++ [(z.1, tagMBO false z.2)]) + f (k ++ [(z.1, tagMBO true z.2)]))
        h := by
  -- Induction on h, for every f: peel the first entry off both sides.
  induction h generalizing f with
  -- h = []: both sides are f [(z.1, z.2 with MBO 0)] + f [(z.1, z.2 with MBO 1)].
  | nil => rfl
  | cons w t ih =>
    -- One step of sumMBO on both sides: the two MBOs of the first entry w.
    simp only [List.cons_append, sumMBO]
    -- The induction hypothesis, for each of the two shifted summands.
    rw [ih, ih]

theorem sumMBO_add (f g : List (A × Σ j, withMBO Y j) → ℝ) (h : List (A × Σ j, Y j)) :
    sumMBO (fun k => f k + g k) h = sumMBO f h + sumMBO g h := by
  -- sumMBO f h sums f over the 2^|h| ways to give h's replies MBOs; induction on h.
  induction h generalizing f g with
  | nil => rfl
  | cons z t ih =>
    -- One step of sumMBO, the induction hypothesis on both branches, then rearrange.
    simp only [sumMBO]
    rw [ih, ih]
    ring

theorem sumMBO_sum {ι : Type} (s : Finset ι) (f : ι → List (A × Σ j, withMBO Y j) → ℝ)
    (h : List (A × Σ j, Y j)) :
    sumMBO (fun k => ∑ i ∈ s, f i k) h = ∑ i ∈ s, sumMBO (f i) h := by
  -- Induction on h: a finite sum passes through each branch of sumMBO.
  induction h generalizing f with
  | nil => rfl
  | cons z t ih =>
    -- One step of sumMBO, the induction hypothesis on both branches, Σ (a + b) = Σ a + Σ b.
    simp only [sumMBO]
    rw [ih, ih, ← Finset.sum_add_distrib]

theorem sumMBO_nonneg {f : List (A × Σ j, withMBO Y j) → ℝ} (hf : ∀ k, 0 ≤ f k)
    (h : List (A × Σ j, Y j)) : 0 ≤ sumMBO f h := by
  -- Induction on h: a sum of the nonnegative values of f.
  induction h generalizing f with
  | nil => exact hf []
  | cons z t ih => exact add_nonneg (ih fun k => hf _) (ih fun k => hf _)

theorem sumMBO_zero (h : List (A × Σ j, Y j)) :
    sumMBO (fun _ : List (A × Σ j, withMBO Y j) => (0 : ℝ)) h = 0 := by
  -- Induction on h: every branch sums zeros.
  induction h with
  | nil => rfl
  | cons z t ih => simp only [sumMBO, ih, add_zero]

open scoped Classical in
/-- A condition on the queries passes through the sum over MBOs. -/
theorem sumMBO_ite (P : List A → Prop) (f : List (A × Σ j, withMBO Y j) → ℝ)
    (h : List (A × Σ j, Y j)) :
    sumMBO (fun k => if P (k.map Prod.fst) then f k else 0) h =
      if P (h.map Prod.fst) then sumMBO f h else 0 := by
  -- Induction on h, for every P and f. Both MBOs of an entry come with the same query, so the
  -- condition, shifted by the first query z.1, is the same on both branches.
  induction h generalizing P f with
  | nil => rfl
  | cons z t ih =>
    -- One step of sumMBO; the queries of (z.1, _) :: k are z.1 :: (queries of k).
    simp only [sumMBO, List.map_cons]
    -- The induction hypothesis with the condition xs ↦ P (z.1 :: xs), on both branches.
    rw [ih (fun xs => P (z.1 :: xs)), ih (fun xs => P (z.1 :: xs))]
    -- Both summands carry the same condition: split on it.
    split_ifs <;> simp

/-- A factor depending only on the queries passes through the sum over MBOs. -/
theorem sumMBO_mul_fst (f : List (A × Σ j, withMBO Y j) → ℝ) (g : List A → ℝ)
    (h : List (A × Σ j, Y j)) :
    sumMBO (fun k => f k * g (k.map Prod.fst)) h = sumMBO f h * g (h.map Prod.fst) := by
  -- Induction on h, for every f and g: as in sumMBO_ite, the factor g depends only on the
  -- queries, which are the same on both MBO branches.
  induction h generalizing f g with
  | nil => rfl
  | cons z t ih =>
    simp only [sumMBO, List.map_cons]
    -- The induction hypothesis with the factor xs ↦ g (z.1 :: xs), on both branches.
    rw [ih (fun k => f ((z.1, tagMBO false z.2) :: k)) (fun xs => g (z.1 :: xs)),
      ih (fun k => f ((z.1, tagMBO true z.2) :: k)) (fun xs => g (z.1 :: xs))]
    -- a·c + b·c = (a + b)·c.
    ring

theorem sumMBO_const_mul (c : ℝ) (f : List (A × Σ j, withMBO Y j) → ℝ) (h : List (A × Σ j, Y j)) :
    sumMBO (fun k => c * f k) h = c * sumMBO f h := by
  -- Induction on h: the constant factor passes through both branches.
  induction h generalizing f with
  | nil => rfl
  | cons z t ih =>
    simp only [sumMBO]
    rw [ih, ih]
    ring

theorem eq_tagMBO_iff {v : Σ j, withMBO Y j} {c : Bool} {y : Σ j, Y j} :
    v = tagMBO c y ↔ forgetMBO v = y ∧ v.2.2 = c := by
  -- A reply with its MBO is determined by the reply without it and the MBO.
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

open scoped Classical in
/-- A reply forgets its MBO into `y` exactly when it is `y` with one of the two MBOs. -/
theorem ite_tagMBO_add (p : Part (Σ j, withMBO Y j)) (y : Σ j, Y j) :
    ((if p = Part.some (tagMBO false y) then 1 else 0) +
      (if p = Part.some (tagMBO true y) then 1 else 0) : ℝ) =
      if p.map forgetMBO = Part.some y then 1 else 0 := by
  -- Case on whether the reply p is defined.
  by_cases hd : p.Dom
  -- p is defined, with value v: each indicator compares v with a reply with its MBO.
  · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
    rw [Part.eq_some_iff.mpr hv, Part.map_some]
    -- v = tagMBO c y iff v forgets to y and its MBO is c.
    simp only [Part.some_inj, eq_tagMBO_iff]
    -- Case on v's MBO and on whether v forgets to y: the left side is 1 exactly when v forgets
    -- to y, whatever its MBO.
    cases hb : v.2.2 <;> by_cases hy : forgetMBO v = y <;> simp [hy]
  -- p is undefined: all three indicators are 0.
  · rw [Part.eq_none_iff'.mpr hd, Part.map_none]
    simp [Part.none_ne_some]

open scoped Classical in
/-- **The sum over MBOs of the transcripts of a system** is the indicator of the transcripts of
the system with the MBO forgotten. -/
theorem sumMBO_replies (t : System A (Σ j, withMBO Y j)) (h : List (A × Σ j, Y j)) :
    sumMBO (fun k => if Replies t (k.map Prod.fst) (k.map Prod.snd) then 1 else 0) h =
      if Replies (relabel t id forgetMBO) (h.map Prod.fst) (h.map Prod.snd) then 1 else 0 := by
  -- t is a deterministic system whose replies carry the MBO; relabel t id forgetMBO is t with
  -- the MBO dropped. Induction on h from the right, one entry z at a time.
  induction h using List.reverseRecOn with
  -- h = []: both systems reply [] to [].
  | nil => simp [sumMBO]
  | append_singleton h z ih =>
    -- Split the last entry z into its two MBO choices.
    rw [sumMBO_snoc]
    -- For each k, the indicators of "t replies k, then z.2 with MBO 0" and "... with MBO 1"
    -- add up to "t replies k" times "t's next reply, MBO dropped, is z.2"; the second factor
    -- depends on k only through its queries.
    have hsummand : ∀ k : List (A × Σ j, withMBO Y j),
        ((if Replies t ((k ++ [(z.1, tagMBO false z.2)]).map Prod.fst)
            ((k ++ [(z.1, tagMBO false z.2)]).map Prod.snd) then 1 else 0) +
          (if Replies t ((k ++ [(z.1, tagMBO true z.2)]).map Prod.fst)
            ((k ++ [(z.1, tagMBO true z.2)]).map Prod.snd) then 1 else 0) : ℝ) =
          (if Replies t (k.map Prod.fst) (k.map Prod.snd) then 1 else 0) *
            (fun xs => if (t (xs ++ [z.1])).map forgetMBO = Part.some z.2 then (1 : ℝ) else 0)
              (k.map Prod.fst) := by
      intro k
      -- replies_snoc: replying to k ++ [z'] is replying to k and then z'.2.
      simp only [List.map_append, List.map_singleton, replies_snoc]
      -- ite_tagMBO_add: the two MBO choices of the next reply add up to "it forgets to z.2".
      rw [← ite_tagMBO_add]
      -- Case on whether t replies k.
      by_cases hr : Replies t (k.map Prod.fst) (k.map Prod.snd) <;> simp [hr]
    -- Rewrite every summand by hsummand.
    simp only [hsummand]
    -- sumMBO_mul_fst pulls the factor that depends only on the queries out of the sum.
    refine (sumMBO_mul_fst (fun k => if Replies t (k.map Prod.fst) (k.map Prod.snd) then (1 : ℝ)
      else 0) (fun xs => if (t (xs ++ [z.1])).map forgetMBO = Part.some z.2 then (1 : ℝ) else 0)
      h).trans ?_
    -- Induction hypothesis: the remaining sum is the indicator for t with the MBO dropped.
    rw [ih]
    -- replies_snoc for t with the MBO dropped; then case on whether it replies h.
    simp only [List.map_append, List.map_singleton, replies_snoc, relabel, List.map_id]
    by_cases hr : Replies (relabel t id forgetMBO) (h.map Prod.fst) (h.map Prod.snd) <;>
      simp [hr]

/-- A transcript with its MBOs forgotten. -/
def forgetMBOs (h : List (A × Σ j, withMBO Y j)) : List (A × Σ j, Y j) :=
  h.map fun z => (z.1, forgetMBO z.2)

/-- A transcript with every MBO unset. -/
def unsetMBOs (h : List (A × Σ j, Y j)) : List (A × Σ j, withMBO Y j) :=
  h.map fun z => (z.1, tagMBO false z.2)

@[simp] theorem forgetMBOs_unsetMBOs (h : List (A × Σ j, Y j)) : forgetMBOs (unsetMBOs h) = h := by
  -- Giving each reply MBO 0 and then forgetting it is the identity on each entry.
  simp [forgetMBOs, unsetMBOs, Function.comp_def]

theorem map_fst_forgetMBOs (h : List (A × Σ j, withMBO Y j)) :
    (forgetMBOs h).map Prod.fst = h.map Prod.fst := by
  -- Forgetting the MBOs keeps the queries.
  simp [forgetMBOs, Function.comp_def]

theorem map_snd_forgetMBOs (h : List (A × Σ j, withMBO Y j)) :
    (forgetMBOs h).map Prod.snd = (h.map Prod.snd).map forgetMBO := by
  -- The replies of the forgotten transcript are the replies with their MBOs forgotten.
  simp [forgetMBOs, Function.comp_def]

/-- Each transcript is one of the terms of the sum over the MBOs of its visible transcript. -/
theorem le_sumMBO {f : List (A × Σ j, withMBO Y j) → ℝ} (hf : ∀ k, 0 ≤ f k)
    (k : List (A × Σ j, withMBO Y j)) : f k ≤ sumMBO f (forgetMBOs k) := by
  -- Induction on k, for every nonnegative f. The first entry z of k, with MBO b, lies on the
  -- b-branch of the sum over MBOs of forgetMBOs k; the other branch is nonnegative.
  induction k generalizing f with
  | nil => exact le_rfl
  | cons z t ih =>
    -- z is its reply with the MBO forgotten, given back its own MBO.
    have hz : z = (z.1, tagMBO z.2.2.2 (forgetMBO z.2)) := rfl
    simp only [forgetMBOs, List.map_cons, sumMBO]
    -- Case on the MBO b of z.
    cases hb : z.2.2.2
    -- b = 0: the induction hypothesis bounds f (z :: t) by the 0-branch.
    · have := ih (f := fun k => f ((z.1, tagMBO false (forgetMBO z.2)) :: k)) (fun k => hf _)
      rw [hz, hb]
      exact le_add_of_le_of_nonneg this (sumMBO_nonneg (fun k => hf _) _)
    -- b = 1: the induction hypothesis bounds f (z :: t) by the 1-branch.
    · have := ih (f := fun k => f ((z.1, tagMBO true (forgetMBO z.2)) :: k)) (fun k => hf _)
      rw [hz, hb]
      exact le_add_of_nonneg_of_le (sumMBO_nonneg (fun k => hf _) _) this

variable [Fintype A] [Fintype J] [∀ j, Fintype (Y j)]

/-- **A game**: a random system whose MBO, once set, stays set (CR18, §3.7.1). -/
def RandomSystem.MonotoneMBO {D : Domain A (Σ j, withMBO Y j)}
    (G : RandomSystem A (Σ j, withMBO Y j) D) : Prop :=
  ∀ h, G h ≠ 0 → (h.map fun z => z.2.2.2).Pairwise (· ≤ ·)

variable {E : List A → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}

open scoped Classical in
/-- **The visible system** `S⁻` of a game, which ignores the MBO (CR18, Definition 4.18): the
probability of a transcript, whatever the MBOs. -/
noncomputable def RandomSystem.visible
    (G : RandomSystem A (Σ j, withMBO Y j) (Domain.ofInputs E m hE)) :
    RandomSystem A (Σ j, Y j) (Domain.ofInputs E m hE) :=
  -- The mass of a visible transcript is the sum of G over its MBO choices. It is a random
  -- system on the input domain: mass 1 on [], nonnegative, and after each transcript h the
  -- replies to a query x weigh the mass of h if x is admitted, 0 otherwise.
  ⟨sumMBO G, by
    -- G⁻ [] = G [] = 1, and sums of nonnegative masses are nonnegative.
    refine ⟨G.mass_nil, sumMBO_nonneg G.mass_nonneg, fun h x => ?_⟩
    -- The weights of the replies y to x after h: y ↦ G⁻ (h ++ [(x, y)]).
    refine ⟨Finsupp.equivFunOnFinite.symm fun y => sumMBO G (h ++ [(x, y)]),
      fun y => rfl, ?_⟩
    -- In G, the replies to x after k, with both MBOs, weigh G k if x is admitted, else 0.
    have reply : ∀ k : List (A × Σ j, withMBO Y j),
        ∑ y : Σ j, Y j, (G (k ++ [(x, tagMBO false y)]) + G (k ++ [(x, tagMBO true y)])) =
          if E (k.map Prod.fst ++ [x]) then G k else 0 := by
      intro k
      -- This is the weight of G's extension law at k and x.
      have hw := G.extensionLaw_weight k x
      rw [Distribution.weight, Finsupp.sum_fintype _ _ (fun _ => rfl)] at hw
      simp only [extensionLaw_apply, Domain.ofInputs_apply] at hw
      -- Reindex the replies with MBOs as pairs (reply, MBO).
      have hsum : ∑ y : Σ j, Y j,
          (G (k ++ [(x, tagMBO false y)]) + G (k ++ [(x, tagMBO true y)])) =
            ∑ y : Σ j, withMBO Y j, G (k ++ [(x, y)]) := by
        let e : (Σ j, Y j) × Bool ≃ Σ j, withMBO Y j :=
          { toFun := fun p => tagMBO p.2 p.1
            invFun := fun y => (forgetMBO y, y.2.2)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [Finset.sum_add_distrib, ← e.sum_comp, Fintype.sum_prod_type_right]
        simp only [Fintype.sum_bool]
        exact add_comm _ _
      rw [hsum, hw]
      congr
    -- Write (y, b) for the reply y with MBO b and [φ] for the indicator of φ. Then
    --   Σ_y G⁻ (h ++ [(x, y)])
    --     = Σ_y sumMBO (k ↦ G (k ++ [(x, (y, 0))]) + G (k ++ [(x, (y, 1))])) h  (sumMBO_snoc)
    --     = sumMBO (k ↦ Σ_y (G (k ++ [(x, (y, 0))]) + G (k ++ [(x, (y, 1))]))) h (sumMBO_sum)
    --     = sumMBO (k ↦ [E (queries of k ++ [x])] · G k) h                      (reply)
    --     = [E (queries of h ++ [x])] · sumMBO G h                              (sumMBO_ite)
    rw [Distribution.weight, Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp only [Finsupp.coe_equivFunOnFinite_symm, sumMBO_snoc]
    rw [← sumMBO_sum]
    simp only [reply, Domain.ofInputs_apply]
    exact sumMBO_ite (fun xs => E (xs ++ [x])) G h⟩

theorem RandomSystem.visible_apply
    (G : RandomSystem A (Σ j, withMBO Y j) (Domain.ofInputs E m hE)) (h : List (A × Σ j, Y j)) :
    G.visible h = sumMBO G h := rfl

end Visible

theorem RandomSystem.RepliesAtQueriedInterface.visible {I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) : G.visible.RepliesAtQueriedInterface := by
  -- A reply y at another interface than the query x: G gives y mass 0 with either MBO, so
  -- the visible mass, their sum over MBOs, is 0.
  intro h x y hy
  -- Split the last entry into its two MBOs.
  rw [RandomSystem.visible_apply, sumMBO_snoc]
  -- G replies at the queried interface: both terms are 0.
  simp only [hG _ x (tagMBO false y) hy, hG _ x (tagMBO true y) hy, add_zero]
  -- A sum of zeros.
  exact sumMBO_zero h

/-- A game replies at the queried interface when its visible system does. -/
theorem RandomSystem.RepliesAtQueriedInterface.of_visible {I : Type} [Fintype I]
    {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hG : G.visible.RepliesAtQueriedInterface) : G.RepliesAtQueriedInterface := by
  -- A reply y at another interface than the query x: G's mass on h ++ [(x, y)] is at most
  -- the visible mass of the transcript with the MBOs forgotten, which is 0 since forgetting
  -- the MBO keeps the interface.
  intro h x y hy
  -- G (h ++ [(x, y)]) ≤ G⁻ (forgetMBOs (h ++ [(x, y)])) (le_sumMBO).
  have hle := le_sumMBO G.mass_nonneg (h ++ [(x, y)])
  rw [← RandomSystem.visible_apply, forgetMBOs, List.map_append, List.map_singleton] at hle
  -- The visible system replies at the queried interface: the bound is 0.
  rw [hG _ x (forgetMBO y) hy] at hle
  -- 0 ≤ G (h ++ [(x, y)]) ≤ 0.
  exact le_antisymm hle (G.mass_nonneg _)

/-! ## Winning -/

section Winning

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

/-- The environment of a winner on replies with the MBO: it does not see the MBO. -/
def DDE.blindMBO (e : DDE (Σ i, X i) (Σ i, Y i)) : DDE (Σ i, X i) (Σ i, withMBO Y i) :=
  -- Query as e on the replies with their MBOs forgotten; the domain stays prefix-closed.
  ⟨fun ys => e.1 (ys.map forgetMBO), fun ys y hd => e.2 (ys.map forgetMBO) (forgetMBO y)
    (by simpa only [List.map_append, List.map_cons, List.map_nil] using hd)⟩

omit [Fintype I] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] in
theorem cons_blindMBO_iff (e : DDE (Σ i, X i) (Σ i, Y i))
    (h : List ((Σ i, X i) × Σ i, withMBO Y i)) :
    Cons (DDE.blindMBO e).1 h ↔ Cons e.1 (forgetMBOs h) := by
  -- Query i of the blinded environment is e's query on the first i replies with their MBOs
  -- forgotten, which are the first i replies of forgetMBOs h.
  simp only [Cons, DDE.blindMBO, forgetMBOs, List.length_map, List.getElem_map,
    ← List.map_take, List.map_map]
  rfl

omit [Fintype I] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] in
theorem good_blindMBO_iff (e : DDE (Σ i, X i) (Σ i, Y i)) (n : ℕ)
    (h : List ((Σ i, X i) × Σ i, withMBO Y i)) :
    Good (DDE.blindMBO e).1 n h ↔ Good e.1 n (forgetMBOs h) := by
  -- Good = Cons ∧ Done; Cons by cons_blindMBO_iff. Done depends on the length and on whether
  -- the environment asks a further query, which forgetting the MBOs keeps.
  rw [Good, Good, cons_blindMBO_iff]
  simp only [Done, DDE.blindMBO, forgetMBOs, List.length_map, List.map_map]
  rfl

/-- The MBO of the last reply of a transcript, unset before any reply. -/
def finalMBO {A : Type} (h : List (A × Σ i, withMBO Y i)) : Bool :=
  (h.getLast?.map fun z => z.2.2.2).getD false

omit [Fintype I] [∀ i, Fintype (Y i)] in
/-- Along a transcript whose MBO, once set, stays set, the final MBO is set exactly when some
MBO is. -/
theorem finalMBO_eq_true_iff {A : Type} {h : List (A × Σ i, withMBO Y i)}
    (hp : (h.map fun z => z.2.2.2).Pairwise (· ≤ ·)) :
    finalMBO h = true ↔ ¬ ∀ z ∈ h, z.2.2.2 = false := by
  -- Induction from the right; only the last entry z matters.
  induction h using List.reverseRecOn with
  -- h = []: the final MBO is unset by definition, and there is no MBO.
  | nil => simp [finalMBO]
  | append_singleton h z ih =>
    -- Monotonicity of h ++ [z]: every MBO in h is ≤ the MBO of z.
    simp only [List.map_append, List.map_singleton, List.pairwise_append, List.pairwise_singleton,
      List.mem_singleton, forall_eq, List.mem_map] at hp
    -- The final MBO is the MBO of z.
    simp only [finalMBO, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.map_some, Option.getD_some, List.mem_append, List.mem_singleton]
    constructor
    -- (→) The MBO of z is set, so not every MBO is unset.
    · intro hz hall
      have := hall z (Or.inr rfl)
      rw [hz] at this
      cases this
    -- (←) Some MBO is set. If the MBO of z were unset, monotonicity would unset all of h.
    · intro hall
      by_contra hz
      have hz' : z.2.2.2 = false := by simpa using hz
      apply hall
      rintro w (hw | rfl)
      -- w ∈ h: the MBO of w is ≤ that of z, which is unset.
      · have := hp.2.2 _ ⟨w, hw, rfl⟩
        rw [hz'] at this
        by_contra hne
        have ht : w.2.2.2 = true := by simpa using hne
        rw [ht] at this
        exact absurd this (by decide)
      -- w = z: unset by assumption.
      · exact hz'

/-- **The winning probability** of a deterministic distinguisher, used as a winner, for a
game (CR18, Definition 4.5): the probability that the MBO is set when it stops. -/
noncomputable def RandomSystem.winProbability {D' : Domain (Σ i, X i) (Σ i, withMBO Y i)}
    (G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) D') (D : DDD I X Y) (hD : IsDDD D) : ℝ :=
  (G.sLaw (DDE.blindMBO (ddeOf hD)).1 hD.2.1.choose).mass fun h => finalMBO h = true

/-- The winning probability of a probabilistic distinguisher, used as a winner. -/
noncomputable def Domain.Distinguisher.winProbability {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}
    {D' : Domain (Σ i, X i) (Σ i, withMBO Y i)} (P : 𝒟.Distinguisher)
    (G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) D') : ℝ :=
  P.1.sum fun D w => w * G.winProbability D.1 D.2.1

/-- The probability that the MBO of a game is unset after a fixed sequence of queries. -/
noncomputable def RandomSystem.unsetProbability {D' : Domain (Σ i, X i) (Σ i, withMBO Y i)}
    (G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) D') (xs : List (Σ i, X i)) : ℝ :=
  (G.sLaw (DDE.ofQueries xs).1 xs.length).mass fun h => ∀ z ∈ h, z.2.2.2 = false

/-- Before any query, the MBO is unset. -/
theorem RandomSystem.unsetProbability_nil {D' : Domain (Σ i, X i) (Σ i, withMBO Y i)}
    (G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) D') : G.unsetProbability [] = 1 := by
  -- The environment asking no queries is compatible with G: it never asks.
  have hc : G.Compatible (DDE.ofQueries ([] : List (Σ i, X i))).1 := by
    intro h x _ _ hx
    simp [DDE.ofQueries, fixedQueries] at hx
  -- So its transcript law within 0 rounds is a probability distribution.
  have hP := G.sLaw_isProbDist hc ([] : List (Σ i, X i)).length
  -- Compare the mass of "every MBO unset" with the total mass 1, on the support.
  rw [RandomSystem.unsetProbability, ← hP.2, ← Distribution.mass_true]
  apply Distribution.mass_congr_of_support
  intro h hh
  -- A transcript in the support is complete within 0 rounds, hence empty.
  have hnil : h = [] := by
    by_contra hne
    apply Finsupp.mem_support_iff.mp hh
    rw [sLaw_apply, if_neg]
    rintro ⟨-, hd | ⟨hd, -⟩⟩
    · exact hne (List.length_eq_zero_iff.mp hd)
    · exact Nat.not_lt_zero _ hd
  -- On [] every MBO is unset: there is none.
  subst hnil
  simp

/-- **Conditional equivalence** `S |≡ T` (CR18, Definition 4.19): the probability of a
transcript with the MBO unset is the probability that the MBO is unset after its queries times
the probability of the transcript under `T`. -/
def RandomSystem.ConditionallyEquivalent {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}
    {D' : Domain (Σ i, X i) (Σ i, withMBO Y i)}
    (G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) D')
    (T : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) : Prop :=
  ∀ h, G (unsetMBOs h) = G.unsetProbability (h.map Prod.fst) * T h

variable {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}

/-- A random system on the input domain admits the fixed queries of a possible transcript of
another one. -/
theorem RandomSystem.compatible_fixedQueries {B : Type} [Fintype B]
    (R : RandomSystem (Σ i, X i) B (Domain.ofInputs E m hE))
    {T : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    {h : List ((Σ i, X i) × Σ i, Y i)} (hT : T h ≠ 0) :
    R.Compatible (fixedQueries (h.map Prod.fst)) := by
  -- After a transcript t following the fixed queries of h, R is asked x, the query of h at
  -- position |t|, and t's queries are the first |t| queries of h. Since T h ≠ 0, the query of
  -- h at position |t| is admitted after its prefix; on the input domain admission depends only
  -- on the queries.
  intro t x hc _ hx
  -- t follows the fixed queries: |t| ≤ |h| and t has h's first |t| queries.
  obtain ⟨hl, ht⟩ := cons_fixedQueries hc
  -- x is the query of h at position |t|.
  have hx' : (h.map Prod.fst)[t.length]? = some x := by
    simpa [fixedQueries] using hx
  -- So |t| < |h|.
  have hlt : t.length < h.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by simpa using hn)] at hx'
    cases hx'
  -- In the possible transcript h, the query at position |t| is admitted after its prefix.
  have hp := (T.possible_prefix hT t.length hlt).1
  -- On the input domain, admission is E on the queries.
  simp only [Domain.ofInputs_apply] at hp ⊢
  -- Replace t's queries and x by those of h.
  rw [ht]
  have hx'' : x = (h[t.length]).1 := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hlt] at hx'
    exact (Option.some_inj.mp hx').symm
  rw [hx'', ← List.map_take, List.length_map] at *
  exact hp

open scoped Classical in
/-- **Winning leaves the MBO unset on the rest**: the winning probability of a deterministic
distinguisher is one minus the mass of its transcripts on which the MBO stays unset, which on
each transcript it may produce is the mass of the game with the MBO unset. -/
theorem RandomSystem.exists_unset_winProbability
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO) (D : DDD I X Y) (hD : IsDDD D)
    (hdc : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).DecisionCompatible D) :
    ∃ ν : Distribution (List ((Σ i, X i) × Σ i, Y i)),
      (∀ h, ν h = if Good (ddeOf hD).1 hD.2.1.choose h then G (unsetMBOs h) else 0) ∧
        G.winProbability D hD = 1 - ν.weight := by
  -- Plan. The winner is D's environment e, blinded to the MBO; it plays G for n rounds:
  --
  --   ┌────────────────┐ ───── x ─────▶ ┌───┐
  --   │ W = blindMBO e │                │ G │
  --   └────────────────┘ ◀─── (y, a) ── └───┘
  --
  -- Transcript x₁, (y₁, a₁), x₂, (y₂, a₂), …; e sees only the yᵢ, and the MBO aᵢ, once 1,
  -- stays 1. W wins when the last aᵢ is 1.
  -- Step 1. G is compatible with W, because G⁻ is compatible with e.
  -- Step 2. μ is the transcript law of G with W; ν is its part where every MBO stays 0, with
  --         the MBOs dropped.
  -- Step 3. ν h = G (h with every MBO 0) if h is complete for e, else 0.
  -- Step 4. The winning probability is
  --         Γ = μ(last MBO 1) = μ(some MBO 1) = 1 − μ(every MBO 0) = 1 − weight ν.
  set e := ddeOf hD
  set n := hD.2.1.choose
  -- Step 1. G⁻ is compatible with e, since D is compatible with the input domain.
  have hV : G.visible.Compatible e.1 := hdc.environment hD _ hG.visible
  -- The game is compatible with the winner, which does not see the MBO.
  have hB : G.Compatible (DDE.blindMBO e).1 := by
    intro h x hcons hGh hx
    -- G h ≠ 0 makes the visible transcript possible: 0 < G h ≤ G⁻ (forgetMBOs h).
    have hpos : G.visible (forgetMBOs h) ≠ 0 := by
      have := le_sumMBO G.mass_nonneg h
      rw [← RandomSystem.visible_apply] at this
      exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (G.mass_nonneg h) (Ne.symm hGh)) this)
    -- e's query after the visible transcript is admitted, since G⁻ is compatible with e;
    -- admission depends only on the queries, which forgetting the MBOs keeps.
    have := hV (forgetMBOs h) x ((cons_blindMBO_iff e h).mp hcons) hpos
      (by rwa [map_snd_forgetMBOs])
    simpa only [Domain.ofInputs_apply, map_fst_forgetMBOs] using this
  -- Step 2. μ: the transcript law of G with W within n rounds; ν: its restriction to the
  -- transcripts with every MBO 0, with the MBOs forgotten.
  set μ := G.sLaw (DDE.blindMBO e).1 n
  refine ⟨Distribution.fTransform forgetMBOs (μ.restrict fun h => ∀ z ∈ h, z.2.2.2 = false),
    fun h => ?_, ?_⟩
  -- Step 3. ν h is the μ-mass of the transcripts that forget to h with every MBO 0.
  · rw [Distribution.fTransform_apply_eq_mass, Distribution.mass_restrict]
    -- There is exactly one such transcript: h with every MBO 0.
    have hcg : ∀ k, (forgetMBOs k = h ∧ ∀ z ∈ k, z.2.2.2 = false) ↔ k = unsetMBOs h := by
      intro k
      constructor
      -- (→) Each entry of k has MBO 0, so it is its forgotten entry given MBO 0.
      · rintro ⟨rfl, hk⟩
        simp only [unsetMBOs, forgetMBOs, List.map_map]
        conv_lhs => rw [← List.map_id k]
        apply List.map_congr_left
        intro z hz
        have := hk z hz
        simp only [Function.comp_apply, id]
        rw [← this]
        rfl
      -- (←) unsetMBOs h forgets to h and all its MBOs are 0.
      · rintro rfl
        refine ⟨forgetMBOs_unsetMBOs h, fun z hz => ?_⟩
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hz
        rfl
    -- μ at h with every MBO 0; that is complete for W iff h is complete for e.
    rw [Distribution.mass_congr _ hcg, Distribution.mass_singleton, sLaw_apply,
      good_blindMBO_iff, forgetMBOs_unsetMBOs]
  -- Step 4. Γ = 1 − weight ν.
  · -- The winning probability is the mass where the MBO is set.
    -- μ is a probability distribution, as G is compatible with W (Step 1).
    have hμ := G.sLaw_isProbDist hB n
    -- On the support of μ, G is positive, so the MBOs there are monotone: the last MBO is 1
    -- iff some MBO is (finalMBO_eq_true_iff).
    have hset : μ.mass (fun h => finalMBO h = true) =
        μ.mass (fun h => ¬ ∀ z ∈ h, z.2.2.2 = false) := by
      apply Distribution.mass_congr_of_support
      intro h hh
      have hne : G h ≠ 0 := by
        intro hz
        apply Finsupp.mem_support_iff.mp hh
        simp only [μ, sLaw_apply, hz, ite_self]
      exact finalMBO_eq_true_iff (hm h hne)
    -- μ(every MBO 0) + μ(some MBO 1) = 1.
    have hcompl := Distribution.mass_add_compl μ (fun h => ∀ z ∈ h, z.2.2.2 = false)
    rw [hμ.2] at hcompl
    -- weight ν = μ(every MBO 0): forgetting the MBOs keeps the weight.
    rw [RandomSystem.winProbability, hset, Distribution.weight_fTransform,
      Distribution.weight_restrict]
    linarith

open scoped Classical in
/-- **Conditional equivalence bounds distinguishing by winning**, for a deterministic
distinguisher (CR18, Lemma 4.16 and Theorem 4.17). -/
theorem RandomSystem.abs_decisionProbability_sub_le_winProbability
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    {T : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hT : T.RepliesAtQueriedInterface)
    (hm : G.MonotoneMBO) (hc : G.ConditionallyEquivalent T)
    (D : DDD I X Y) (hD : IsDDD D)
    (hdc : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).DecisionCompatible D) :
    |G.visible.decisionProbability D hD - T.decisionProbability D hD| ≤
      G.winProbability D hD := by
  -- Plan. D plays G⁻, which is G with the MBO dropped, and T, through its environment e for
  -- n rounds:
  --
  --   ┌───┐ ──x──▶ ┌───┐                    ┌───┐ ──x──▶ ┌───┐
  --   │ D │        │ G │ ──▶ a (dropped)    │ D │        │ T │
  --   └───┘ ◀──y── └───┘                    └───┘ ◀──y── └───┘
  --
  -- μV, μT: the transcript laws of G⁻ and T with e; P: the event "D decides 1", so that the
  -- decision probabilities are p_D(G⁻) = μV(P) and p_D(T) = μT(P). ν: the law of G's
  -- transcripts on which the MBO stays 0, with the MBOs dropped; it lies below μV and μT.
  -- Step 1. ν h = G (h with every MBO 0) on the h complete for e, and D's winning
  --         probability is Γ_D(G) = 1 − weight ν.
  -- Step 2. ν ≤ μV: G (h with every MBO 0) is one term of G⁻ h, the sum over the MBOs.
  -- Step 3. ν ≤ μT: by conditional equivalence, G (h with every MBO 0)
  --         = Pr[MBO stays 0 on h's queries] · T h ≤ T h.
  -- Step 4. If μ₁ has weight 1 and ν ≤ μ₁, then 0 ≤ μ₁(P) − ν(P) ≤ 1 − weight ν.
  -- Step 5. The chain:
  --   |p_D(G⁻) − p_D(T)|
  --     = |(μV(P) − ν(P)) − (μT(P) − ν(P))|    (subtract and add ν(P))
  --     ≤ 1 − weight ν                         (Steps 2–4: both lie in [0, 1 − weight ν])
  --     = Γ_D(G)                               (Step 1)
  set e := ddeOf hD
  set n := hD.2.1.choose
  -- G⁻ and T are compatible with e, as D is compatible with the input domain.
  have henv := hdc.environment hD
  have hV : G.visible.Compatible e.1 := henv _ hG.visible
  have hTc : T.Compatible e.1 := henv _ hT
  -- μV, μT: the transcript laws of G⁻ and T with e within n rounds.
  set μV := G.visible.sLaw e.1 n
  set μT := T.sLaw e.1 n
  -- Step 1. ν, with Γ_D(G) = 1 − weight ν.
  obtain ⟨ν, hν, hwin⟩ := G.exists_unset_winProbability hG hm D hD hdc
  -- Step 2. ν ≤ μV.
  have hνV : ∀ h, ν h ≤ μV h := by
    intro h
    rw [hν, sLaw_apply]
    -- Split on whether h is complete for e; if not, both sides are 0.
    split_ifs
    -- le_sumMBO: G (h with every MBO 0) ≤ sumMBO G h = G⁻ h.
    · have := le_sumMBO G.mass_nonneg (unsetMBOs h)
      rwa [forgetMBOs_unsetMBOs, ← RandomSystem.visible_apply] at this
    · exact le_rfl
  -- Step 3. ν ≤ μT.
  have hνT : ∀ h, ν h ≤ μT h := by
    intro h
    rw [hν, sLaw_apply]
    split_ifs
    -- Conditional equivalence: G (h with every MBO 0) = Pr[MBO stays 0 on h's queries] · T h.
    · rw [hc h]
      by_cases hz : T h = 0
      -- T h = 0: both sides are 0.
      · rw [hz, mul_zero]
      -- Otherwise G admits the fixed queries of h, so its transcript law with them is a
      -- probability distribution, and the probability that the MBO stays 0, one of its masses,
      -- is ≤ 1.
      · have hP := G.sLaw_isProbDist (G.compatible_fixedQueries hz) (h.map Prod.fst).length
        have hle : G.unsetProbability (h.map Prod.fst) ≤ 1 := by
          rw [← hP.2]
          exact Distribution.mass_le_weight hP.1 _
        exact mul_le_of_le_one_left (T.mass_nonneg h) hle
    · exact le_rfl
  -- Both transcript laws have weight 1.
  have hμV := G.visible.sLaw_isProbDist hV n
  have hμT := T.sLaw_isProbDist hTc n
  -- Step 4. Bound the part of μV and μT beyond ν.
  -- Masses of the differences.
  have hsub : ∀ (μ₁ : Distribution (List ((Σ i, X i) × Σ i, Y i)))
      (P : List ((Σ i, X i) × Σ i, Y i) → Prop),
      (μ₁ - ν).mass P = μ₁.mass P - ν.mass P := by
    intro μ₁ P
    -- Mass is additive: ν + (μ₁ − ν) = μ₁.
    have := Distribution.mass_add ν (μ₁ - ν) P
    rw [add_sub_cancel] at this
    linarith
  -- If μ₁ has weight 1 and ν ≤ μ₁, then μ₁ − ν is nonnegative with weight 1 − weight ν, so
  -- each of its masses lies in [0, 1 − weight ν].
  have hbound : ∀ μ₁ : Distribution (List ((Σ i, X i) × Σ i, Y i)), μ₁.weight = 1 →
      (∀ h, ν h ≤ μ₁ h) → ∀ P, 0 ≤ μ₁.mass P - ν.mass P ∧
        μ₁.mass P - ν.mass P ≤ 1 - ν.weight := by
    intro μ₁ hw hle P
    -- μ₁ − ν ≥ 0 pointwise.
    have hnn : (μ₁ - ν).NonNeg := fun h => by
      simp only [Finsupp.coe_sub, Pi.sub_apply, sub_nonneg]
      exact hle h
    rw [← hsub]
    refine ⟨hnn.mass_nonneg P, ?_⟩
    -- weight (μ₁ − ν) = weight μ₁ − weight ν = 1 − weight ν.
    have hwt : (μ₁ - ν).weight = 1 - ν.weight := by
      rw [← Distribution.mass_true, hsub, Distribution.mass_true, Distribution.mass_true, hw]
    rw [← hwt]
    exact Distribution.mass_le_weight hnn P
  -- Step 5. Step 4 for μV and for μT, with P = "D decides 1".
  obtain ⟨h1, h2⟩ := hbound μV hμV.2 hνV
    (fun h => ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd)))
  obtain ⟨h3, h4⟩ := hbound μT hμT.2 hνT
    (fun h => ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd)))
  -- Γ_D(G) = 1 − weight ν; |a| ≤ c is −c ≤ a ∧ a ≤ c.
  rw [hwin, abs_le]
  -- The decision probabilities are μV(P) and μT(P) by definition.
  change -(1 - ν.weight) ≤ μV.mass _ - μT.mass _ ∧ μV.mass _ - μT.mass _ ≤ 1 - ν.weight
  -- Both inequalities follow from Step 4 by linear arithmetic.
  constructor <;> linarith

/-- **Conditional equivalence bounds distinguishing by winning** (CR18, Lemma 4.16 and
Theorem 4.17): a distinguisher's advantage between the visible system of a game and a random
system conditionally equivalent to it is at most its winning probability. -/
theorem Domain.Distinguisher.advantage_le_winProbability
    (P : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).Distinguisher)
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    {T : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hT : T.RepliesAtQueriedInterface)
    (hm : G.MonotoneMBO) (hc : G.ConditionallyEquivalent T) :
    |P.probability G.visible - P.probability T| ≤ P.winProbability G := by
  -- P is a distribution over deterministic distinguishers D, with weights P(D) ≥ 0:
  --   |Σ_D P(D)·p_D(G⁻) − Σ_D P(D)·p_D(T)|
  --     = |Σ_D P(D)·(p_D(G⁻) − p_D(T))|
  --     ≤ Σ_D P(D)·|p_D(G⁻) − p_D(T)|     (triangle inequality, P(D) ≥ 0)
  --     ≤ Σ_D P(D)·Γ_D(G)                  (the deterministic case)
  --     = Γ_P(G)
  simp only [Domain.Distinguisher.probability, Domain.Distinguisher.winProbability,
    Finsupp.sum]
  -- The difference of the sums is the sum of the differences.
  rw [← Finset.sum_sub_distrib]
  -- Triangle inequality, then compare termwise.
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun D _ => ?_)
  -- |P(D)·a − P(D)·b| = P(D)·|a − b|, as P(D) ≥ 0.
  rw [← mul_sub, abs_mul, abs_of_nonneg (P.2.1 D)]
  -- The deterministic case, scaled by P(D) ≥ 0.
  exact mul_le_mul_of_nonneg_left
    (RandomSystem.abs_decisionProbability_sub_le_winProbability hG hT hm hc D.1 D.2.1 D.2.2)
    (P.2.1 D)

open scoped Classical in
/-- **Winning on fixed queries bounds winning**, for a deterministic distinguisher: a game
conditionally equivalent to a random system, whose MBO stays unset with probability at least
`1 - ε` on the queries of each transcript of the random system, is won with probability at
most `ε`. -/
theorem RandomSystem.winProbability_le_of_unsetProbability
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    {T : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hT : T.RepliesAtQueriedInterface)
    (hm : G.MonotoneMBO) (hc : G.ConditionallyEquivalent T) {ε : ℝ}
    (hε : ∀ h, T h ≠ 0 → 1 - ε ≤ G.unsetProbability (h.map Prod.fst))
    (D : DDD I X Y) (hD : IsDDD D)
    (hdc : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).DecisionCompatible D) :
    G.winProbability D hD ≤ ε := by
  -- With e the environment of D: ν h = G (h with every MBO 0) on the transcripts h complete
  -- for e, and Γ_D(G) = 1 − weight ν (exists_unset_winProbability). D may choose its queries
  -- adaptively; conditional
  -- equivalence writes ν h as Pr[MBO stays 0 on h's queries], a fixed-query probability,
  -- times T h, so hε gives ν ≥ (1 − ε)·μT, with μT the transcript law of T with e, a
  -- probability distribution. Then
  --   Γ_D(G) = 1 − weight ν
  --          = 1 − weight (ν − (1 − ε)·μT) − (1 − ε)·weight μT
  --          ≤ 1 − (1 − ε)·1                   (ν − (1 − ε)·μT ≥ 0, weight μT = 1)
  --          = ε
  obtain ⟨ν, hν, hwin⟩ := G.exists_unset_winProbability hG hm D hD hdc
  -- μT is a probability distribution, as T is compatible with e.
  have hμT := T.sLaw_isProbDist (hdc.environment hD _ hT) hD.2.1.choose
  -- ν − (1 − ε)·μT ≥ 0 pointwise.
  have hle : (ν - (1 - ε) • T.sLaw (ddeOf hD).1 hD.2.1.choose).NonNeg := fun h => by
    simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      sub_nonneg]
    rw [hν, sLaw_apply]
    split_ifs
    -- h complete for e: G (h with every MBO 0) = Pr[MBO stays 0 on h's queries] · T h, and the
    -- probability is ≥ 1 − ε by hε if T h ≠ 0.
    · rw [hc h]
      by_cases hz : T h = 0
      -- T h = 0: both sides are 0.
      · simp [hz]
      · exact mul_le_mul_of_nonneg_right (hε h hz) (T.mass_nonneg h)
    -- h not complete for e: both sides are 0.
    · simp
  -- weight ν = weight (ν − (1 − ε)·μT) + (1 − ε)·weight μT: weight is linear.
  have hw : ν.weight = (ν - (1 - ε) • T.sLaw (ddeOf hD).1 hD.2.1.choose).weight +
      (1 - ε) * (T.sLaw (ddeOf hD).1 hD.2.1.choose).weight := by
    rw [← Distribution.weight_smul, ← Distribution.weight_add, sub_add_cancel]
  -- Γ_D(G) = 1 − weight ν ≤ ε, since the first weight is ≥ 0 and weight μT = 1.
  rw [hwin, hw, hμT.2]
  linarith [hle.weight_nonneg]

/-- **Winning on fixed queries bounds winning**: a game conditionally equivalent to a random
system, whose MBO stays unset with probability at least `1 - ε` on the queries of each
transcript of the random system, is won by each distinguisher with probability at most `ε`. -/
theorem Domain.Distinguisher.winProbability_le_of_unsetProbability
    (P : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).Distinguisher)
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    {T : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hT : T.RepliesAtQueriedInterface)
    (hm : G.MonotoneMBO) (hc : G.ConditionallyEquivalent T) {ε : ℝ}
    (hε : ∀ h, T h ≠ 0 → 1 - ε ≤ G.unsetProbability (h.map Prod.fst)) :
    P.winProbability G ≤ ε := by
  -- Γ_P(G) = Σ_D P(D)·Γ_D(G) ≤ Σ_D P(D)·ε = ε.
  calc P.winProbability G ≤ P.1.sum fun _ w => w * ε := by
        -- Termwise, by the deterministic case scaled by P(D) ≥ 0.
        simp only [Domain.Distinguisher.winProbability, Finsupp.sum]
        exact Finset.sum_le_sum fun D _ => mul_le_mul_of_nonneg_left
          (RandomSystem.winProbability_le_of_unsetProbability hG hT hm hc hε D.1 D.2.1 D.2.2)
          (P.2.1 D)
    _ = ε := by
        -- Σ_D P(D)·ε = (Σ_D P(D))·ε = ε, as P's weights sum to 1.
        simp only [Finsupp.sum, ← Finset.sum_mul]
        rw [show (∑ D ∈ P.1.support, P.1 D) = 1 from P.2.2, one_mul]

/-- **Conditional equivalence bounds the distance by non-adaptive winning** (CR18,
Theorem 4.17, printed p. 110: "If for an (X, Y)-system S one can define an MBO such that
Ŝ |≡ T, then [...] ∆(S, T) ≤ Γ(bŜ)"): a game conditionally equivalent to a random system,
whose MBO stays unset with probability at least `1 - ε` on the queries of each transcript of
the random system, has its visible system within `ε` of the random system. -/
theorem RandomSystem.transcriptDistance_visible_le_of_unsetProbability
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    {T : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hT : T.RepliesAtQueriedInterface)
    (hm : G.MonotoneMBO) (hc : G.ConditionallyEquivalent T) {ε : ℝ}
    (hε : ∀ h, T h ≠ 0 → 1 - ε ≤ G.unsetProbability (h.map Prod.fst)) :
    G.visible.transcriptDistance T ≤ ENNReal.ofReal ε := by
  --   Δ(G⁻, T) = sup_P |p_P(G⁻) − p_P(T)|    (transcriptDistance_eq_iSup)
  --            ≤ sup_P Γ_P(G)                (advantage_le_winProbability)
  --            ≤ ε                           (winProbability_le_of_unsetProbability)
  -- The hypothesis bounds the MBO only on fixed query sequences, yet the bound holds for
  -- every adaptive distinguisher.
  -- The transcript distance is the largest advantage of a probabilistic distinguisher.
  rw [RandomSystem.transcriptDistance_eq_iSup hG.visible hT]
  -- Lemma 4.16 bounds each advantage by winning, which the unset MBO bounds.
  exact iSup_le fun P => ENNReal.ofReal_le_ofReal
    ((P.advantage_le_winProbability hG hT hm hc).trans
      (P.winProbability_le_of_unsetProbability hG hT hm hc hε))

end Winning

end SystemAlgebra
