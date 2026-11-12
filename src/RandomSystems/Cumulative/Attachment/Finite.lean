module

public import RandomSystems.Cumulative.Attachment.Defs
public import RandomSystems.Converter.InsideCuts

/-!
# Finite attachment horizons

`IsRandomSystem.attachCut_presents` evaluates the finite assembly on any resource presentation.
`attachCut_eq_of_le` identifies every sufficient inside horizon with `k q`: restricted samples
have the masses supplied by `PDS.behaviorMass_fTransform_cutSystem`, and their reply events
agree by `IsDDCFrom.replies_apply_cutSystem_iff`. `attachCut_coherent` compares outside horizons
through one common resource presentation, providing the coherence needed for gluing.
-/

@[expose] public section

namespace SystemAlgebra.IsRandomSystem

open Probability Probability.Distribution

-- `O`/`J` are outside/inside ports; `U`/`V` and `X`/`Y` are their query/reply families.
variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
-- `E`/`F` admit inside/outside inputs, exclude the empty input and retain nonempty prefixes.
variable {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
  (hE : ¬ E [] ∧ ∀ {s t}, s <+: t → s ≠ [] → E t → E s)
  (hF : ¬ F [] ∧ ∀ {s t}, s <+: t → s ≠ [] → F t → F s)
-- `α` is fixed; `b` bounds consecutive inside queries and `k q` bounds their total through q.
variable {α : InsideOutsideSystem O J U V X Y} {b : ℕ}
  (ha : IsDDCFrom E F b α) {k : ℕ → ℕ}
  (hk : InsideQueriesBounded α k) (mono : Monotone k)
-- `p` is normalized on `E`; `ports` rules out replies at a port different from the query.
variable {p : List ((Σ j, X j) × (Σ j, Y j)) → ℝ}
  (hp : IsRandomSystem (fun h x => E (h.map Prod.fst ++ [x])) p)
  (ports : ∀ h (x : Σ j, X j) (y : Σ j, Y j), y.1 ≠ x.1 → p (h ++ [(x, y)]) = 0)

/-- Every finite attachment replies at its queried outside port. -/
lemma attachCut_repliesAtQueriedInterface (q n : ℕ) (hkn : k q ≤ n) :
    (attachCut hE hF ha hk mono hp ports q n hkn).RepliesAtQueriedInterface := by
  unfold attachCut
  exact PDCBehavior.attach_repliesAtQueriedInterface
    ⟨fun hx => hE.1 hx.1, fun hs hn hx => ⟨hE.2 hs hn hx.1, hs.length_le.trans hx.2⟩⟩
    ⟨fun hx => hF.1 hx.1, fun hs hn hx => ⟨hF.2 hs hn hx.1, hs.length_le.trans hx.2⟩⟩ _ _
    (by intro h x y hne
        change SystemAlgebra.cutMass p n (h ++ [(x, y)]) = 0
        simp only [SystemAlgebra.cutMass, ports h x y hne, ite_self])

/-- A certified resource presentation evaluates the finite attachment by its reply events. -/
lemma attachCut_presents (q n : ℕ) (hkn : k q ≤ n)
    -- `Q` samples resources on the inside cut; `hQ` identifies their cumulative masses.
    (Q : ProbDist {s : InterfaceSystem J X Y // IsDDS s ∧ RepliesAtQueriedInterface s ∧
      ∀ xs, (s xs).Dom ↔ E xs ∧ xs.length ≤ n})
    (hQ : ∀ g, behaviorMass Q.1 (g.map Prod.fst) (g.map Prod.snd) =
      SystemAlgebra.cutMass p n g)
    (h : List ((Σ o, U o) × (Σ o, V o))) :
    attachCut hE hF ha hk mono hp ports q n hkn h =
      Q.1.mass (fun s => Replies
        (apply (filterDom (fun xs => (outsideInputs xs).length ≤ q) α) s.1)
        (h.map Prod.fst) (h.map Prod.snd)) := by
  let R : RandomSystem (Σ j, X j) (Σ j, Y j)
      (Domain.ofInputs (fun xs => E xs ∧ xs.length ≤ n) n (fun _ hx => hx.2)) :=
    ⟨SystemAlgebra.cutMass p n, by
      rw [← Domain.cutDomain_ofInputs]; exact IsRandomSystem.cutMass _ p hp n⟩
  have tags : R.RepliesAtQueriedInterface := by
    intro g x y hne
    change SystemAlgebra.cutMass p n (g ++ [(x, y)]) = 0
    simp only [SystemAlgebra.cutMass, ports g x y hne, ite_self]
  have inside : ¬ (E [] ∧ 0 ≤ n) ∧
      ∀ {s t}, s <+: t → s ≠ [] → (E t ∧ t.length ≤ n) → E s ∧ s.length ≤ n :=
    ⟨fun hx => hE.1 hx.1, fun hs hn hx => ⟨hE.2 hs hn hx.1, hs.length_le.trans hx.2⟩⟩
  have outside : ¬ (F [] ∧ 0 ≤ q) ∧
      ∀ {s t}, s <+: t → s ≠ [] → (F t ∧ t.length ≤ q) → F s ∧ s.length ≤ q :=
    ⟨fun hx => hF.1 hx.1, fun hs hn hx => ⟨hF.2 hs hn hx.1, hs.length_le.trans hx.2⟩⟩
  -- The same filtered converter has the larger inside-domain certificate.
  have certified : IsDDCFrom (fun xs => E xs ∧ xs.length ≤ n)
      (fun xs => F xs ∧ xs.length ≤ q) b
      (filterDom (fun xs => (outsideInputs xs).length ≤ q) α) :=
    (ha.filterDom_of_insideQueriesBounded hk mono q).inside_mono
      (fun xs hx => ⟨hx.1, hx.2.trans hkn⟩)
  exact PDCBehavior.attach_ofDDC_presents inside outside _ certified R tags Q hQ h

/-- Any inside horizon covering the total-query bound gives the same outside cut. -/
lemma attachCut_eq_of_le (q n : ℕ) (hkn : k q ≤ n) :
    attachCut hE hF ha hk mono hp ports q n hkn =
      attachCut hE hF ha hk mono hp ports q (k q) le_rfl := by
  let R : RandomSystem (Σ j, X j) (Σ j, Y j)
      (Domain.ofInputs (fun xs => E xs ∧ xs.length ≤ n) n (fun _ hx => hx.2)) :=
    ⟨SystemAlgebra.cutMass p n, by
      rw [← Domain.cutDomain_ofInputs]; exact IsRandomSystem.cutMass _ p hp n⟩
  have tags : R.RepliesAtQueriedInterface := by
    intro h x y hne
    change SystemAlgebra.cutMass p n (h ++ [(x, y)]) = 0
    simp only [SystemAlgebra.cutMass, ports h x y hne, ite_self]
  have inside (r : ℕ) : ¬ (E [] ∧ 0 ≤ r) ∧
      ∀ {s t}, s <+: t → s ≠ [] → (E t ∧ t.length ≤ r) → E s ∧ s.length ≤ r :=
    ⟨fun hx => hE.1 hx.1, fun hs hn hx => ⟨hE.2 hs hn hx.1, hs.length_le.trans hx.2⟩⟩
  -- One presentation retains the exact domain and reply-port contracts of every sample.
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation (inside n) R tags
  let restrict : {s : InterfaceSystem J X Y // IsDDS s ∧ RepliesAtQueriedInterface s ∧
      ∀ xs, (s xs).Dom ↔ E xs ∧ xs.length ≤ n} →
      {s : InterfaceSystem J X Y // IsDDS s ∧ RepliesAtQueriedInterface s ∧
      ∀ xs, (s xs).Dom ↔ E xs ∧ xs.length ≤ k q} := fun s =>
    ⟨cutSystem s.1 (k q), s.2.1.cutSystem _,
      (fun h x y hy => s.2.2.1 h x y ((filterDom_mem_iff _ _ _ _).mp hy).2), by
      intro xs
      rw [cutSystem, filterDom_dom, s.2.2.2]
      exact ⟨fun hx => ⟨hx.2.1, hx.1⟩, fun hx => ⟨hx.2, hx.1, hx.2.trans hkn⟩⟩⟩
  -- Restricting each sample cuts the same cumulative law at `k q`.
  have mapped (h) : behaviorMass (Q.map restrict).1 (h.map Prod.fst) (h.map Prod.snd) =
      SystemAlgebra.cutMass p (k q) h := by
    rw [ProbDist.map_val, PDS.behaviorMass_fTransform_cutSystem _ _ (k q) (fun _ => rfl),
      List.length_map, hQ]
    by_cases hh : h.length ≤ k q
    · simp only [SystemAlgebra.cutMass, ite_eq_left hh, ite_eq_left (hh.trans hkn), R]
    · simp only [SystemAlgebra.cutMass, ite_eq_right hh]
  -- The small certificate bounds all inside queries, including for the widened domain.
  have small := ha.filterDom_of_insideQueriesBounded hk mono q
  have bound := small.insideQueriesBounded_of_domain (fun _ hx => hx.2)
  have wide : IsDDCFrom (fun xs => E xs ∧ xs.length ≤ n)
      (fun xs => F xs ∧ xs.length ≤ q) b
      (filterDom (fun xs => (outsideInputs xs).length ≤ q) α) :=
    small.inside_mono (fun xs hx => ⟨hx.1, hx.2.trans hkn⟩)
  apply RandomSystem.ext
  intro h
  rw [attachCut_presents hE hF ha hk mono hp ports q n hkn Q hQ,
    attachCut_presents hE hF ha hk mono hp ports q (k q) le_rfl (Q.map restrict) mapped,
    ProbDist.map_val, Distribution.mass_fTransform]
  exact Distribution.mass_congr Q.1 fun s =>
    (wide.replies_apply_cutSystem_iff bound monotone_const s.2.2.1 s.2.2.2
      (Nat.le_refl (h.map Prod.fst).length)).symm

/-- Consecutive outside cuts agree on every transcript visible at the smaller horizon. -/
lemma attachCut_coherent (q : ℕ) (h : List ((Σ o, U o) × (Σ o, V o)))
    (hh : h.length ≤ q) :
    attachCut hE hF ha hk mono hp ports (q + 1) (k (q + 1)) le_rfl h =
      attachCut hE hF ha hk mono hp ports q (k q) le_rfl h := by
  let R : RandomSystem (Σ j, X j) (Σ j, Y j)
      (Domain.ofInputs (fun xs => E xs ∧ xs.length ≤ k (q + 1)) (k (q + 1))
        (fun _ hx => hx.2)) :=
    ⟨SystemAlgebra.cutMass p (k (q + 1)), by
      rw [← Domain.cutDomain_ofInputs]; exact IsRandomSystem.cutMass _ p hp _⟩
  have tags : R.RepliesAtQueriedInterface := by
    intro g x y hne
    change SystemAlgebra.cutMass p (k (q + 1)) (g ++ [(x, y)]) = 0
    simp only [SystemAlgebra.cutMass, ports g x y hne, ite_self]
  -- Both outside cuts use this one presentation at the larger inside horizon.
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation
    ⟨fun hx => hE.1 hx.1, fun hs hn hx => ⟨hE.2 hs hn hx.1, hs.length_le.trans hx.2⟩⟩ R tags
  rw [← attachCut_eq_of_le hE hF ha hk mono hp ports q (k (q + 1)) (mono (Nat.le_succ q))]
  rw [attachCut_presents hE hF ha hk mono hp ports (q + 1) _ le_rfl Q hQ,
    attachCut_presents hE hF ha hk mono hp ports q _ (mono (Nat.le_succ q)) Q hQ]
  apply Distribution.mass_congr Q.1
  intro s
  -- Both outside filters retain the observed transcript.
  rw [apply_filterDom_outside_length, apply_filterDom_outside_length]
  have larger : (h.map Prod.fst).length ≤ q + 1 := by
    rw [List.length_map]
    exact hh.trans (Nat.le_succ q)
  have smaller : (h.map Prod.fst).length ≤ q := by rwa [List.length_map]
  exact (replies_cutSystem_iff _ _ larger).trans (replies_cutSystem_iff _ _ smaller).symm

end SystemAlgebra.IsRandomSystem
