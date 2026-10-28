import RandomSystems.System.Basic

/-!
# Componentwise wiring of parallel systems

Each feedback route retains the component tag. Wiring the components separately therefore
agrees with wiring their parallel family. Convergence is explicit for every component;
no finiteness of the index type or equality of arbitrary off-tree representatives is used.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” His converter definition on pp. 17–18 supplies bounded internal
interaction. The theorem below derives the corresponding wiring law from the existing
`Induces` semantics, with the weaker hypothesis of convergence.
-/

namespace SystemAlgebra


variable {K : Type} {A B X Y : K → Type}

open Classical in
/-- A family of feedback routes, each retaining its component label. -/
def parallelRoute (route : ∀ k, Y k → B k ⊕ X k) :
    (Σ k, Y k) → (Σ k, B k) ⊕ (Σ k, X k)
  | ⟨k, y⟩ => (route k y).map (Sigma.mk k) (Sigma.mk k)

open Classical in
/-- Inputs enter the selected component through its own injection. -/
def parallelInj (inj : ∀ k, A k → X k) : (Σ k, A k) → Σ k, X k
  | ⟨k, a⟩ => ⟨k, inj k a⟩

variable {s : ∀ k, System (X k) (Y k)} {route : ∀ k, Y k → B k ⊕ X k}
  {inj : ∀ k, A k → X k}

open Classical in
/-- An internal exchange affects only the component in which it started. -/
lemma Exchange.parallel_at {k : K} {T o T'} (l : Exchange (s k) (route k) T o T') :
    ∀ (H : List (Σ k, X k)) (x : X k), restrict k (H ++ [⟨k, x⟩]) = T →
      ∃ H', Exchange (parAll s) (parallelRoute route) (H ++ [⟨k, x⟩])
          (o.map (Sigma.mk k)) H' ∧
        restrict k H' = T' ∧
        ∀ j, j ≠ k → restrict j H' = restrict j H := by
  induction l with
  | silent T hd =>
    rintro H x rfl
    refine ⟨_, Exchange.silent _ ?_, rfl, ?_⟩
    · rw [parAll_snoc]
      change ¬ (s k (restrict k H ++ [x])).Dom
      simpa only [restrict_append, restrict_cons_self, restrict_nil] using hd
    · intro j hj
      simp only [restrict_append, restrict_cons_ne (Ne.symm hj), restrict_nil,
        List.append_nil]
  | out T y b hy hr =>
    rintro H x rfl
    refine ⟨_, Exchange.out _ ⟨k, y⟩ _ ?_ ?_, rfl, ?_⟩
    · rw [parAll_snoc]
      exact Part.mem_map _ (by simpa only [restrict_append, restrict_cons_self,
        restrict_nil] using hy)
    · simp only [parallelRoute, hr, Sum.map_inl]
    · intro j hj
      simp only [restrict_append, restrict_cons_ne (Ne.symm hj), restrict_nil,
        List.append_nil]
  | feed T y x' o T' hy hr _ ih =>
    rintro H x rfl
    obtain ⟨H', l, hk, hj⟩ := ih (H ++ [⟨k, x⟩]) x' (by simp)
    refine ⟨H', Exchange.feed _ ⟨k, y⟩ ⟨k, x'⟩ _ _ ?_ ?_ l, hk, ?_⟩
    · rw [parAll_snoc]
      exact Part.mem_map _ (by simpa only [restrict_append, restrict_cons_self,
        restrict_nil] using hy)
    · simp only [parallelRoute, hr, Sum.map_inr]
    · intro j hne
      rw [hj j hne]
      simp only [restrict_append, restrict_cons_ne (Ne.symm hne), restrict_nil,
        List.append_nil]

open Classical in
/-- Convergent component wirings commute with their tagged parallel composition.
The componentwise histories prove the locality asserted by the disjoint-interface view
of Jost, Thesis, printed p. 17. -/
theorem parAll_interconnect_all (hc : ∀ k, Converges (s k) (route k) (inj k)) :
    parAll (fun k => interconnect (s k) (route k) (inj k)) =
      interconnect (parAll s) (parallelRoute route) (parallelInj inj) := by
  -- Keep the induced internal history of every component at each outside prefix.
  have key : ∀ u : List (Σ k, A k), ∃ o H,
      Induces (parAll s) (parallelRoute route) (parallelInj inj) u o H ∧
      (∀ k, ∃ ok, Induces (s k) (route k) (inj k) (restrict k u) ok (restrict k H)) ∧
      ∀ c, c ∈ parAll (fun k => interconnect (s k) (route k) (inj k)) u ↔
        o = some c := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      exact ⟨none, [], Induces.nil, fun _ => ⟨none, Induces.nil⟩, by simp⟩
    | append_singleton u a ih =>
      obtain ⟨o, H, r, hrs, -⟩ := ih
      obtain ⟨k, a⟩ := a
      obtain ⟨ok, T, rk⟩ := hc k (restrict k u ++ [a])
      obtain ⟨_, _, rk0, lk⟩ := induces_snoc_iff.mp rk
      obtain ⟨_, rkH⟩ := hrs k
      obtain ⟨-, rfl⟩ := rk0.det rkH
      obtain ⟨H', l, hk, hj⟩ := lk.parallel_at H (inj k a) (by simp)
      refine ⟨_, H', Induces.snoc _ _ _ _ _ _ r l, ?_, ?_⟩
      · intro j
        by_cases he : j = k
        · subst j
          refine ⟨ok, ?_⟩
          simpa only [restrict_append, restrict_cons_self, restrict_nil, hk] using rk
        · obtain ⟨oj, rj⟩ := hrs j
          refine ⟨oj, ?_⟩
          simpa only [restrict_append, restrict_cons_ne (Ne.symm he), restrict_nil,
            List.append_nil, hj j he] using rj
      · -- The last reply is exactly the tagged reply of the active component.
        intro c
        rw [parAll_snoc, Part.mem_map_iff]
        constructor
        · rintro ⟨b, hb, rfl⟩
          obtain ⟨H'', rb⟩ := mem_interconnect.mp hb
          rw [(rk.det rb).1]
          rfl
        · intro he
          cases ok with
          | none => cases he
          | some b => cases he; exact ⟨b, mem_of_induces_some rk, rfl⟩
  -- Determinism identifies the constructed joint execution with any induced execution.
  apply system_ext
  intro u c
  obtain ⟨o, H, r, -, ho⟩ := key u
  rw [ho, mem_interconnect]
  constructor
  · rintro rfl
    exact ⟨H, r⟩
  · rintro ⟨H', r'⟩
    exact (r.det r').1

open Classical in
/-- Trimming each component preserves the completed joint behavior. -/
lemma trim_parAll_trim {A B : K → Type} (s : ∀ k, System (A k) (B k)) :
    trim (parAll fun k => trim (s k)) = trim (parAll s) := by
  -- Reachable behavior is preserved componentwise, then canonicalized jointly.
  exact (EqOnReachable.parAll fun k => trim_behEq (s k)).trim_eq
    Part.not_none_dom Part.not_none_dom


section Pair

variable {C D : K → Type}

open Classical in
/-- Regroup a pair of tagged families as a tagged family of pairs. -/
def pairParallel : Two (Σ k, A k) (Σ k, C k) ≃ Σ k, Two (A k) (C k) where
  toFun
    | ⟨none, ⟨k, a⟩⟩ => ⟨k, ⟨none, a⟩⟩
    | ⟨some (), ⟨k, c⟩⟩ => ⟨k, ⟨some (), c⟩⟩
  invFun
    | ⟨k, ⟨none, a⟩⟩ => ⟨none, ⟨k, a⟩⟩
    | ⟨k, ⟨some (), c⟩⟩ => ⟨some (), ⟨k, c⟩⟩
  left_inv := by rintro ⟨(_ | ⟨⟩), ⟨k, a⟩⟩ <;> rfl
  right_inv := by rintro ⟨k, ⟨(_ | ⟨⟩), a⟩⟩ <;> rfl

open Classical in
/-- The left component history is unchanged by regrouping. -/
lemma restrict_pairParallel_none (k : K) (h : List (Two (Σ k, A k) (Σ k, C k))) :
    restrict none (restrict k (h.map pairParallel)) = restrict k (restrict none h) := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    rcases a with ⟨(_ | ⟨⟩), ⟨j, a⟩⟩ <;> by_cases he : j = k
    all_goals first | subst j | skip
    all_goals simp_all [pairParallel]

open Classical in
/-- The right component history is unchanged by regrouping. -/
lemma restrict_pairParallel_some (k : K) (h : List (Two (Σ k, A k) (Σ k, C k))) :
    restrict (some ()) (restrict k (h.map pairParallel)) =
      restrict k (restrict (some ()) h) := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    rcases a with ⟨(_ | ⟨⟩), ⟨j, a⟩⟩ <;> by_cases he : j = k
    all_goals first | subst j | skip
    all_goals simp_all [pairParallel]

open Classical in
/-- Pairing two parallel families agrees with pairing corresponding components, after
explicit regrouping of the tagged alphabets. -/
lemma pair_parAll (s : ∀ k, System (A k) (B k)) (t : ∀ k, System (C k) (D k)) :
    pair (parAll s) (parAll t) =
      relabel (parAll fun k => pair (s k) (t k)) pairParallel pairParallel.symm := by
  apply parAll_ext
  · simp [pair, relabel]
  · intro h o a
    cases o with
    | none =>
      obtain ⟨k, a⟩ := a
      simp only [pair_left, parAll_snoc, relabel, List.map_append, List.map_singleton]
      change _ = ((parAll fun k => pair (s k) (t k))
        (h.map pairParallel ++ [⟨k, ⟨none, a⟩⟩])).map pairParallel.symm
      rw [parAll_snoc, pair_left, restrict_pairParallel_none,
        Part.map_map, Part.map_map, Part.map_map]
      rfl
    | some o =>
      cases o
      obtain ⟨k, a⟩ := a
      simp only [pair_right, parAll_snoc, relabel, List.map_append, List.map_singleton]
      change _ = ((parAll fun k => pair (s k) (t k))
        (h.map pairParallel ++ [⟨k, ⟨some (), a⟩⟩])).map pairParallel.symm
      rw [parAll_snoc, pair_right, restrict_pairParallel_some,
        Part.map_map, Part.map_map, Part.map_map]
      rfl

end Pair

end SystemAlgebra
