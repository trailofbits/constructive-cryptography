module

public import RandomSystems.Cumulative.Attachment.Finite

/-!
# Normalized cumulative attachment

`IsRandomSystem.attachMass_isRandomSystem` glues coherent finite attachments on the outside
input domain. `cut_attachMass` recovers every finite attachment with a sufficient inside
horizon. `attachMass_eq_of_queryBound` shows that the cumulative behavior is independent of
the chosen total-query bound: two witnesses use the same finite assembly at a common horizon.
`attachMass_eq_attach` recovers existing deterministic attachment on bounded input domains.
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

/-- The cumulative attachment is normalized on the converter's outside input domain. -/
theorem attachMass_isRandomSystem :
    IsRandomSystem (fun h x => F (h.map Prod.fst ++ [x]))
      (attachMass hE hF ha hk mono hp ports) :=
  RandomSystem.limitMass_isRandomSystem _ _ (attachCut_coherent hE hF ha hk mono hp ports)

/-- The cumulative attachment gives zero mass to a reply at a different outside port. -/
lemma attachMass_repliesAtQueriedInterface
    -- `h` is the prior transcript and `x`/`y` the next query/reply, at distinct ports.
    (h : List ((Σ o, U o) × (Σ o, V o))) (x : Σ o, U o) (y : Σ o, V o)
    (hne : y.1 ≠ x.1) : attachMass hE hF ha hk mono hp ports (h ++ [(x, y)]) = 0 :=
  attachCut_repliesAtQueriedInterface hE hF ha hk mono hp ports
    (h ++ [(x, y)]).length _ le_rfl h x y hne

/-- Observing through `q` recovers the finite assembly at any sufficient inside horizon `n`. -/
lemma cut_attachMass
    -- `hkn` ensures that `n` covers all inside queries through outside horizon `q`.
    (q n : ℕ) (hkn : k q ≤ n) :
    IsRandomSystem.cut _ (attachMass hE hF ha hk mono hp ports)
      (attachMass_isRandomSystem hE hF ha hk mono hp ports) q =
      attachCut hE hF ha hk mono hp ports q n hkn :=
  (RandomSystem.cut_limitMass _ _ (attachCut_coherent hE hF ha hk mono hp ports) q).trans
    (attachCut_eq_of_le hE hF ha hk mono hp ports q n hkn).symm

/-- Two total-query witnesses for the same converter give the same cumulative attachment. -/
lemma attachMass_eq_of_queryBound
    -- `hl`/`monol` give the alternative monotone total-query bound `l` for the same `α`.
    {l : ℕ → ℕ} (hl : InsideQueriesBounded α l) (monol : Monotone l) :
    attachMass hE hF ha hk mono hp ports = attachMass hE hF ha hl monol hp ports := by
  funext h
  -- Both finite assemblies use the larger of their two sufficient inside horizons.
  let n := max (k h.length) (l h.length)
  change attachCut hE hF ha hk mono hp ports h.length (k h.length) le_rfl h =
    attachCut hE hF ha hl monol hp ports h.length (l h.length) le_rfl h
  calc
    _ = attachCut hE hF ha hk mono hp ports h.length n (le_max_left _ _) h :=
      congrArg (fun R => R h)
        (attachCut_eq_of_le hE hF ha hk mono hp ports h.length n (le_max_left _ _)).symm
    _ = attachCut hE hF ha hl monol hp ports h.length n (le_max_right _ _) h := rfl
    _ = _ := congrArg (fun R => R h)
      (attachCut_eq_of_le hE hF ha hl monol hp ports h.length n (le_max_right _ _))

/-- On bounded input domains, cumulative attachment is the existing deterministic attachment. -/
lemma attachMass_eq_attach
    -- `m`/`n` bound the admitted inside/outside histories, respectively.
    {m n : ℕ} (hEm : ∀ xs, E xs → xs.length ≤ m) (hFn : ∀ xs, F xs → xs.length ≤ n)
    -- `R` is the bounded resource; `hR` is its reply-port contract.
    (R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hEm))
    (hR : R.RepliesAtQueriedInterface) :
    attachMass hE hF ha hk mono R.2 hR =
      (PDCBehavior.attach hE hF
        (PDCBehavior.ofDDC α ha : PDCBehavior O J U V X Y E m hEm F n hFn) R hR :
        List ((Σ o, U o) × (Σ o, V o)) → ℝ) := by
  -- The bounded inside domain supplies a constant total-query witness.
  have bound := ha.insideQueriesBounded_of_domain hEm
  rw [attachMass_eq_of_queryBound hE hF ha hk mono R.2 hR bound monotone_const]
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation hE R hR
  -- Retag the same samples with the redundant length certificate; no sample is changed.
  let retag : {s : InterfaceSystem J X Y // IsDDS s ∧ RepliesAtQueriedInterface s ∧
      ∀ xs, (s xs).Dom ↔ E xs} →
      {s : InterfaceSystem J X Y // IsDDS s ∧ RepliesAtQueriedInterface s ∧
      ∀ xs, (s xs).Dom ↔ E xs ∧ xs.length ≤ m} := fun s =>
    ⟨s.1, s.2.1, s.2.2.1, fun xs => (s.2.2.2 xs).trans
      ⟨fun hx => ⟨hx, hEm xs hx⟩, fun hx => hx.1⟩⟩
  have mapped (g) : behaviorMass (Q.map retag).1
      (g.map Prod.fst) (g.map Prod.snd) = SystemAlgebra.cutMass R m g := by
    rw [ProbDist.map_val, behaviorMass, mass_fTransform]
    change behaviorMass Q.1 (g.map Prod.fst) (g.map Prod.snd) = SystemAlgebra.cutMass R m g
    rw [hQ]
    exact (congrFun (RandomSystem.cut_bound_val R) g).symm
  funext h
  change attachCut hE hF ha bound monotone_const R.2 hR h.length m le_rfl h = _
  rw [attachCut_presents hE hF ha bound monotone_const R.2 hR _ _ le_rfl _ mapped,
    PDCBehavior.attach_ofDDC_presents hE hF α ha R hR Q hQ,
    ProbDist.map_val, mass_fTransform]
  -- The raw outside-cut law removes the filter at this transcript's own length.
  apply mass_congr Q.1
  intro s
  rw [apply_filterDom_outside_length]
  exact replies_cutSystem_iff _ _ (by rw [List.length_map])

end SystemAlgebra.IsRandomSystem
