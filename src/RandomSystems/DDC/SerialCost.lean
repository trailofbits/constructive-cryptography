import RandomSystems.DDC.Tensor

/-!
# Port-weighted serial converter bounds

The intermediate query port determines the inner converter's consecutive-run cost. The outer
converter's charge increases by that cost when it issues the query. This refines the existing
serial DDC run bound without changing its domain or serial wiring.

The conclusion bounds the composite's *consecutive run*. It does not bound its aggregate work
over all outside invocations. `RandomSystems.Converter.SerialAccounting` provides the
separate aggregate theorem, with query-value-dependent costs and a hypothesis on every
partial component transcript.
-/

namespace SystemAlgebra

section SerialCost

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}
  {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}
  {bβ bα : Nat}

/-- A pending outside input cannot follow an inside query. -/
lemma insideRun_eq_zero_of_admits_outside {O J : Type} {U V : O → Type} {X Y : J → Type}
    {a : InsideOutsideSystem O J U V X Y} {h} {o : O} {u : U o}
    (ha : Admits a h ⟨⟨none, o⟩, u⟩) : insideRun a h = 0 := by
  classical
  rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
  · rfl
  · rw [List.concat_eq_append] at ha ⊢
    rw [insideRun, run_snoc, if_neg]
    rintro ⟨y, hy, hi⟩
    rw [Admits, replyLabel_of_mem _ hy] at ha
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, port⟩, y⟩
    · exact absurd hi (by simp only [IsInside, reduceCtorEq, not_false_eq_true])
    · cases ha

/-- The run just before a response is bounded by the cost of its current outside port. -/
lemma IsDDC.insideRun_prefix_le_cost (hα : IsDDC bα α) (cost : M → Nat)
    (hc : ∀ h, (α h).Dom → ∀ m, lastOuter h = some m → insideRun α h ≤ cost m)
    {h z m} (hd : (α (h ++ [z])).Dom) (hm : lastOuter (h ++ [z]) = some m) :
    insideRun α h ≤ cost m := by
  rcases z with ⟨⟨_ | ⟨⟩, port⟩, z⟩
  · rw [insideRun_eq_zero_of_admits_outside (hα.admits _ _ hd)]
    exact Nat.zero_le _
  · rcases eq_or_ne h [] with rfl | hn
    · exact Nat.zero_le _
    · apply hc h (hα.dds.2 ⟨_, rfl⟩ hn hd) m
      simpa only [lastOuter_snoc, outerOf, Option.none_or] using hm

/-- The outer converter is about to answer; `c` queries have already been exposed. -/
def serialCostAtOuter (charge : List (Σ l, twoFam U Ym l) → Nat) (c : Nat)
    (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) : Prop :=
  ∃ G₁ z, G = G₁ ++ [⟨none, z⟩] ∧ c ≤ charge (restrict none G₁)

/-- The inner converter is about to answer a call at `m`; reserve that port's cost. -/
def serialCostAtInner (α : InsideOutsideSystem M J Xm Ym X Y)
    (cost : M → Nat) (charge : List (Σ l, twoFam U Ym l) → Nat) (c : Nat)
    (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) : Prop :=
  ∃ G₁ z m, G = G₁ ++ [⟨some (), z⟩] ∧
    lastOuter (restrict (some ()) G₁ ++ [z]) = some m ∧
    cost m ≤ charge (restrict none G₁) ∧
    c ≤ charge (restrict none G₁) - cost m + insideRun α (restrict (some ()) G₁)

/-- A serial exchange preserves the sum of the costs of the outer queries. -/
lemma serialM_exchange_cost (hα : IsDDC bα α) (cost : M → Nat)
    (charge : List (Σ l, twoFam U Ym l) → Nat)
    (hcharge : ∀ h z m x, (⟨⟨some (), m⟩, x⟩ : Σ l, twoFam V Xm l) ∈ β (h ++ [z]) →
      charge (h ++ [z]) = charge h + cost m)
    (hcost : ∀ h, (α h).Dom → ∀ m, lastOuter h = some m → insideRun α h ≤ cost m)
    {G o G'} (ex : Exchange (pair β α) serialRouteM G o G')
    (c : Nat) (hs : serialCostAtOuter charge c G ∨ serialCostAtInner α cost charge c G) :
    ∀ w j, o = some w → w.1 = ⟨some (), j⟩ →
      ∃ m, lastOuter (restrict (some ()) G') = some m ∧
        cost m ≤ charge (restrict none G') ∧
        c + 1 ≤ charge (restrict none G') - cost m + insideRun α (restrict (some ()) G') := by
  classical
  induction ex generalizing c with
  | silent G hd =>
    -- A silent exchange cannot expose an inside query.
    intro w j he; cases he
  | out G y w hy hr =>
    -- An exposed query extends the current inner run after its reserved charge.
    intro w' j he hw
    cases he
    rcases hs with ⟨G₁, z, rfl, hc⟩ | ⟨G₁, z, m, rfl, hm, hmle, hc⟩
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, port⟩, y⟩
      · simp only [serialRouteM, Sum.inl.injEq] at hr
        subst w
        cases hw
      · cases hr
    · rw [pair_right] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, port⟩, y⟩
      · cases hr
      · simp only [serialRouteM, Sum.inl.injEq] at hr
        subst w
        refine ⟨m, ?_, ?_, ?_⟩
        · simpa only [restrict_some_snoc_right] using hm
        · simpa only [restrict_none_snoc_right] using hmle
        · rw [restrict_none_snoc_right, restrict_some_snoc_right,
            insideRun_snoc_of_mem hy']
          simp only [IsInside, ↓reduceIte]
          omega
  | feed G y x o G'' hy hr ex ih =>
    -- A fed outer query reserves its port cost; a fed inner answer closes that run.
    apply ih c
    rcases hs with ⟨G₁, z, rfl, hc⟩ | ⟨G₁, z, m, rfl, hm, hmle, hc⟩
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, port⟩, y⟩
      · cases hr
      · simp only [serialRouteM, Sum.inr.injEq] at hr
        subst x
        refine Or.inr ⟨_, _, port, rfl, ?_, ?_, ?_⟩
        · rw [restrict_some_snoc_left, lastOuter_snoc]; rfl
        · rw [restrict_none_snoc_left, hcharge _ _ port y hy']
          omega
        · rw [restrict_none_snoc_left, restrict_some_snoc_left, hcharge _ _ port y hy']
          omega
    · rw [pair_right] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, port⟩, y⟩
      · simp only [serialRouteM, Sum.inr.injEq] at hr
        subst x
        have hp := hα.replies _ _ port hy' rfl
        rw [hm] at hp
        have he : m = port := Option.some.inj hp
        subst port
        have hb := hα.insideRun_prefix_le_cost cost hcost (Part.dom_iff_mem.mpr ⟨_, hy'⟩) hm
        refine Or.inl ⟨_, _, rfl, ?_⟩
        rw [restrict_none_snoc_right]
        omega
      · cases hr


/-- Serial composition can use port-dependent inner bounds and the sum charged by the
outer converter, while retaining the existing DDC and serial-wiring definitions. Jost,
Definition 2.2.2, printed pp. 17–18: “Upon an input at an outside interface, the converter is
allowed to make a bounded number of queries to the inside interfaces ... before returning a
value at the queried interface.” This theorem refines the numerical consecutive-run bound. -/
lemma IsDDC.comp_of_query_cost (hβ : IsDDC bβ β) (hα : IsDDC bα α)
    (cost : M → Nat) (charge : List (Σ l, twoFam U Ym l) → Nat) (bound : Nat)
    (hcharge : ∀ h z m x, (⟨⟨some (), m⟩, x⟩ : Σ l, twoFam V Xm l) ∈ β (h ++ [z]) →
      charge (h ++ [z]) = charge h + cost m)
    (hbound : ∀ h, (β h).Dom → charge h ≤ bound)
    (hcost : ∀ h, (α h).Dom → ∀ m, lastOuter h = some m → insideRun α h ≤ cost m) :
    IsDDC bound (trim (serialM β α)) := by
  classical
  -- Preserve the charge invariant over each reachable serial input prefix.
  have cost_reach : ∀ u, Reach (serialM β α) u → ∀ o H,
      Induces (pair β α) serialRouteM serialInjM u o H →
      ∀ w j, o = some w → w.1 = ⟨some (), j⟩ →
        ∃ m, lastOuter (restrict (some ()) H) = some m ∧
          cost m ≤ charge (restrict none H) ∧
          insideRun (serialM β α) u ≤
            charge (restrict none H) - cost m + insideRun α (restrict (some ()) H) := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      intro _ o H r w j he _
      obtain ⟨ho, _⟩ := r.det Induces.nil
      rw [he] at ho
      cases ho
    | append_singleton u a ih =>
      -- Admission selects either a fresh outside invocation or a pending inner continuation.
      intro hr o' H' r' w j he hw
      subst o'
      obtain ⟨hr0, _⟩ := reach_snoc_iff.mp hr
      obtain ⟨o, H, r, hs, _⟩ := serialM_reach_partial hβ hα u hr0
      obtain ⟨_, H0, r0, ex⟩ := induces_snoc_iff.mp r'
      obtain ⟨rfl, rfl⟩ := r.det r0
      have had : admitAfter (o.map (·.1)) a.1 := by
        by_contra hn
        have hf := (serialM_next_partial hβ hα r hs a).2 hn _ _ r'
        cases hf
      have start : serialCostAtOuter charge (insideRun (serialM β α) u)
          (H ++ [serialInjM a]) ∨
          serialCostAtInner α cost charge (insideRun (serialM β α) u)
            (H ++ [serialInjM a]) := by
        rcases a with ⟨⟨_ | ⟨⟨⟩⟩, port⟩, a⟩
        · apply Or.inl
          refine ⟨H, _, rfl, ?_⟩
          have ha : Admits (serialM β α) u ⟨⟨none, port⟩, a⟩ := by
            rwa [Admits, replyLabel_serialM r]
          rw [insideRun_eq_zero_of_admits_outside ha]
          exact Nat.zero_le _
        · cases o with
          | none => cases had
          | some old =>
            rcases old with ⟨⟨_ | ⟨⟨⟩⟩, oldPort⟩, v⟩
            · cases had
            · obtain ⟨m, hm, hmle, hc⟩ := ih hr0 _ _ r _ oldPort rfl rfl
              refine Or.inr ⟨H, _, m, rfl, ?_, hmle, hc⟩
              simpa only [lastOuter_snoc, outerOf, Option.none_or] using hm
      obtain ⟨m, hm, hmle, hc⟩ := serialM_exchange_cost hα cost charge hcharge hcost
        ex (insideRun (serialM β α) u) start w j rfl hw
      -- The final exposed output is one more query of the current inner run.
      refine ⟨m, hm, hmle, ?_⟩
      have hy : w ∈ serialM β α (u ++ [a]) := mem_of_induces_some r'
      rw [insideRun_snoc_of_mem hy, if_pos (show IsInside w from congrArg Sigma.fst hw)]
      exact hc
  refine { hβ.comp hα with bound := ?_ }
  intro u hd
  have hr := reach_of_trim hd
  rw [insideRun, run_trim _ _ hr]
  obtain ⟨o, H, r, ⟨_, hs⟩, _⟩ := serialM_reach_partial hβ hα u hr
  -- Only the pending-inner case has a nonzero composite run.
  rcases hs with ⟨rfl, _, _⟩ | ⟨w, rfl, ⟨port, hw⟩, _, _⟩ |
      ⟨w, j, m, port, rfl, hw, _, hwa, hwb, _, _⟩
  · exact Nat.zero_le _
  · change insideRun (serialM β α) u ≤ bound
    rw [insideRun_eq_zero_of_outer (by rw [replyLabel_serialM r, Option.map_some, hw])]
    exact Nat.zero_le _
  · obtain ⟨m', hm', _, hc⟩ := cost_reach u hr _ _ r w j rfl hw
    have ha := hcost _ hwa.2.1 m' hm'
    have hb := hbound _ hwb.2.1
    change insideRun (serialM β α) u ≤ bound
    omega

end SerialCost

end SystemAlgebra
