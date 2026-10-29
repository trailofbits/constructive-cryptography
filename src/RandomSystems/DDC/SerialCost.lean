import RandomSystems.DDC.Tensor

/-!
# Port-weighted serial converter bounds

The serial composition `β ⊙ α` (`serialM`) of an outer DDC `β`, outside labels `O` and inside
labels `M`, and an inner DDC `α`, outside labels `M` and inside labels `J`:

```text
        o(u)   ┌─────┐   m(x)   ┌─────┐   j(x')
  ────────────►│     ├─────────►│     ├──────────►
               │  β  │          │  α  │
  ◄────────────┤     │◄─────────┤     │◄──────────
        o ⇒ v  └─────┘   m ⇒ y  └─────┘   j ⇒ y'
     O                    M                  J
```

A DDC bounds its *run*, the number of consecutive inside queries: “There is a finite upper bound
on the number of consecutive outputs of the form (y, I′) ∈ 𝒳 × ℐ_in” [1, Definition 2.2.2,
printed p. 18]. `IsDDC.comp` bounds the run of `β ⊙ α` by the product `b_α · b_β`. Here the run
of `α` in an invocation at the port `m` is bounded by `cost m`, and `β` carries a `charge` on its
input histories that grows by `cost m` with each query at `m`:

```text
  run_α(h) ≤ cost m                   when α answers h and m is the label of the last outside
                                      input of h
  charge(h z) = charge(h) + cost m    when β answers h z with a query at m
  charge(h) ≤ B                       when β answers h
```

Then `β ⊙ α` has at most `B` consecutive inside queries. After an outside reply, the charge may
restart, subject to `charge ≤ B`. The bound is a refinement derived here,
not a statement of [1]; it bounds consecutive inside queries, not their total over invocations.

The proof follows the composite's run `c` along the joint history of `[β, α]`, with `H_β` and
`H_α` the input histories of `β` and `α`. While `β` is about to answer, `c ≤ charge(H_β)`. While
`α` is about to answer in an invocation at `m`, the charge reserves `cost m` for that invocation:

```text
  cost m ≤ charge(H_β)    and    c ≤ (charge(H_β) − cost m) + run_α(H_α)
```

## Main definitions

* `serialCostAtOuter`, `serialCostAtInner`: the charge invariant while `β`, resp. `α`, is about
  to answer

The conclusion bounds the composite's consecutive run. It does not bound its aggregate work
over all outside invocations. `RandomSystems.Converter.SerialAccounting` provides the
aggregate theorem, with query-value-dependent costs and a hypothesis on every partial
component transcript.

## Main results

* `IsDDC.insideRun_prefix_le_cost`: the run of `α` before its last input is within the cost
* `serialM_exchange_cost`: one exchange of `[β, α]` exposing an inside query keeps the invariant
* `IsDDC.comp_of_query_cost`: the composite's run is at most the bound `B` on the charge

## References

1. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis, ETH Zurich, 2020.
-/

namespace SystemAlgebra

section SerialCost

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}
  {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}
  {bβ bα : Nat}

/-- **The run before the last input is within the cost**: if `run_α(h) ≤ cost m` on every answered
history `h` whose last outside input is at `m`, then also `run_α(h) ≤ cost m` when `α` answers
`h z` and the last outside input of `h z` is at `m`. This bounds a run that `α` has just closed by
its outside reply `m ⇒ y`. -/
lemma IsDDC.insideRun_prefix_le_cost (hα : IsDDC bα α) (cost : M → Nat)
    (hc : ∀ h, (α h).Dom → ∀ m, lastOuter h = some m → insideRun α h ≤ cost m)
    {h z m} (hd : (α (h ++ [z])).Dom) (hm : lastOuter (h ++ [z]) = some m) :
    insideRun α h ≤ cost m := by
  rcases z with ⟨⟨_ | ⟨⟩, port⟩, z⟩
  -- `z` is an outside input: no inside query is pending, so `run_α(h) = 0`.
  · rw [insideRun_eq_zero_of_admits_outside (hα.admits _ _ hd)]
    exact Nat.zero_le _
  -- `z` is an inside reply: `α` answers the prefix `h`, whose last outside input is still at `m`.
  · rcases eq_or_ne h [] with rfl | hn
    · exact Nat.zero_le _
    · apply hc h (hα.dds.2 ⟨_, rfl⟩ hn hd) m
      simpa only [lastOuter_snoc, outerOf, Option.none_or] using hm

/-- **The invariant while `β` is about to answer.** The joint history of `[β, α]` is
`G = G₁ · z` with `z` an input of `β`, and the charge before `z` covers the composite's run `c`:
`c ≤ charge(H_β(G₁))`, where `H_β = restrict none` is the input history of `β`. -/
def serialCostAtOuter (charge : List (Σ l, twoFam U Ym l) → Nat) (c : Nat)
    (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) : Prop :=
  ∃ G₁ z, G = G₁ ++ [⟨none, z⟩] ∧ c ≤ charge (restrict none G₁)

/-- **The invariant while `α` is about to answer.** The joint history is `G = G₁ · z` with `z` an
input of `α` in an invocation at `m`, the label of the last outside input of `H_α(G₁) · z`, where
`H_α = restrict (some ())` is the input history of `α`. The charge reserves `cost m`, and the
remainder plus the run of `α` covers the composite's run `c`:

```text
  cost m ≤ charge(H_β(G₁))    and    c ≤ (charge(H_β(G₁)) − cost m) + run_α(H_α(G₁))
```

The first condition makes the natural-number subtraction exact. -/
def serialCostAtInner (α : InsideOutsideSystem M J Xm Ym X Y)
    (cost : M → Nat) (charge : List (Σ l, twoFam U Ym l) → Nat) (c : Nat)
    (G : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) : Prop :=
  ∃ G₁ z m, G = G₁ ++ [⟨some (), z⟩] ∧
    lastOuter (restrict (some ()) G₁ ++ [z]) = some m ∧
    cost m ≤ charge (restrict none G₁) ∧
    c ≤ charge (restrict none G₁) - cost m + insideRun α (restrict (some ()) G₁)

/-- **One exchange keeps the invariant.** An exchange of `[β, α]` passes one input along the
serial wiring until an output leaves. If the invariant holds for `c` at its start `G`, and it
exposes an inside query `j(x′)` of the composite, the invariant for `α` holds for `c + 1` at its
end `G'`. Inside the exchange, a query `m(x)` of `β` raises the charge by `cost m`, reserved for
`α`, and a reply `m ⇒ y` of `α` releases it after a run of at most `cost m`. -/
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
    -- An output of `[β, α]` leaves the wiring.
    intro w' j he hw
    cases he
    rcases hs with ⟨G₁, z, rfl, hc⟩ | ⟨G₁, z, m, rfl, hm, hmle, hc⟩
    -- An output of `β` leaves only as an outside reply `o ⇒ v`, not as an inside query.
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, port⟩, y⟩
      · simp only [serialRouteM, Sum.inl.injEq] at hr
        subst w
        cases hw
      · cases hr
    -- An inside query `j(x′)` of `α` leaves: the charge is unchanged and `run_α` grows by one.
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
    -- An output of `[β, α]` is fed to the other component; the invariant moves with it.
    apply ih c
    rcases hs with ⟨G₁, z, rfl, hc⟩ | ⟨G₁, z, m, rfl, hm, hmle, hc⟩
    -- `β` queries `m(x)`, which becomes an outside input of `α` at `m`. With `H_β' = H_β · z`,
    -- `charge(H_β') = charge(H_β) + cost m`, so `cost m ≤ charge(H_β')` and
    -- `c ≤ charge(H_β) = charge(H_β') − cost m`.
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
    -- `α` replies `m ⇒ y` at the label of its invocation, which `β` receives. The closed run
    -- has `run_α(H_α) ≤ cost m`, so `c ≤ charge(H_β) − cost m + run_α(H_α) ≤ charge(H_β)`.
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


/-- **Port-weighted serial bound**: the composite `β ⊙ α` has at most `bound` consecutive inside
queries when

```text
  charge(h z) = charge(h) + cost m    whenever β answers h z with a query m(x)      (hcharge)
  charge(h) ≤ bound                   whenever β answers h                           (hbound)
  run_α(h) ≤ cost m                   whenever α answers h, last outside input at m  (hcost)
```

A refinement, derived here, of the bounded run of [1, Definition 2.2.2, printed p. 18]: “There
is a finite upper bound on the number of consecutive outputs of the form (y, I′) ∈ 𝒳 × ℐ_in.”
With `cost m = b_α` and `charge = b_α · run_β` it recovers `IsDDC.comp`. It bounds one run, not
the total inside queries over all invocations; after an outside reply, `charge` may restart
subject to `hbound`. -/
theorem IsDDC.comp_of_query_cost (hβ : IsDDC bβ β) (hα : IsDDC bα α)
    (cost : M → Nat) (charge : List (Σ l, twoFam U Ym l) → Nat) (bound : Nat)
    (hcharge : ∀ h z m x, (⟨⟨some (), m⟩, x⟩ : Σ l, twoFam V Xm l) ∈ β (h ++ [z]) →
      charge (h ++ [z]) = charge h + cost m)
    (hbound : ∀ h, (β h).Dom → charge h ≤ bound)
    (hcost : ∀ h, (α h).Dom → ∀ m, lastOuter h = some m → insideRun α h ≤ cost m) :
    IsDDC bound (trim (serialM β α)) := by
  classical
  -- On each reachable composite history `u` whose last output is an inside query, with joint
  -- history `H` and `α` in an invocation at `m`:
  -- `cost m ≤ charge(H_β)` and `run(u) ≤ charge(H_β) − cost m + run_α(H_α)`.
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
      -- The composite is silent on the empty history.
      intro _ o H r w j he _
      obtain ⟨ho, _⟩ := r.det Induces.nil
      rw [he] at ho
      cases ho
    | append_singleton u a ih =>
      -- The next input `a` is admitted after the composite's last output on `u`.
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
      -- The invariant holds with `c = run(u)` when `a` enters the wiring.
      have start : serialCostAtOuter charge (insideRun (serialM β α) u)
          (H ++ [serialInjM a]) ∨
          serialCostAtInner α cost charge (insideRun (serialM β α) u)
            (H ++ [serialInjM a]) := by
        rcases a with ⟨⟨_ | ⟨⟨⟩⟩, port⟩, a⟩
        -- An outside input at `port` goes to `β`. It is admitted only after a non-inside output,
        -- also on the silent `u = []`, so `run(u) = 0 ≤ charge(H_β)`.
        · apply Or.inl
          refine ⟨H, _, rfl, ?_⟩
          have ha : Admits (serialM β α) u ⟨⟨none, port⟩, a⟩ := by
            rwa [Admits, replyLabel_serialM r]
          rw [insideRun_eq_zero_of_admits_outside ha]
          exact Nat.zero_le _
        -- An inside reply `j ⇒ y` goes to `α`. It is admitted only after the composite's inside
        -- query `j(x′)`, where the hypothesis gives the invariant; `α`'s invocation is unchanged.
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
      -- The exchange ends with the inside query `w`, so `run(u · a) = run(u) + 1`.
      refine ⟨m, hm, hmle, ?_⟩
      have hy : w ∈ serialM β α (u ++ [a]) := mem_of_induces_some r'
      rw [insideRun_snoc_of_mem hy, if_pos (show IsInside w from congrArg Sigma.fst hw)]
      exact hc
  -- The other DDC conditions are those of `IsDDC.comp`; only the run bound changes.
  refine { hβ.comp hα with bound := ?_ }
  intro u hd
  have hr := reach_of_trim hd
  rw [insideRun, run_trim _ _ hr]
  obtain ⟨o, H, r, ⟨_, hs⟩, _⟩ := serialM_reach_partial hβ hα u hr
  -- Only the pending-inner case has a nonzero composite run.
  rcases hs with ⟨rfl, _, _⟩ | ⟨w, rfl, ⟨port, hw⟩, _, _⟩ |
      ⟨w, j, m, port, rfl, hw, _, hwa, hwb, _, _⟩
  -- Empty history: `run([]) = 0`.
  · exact Nat.zero_le _
  -- Last output an outside reply `o ⇒ v`: `run(u) = 0`.
  · change insideRun (serialM β α) u ≤ bound
    rw [insideRun_eq_zero_of_outer (by rw [replyLabel_serialM r, Option.map_some, hw])]
    exact Nat.zero_le _
  -- Last output an inside query: `β` and `α` both wait on answered histories, so
  -- `run(u) ≤ charge(H_β) − cost m + run_α(H_α) ≤ charge(H_β) ≤ bound` by `hcost` and `hbound`.
  · obtain ⟨m', hm', _, hc⟩ := cost_reach u hr _ _ r w j rfl hw
    have ha := hcost _ hwa.2.1 m' hm'
    have hb := hbound _ hwb.2.1
    change insideRun (serialM β α) u ≤ bound
    omega

end SerialCost

end SystemAlgebra
