module

public import RandomSystems.Converter.Calls

/-!
# Payload-weighted accounting for direct calls

`callRule_query_count` in `RandomSystems.Converter.Calls` counts inside queries, and
`currentCall_query_charge` charges them by port. Here the charge `charge x` of an inside
request `x : Σ j, X j` may depend on its entire payload, for example the number of compression
blocks of a hash input. Each outside invocation `u` reserves a list of charges `charges u`;
the `k`-th inside request of the invocation is paid from the `k`-th reservation, and the unused
suffix is retained, so completed and interrupted invocations satisfy the same inequality:

```text
  outside u   reserve  Σ charges(u)
  inside x    pay charge(x) + Σ drop(k + 1, charges(u)) ≤ Σ drop(k, charges(u))
  total       Σ_{inside x} charge(x) ≤ Σ_{outside u} Σ charges(u)
```

`callRule_query_charge_le` is the bound for arbitrary replies.
`callConverter_query_charge_le` specializes it to the domain-restricted canonical converter.
With a charge depending only on the port, the sum counts per-port work. In a serial
composition, this bound supplies the inner work premise of `IsDDCFrom.comp_query_charge_le`.

-/

@[expose] public section

namespace SystemAlgebra

/-- If, in invocation
`(u, [r₁, …, rₖ])`, every issued request `x` satisfies

`charge x + Σ drop (k + 1) (charges u) ≤ Σ drop k (charges u)`   (`hcharge`),

then every transcript of `callRule call` charges its inside requests at most the sum of the
reservations `Σ charges u` of its outside inputs. The hypothesis quantifies over arbitrary
reply lists; no functional consistency of the inside system is needed. -/
theorem callRule_query_charge_le {O J : Type} {U V : O → Type} {X Y : J → Type}
    -- `call u rs` returns at `u.1` or issues the next inside request, given replies `rs`.
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    -- `charge x` is the cost of request `x`; `charges u` reserves costs position by position.
    (charge : (Σ j, X j) → Nat) (charges : (Σ o, U o) → List Nat)
    -- `hcharge`: the request at position `k = rs.length` is paid from that position onward.
    (hcharge : ∀ u rs x, call u rs = .inr x →
      charge x + ((charges u).drop (rs.length + 1)).sum ≤
        ((charges u).drop rs.length).sum)
    -- `T` is a transcript of the raw call rule.
    (T : List (_ × _)) (hr : Replies (callRule call) (T.map Prod.fst) (T.map Prod.snd)) :
    ((insideQueries (T.map Prod.snd)).map charge).sum ≤
      ((outsideInputs (T.map Prod.fst)).map fun u => (charges u).sum).sum := by
  -- The unpaid suffix of the current invocation's reservation.
  let remaining (h : List (Σ l, twoFam U Y l)) :=
    match currentCall h.reverse [] with
    | none => 0
    | some (u, rs) => ((charges u).drop (rs.length + 1)).sum
  -- One output of the rule is paid from the reservation at its position.
  have next h u rs y (hc : currentCall h.reverse [] = some (u, rs))
      (hy : y ∈ callRule call h) :
      ((insideQueries [y]).map charge).sum + remaining h ≤
        ((charges u).drop rs.length).sum := by
    cases he : call u rs with
    | inl v =>
      -- A return issues nothing and keeps at most the current suffix.
      simp only [callRule, hc, he, Part.mem_some_iff] at hy
      subst y
      simp only [insideQueries_outside, List.map_nil, List.sum_nil, zero_add, remaining, hc]
      exact (List.drop_sublist_drop_left _ (Nat.le_succ _)).sum_le_sum (fun n _ => Nat.zero_le n)
    | inr x =>
      -- A request pays `charge x` and retains the next suffix (`hcharge`).
      simp only [callRule, hc, he, Part.mem_some_iff] at hy
      subst y
      simpa only [insideQueries_inside, List.map_singleton, List.sum_singleton, remaining, hc]
        using hcharge u rs x he
  -- Invariant: charges paid plus the retained suffix never exceed the reservations.
  suffices bound : ∀ T : List (_ × _),
      Replies (callRule call) (T.map Prod.fst) (T.map Prod.snd) →
      ((insideQueries (T.map Prod.snd)).map charge).sum + remaining (T.map Prod.fst) ≤
        ((outsideInputs (T.map Prod.fst)).map fun u => (charges u).sum).sum from
    (Nat.le_add_right _ _).trans (bound T hr)
  intro T
  induction T using List.reverseRecOn with
  | nil => intro _; exact Nat.le_refl 0
  | append_singleton T z ih =>
    intro hr
    obtain ⟨x, y⟩ := z
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr, hy⟩ := replies_snoc.mp hr
    have hi := ih hr
    have hym := Part.eq_some_iff.mp hy
    simp only [insideQueries_append, outsideInputs_append, List.map_append, List.sum_append]
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
    · -- An outside query adds its whole reservation and starts a fresh invocation.
      have hc : currentCall ((T.map Prod.fst) ++
          [(⟨⟨none, i⟩, x⟩ : Σ l, twoFam U Y l)]).reverse [] = some (⟨i, x⟩, []) := by
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          currentCall]
      have hn := next _ _ _ y hc hym
      simp only [List.length_nil, List.drop_zero, remaining, hc] at hn
      rw [outsideInputs_outside, List.map_singleton, List.sum_singleton]
      simp only [remaining, List.map_append, List.map_singleton, hc, List.length_nil]
      omega
    · -- An inside reply advances the reservation by one position.
      have hc : currentCall ((T.map Prod.fst) ++
          [(⟨⟨some (), i⟩, x⟩ : Σ l, twoFam U Y l)]).reverse [] =
          (currentCall (T.map Prod.fst).reverse []).map
            (fun (u, rs) => (u, rs ++ [⟨i, x⟩])) := by
        simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
          currentCall]
        exact currentCall_acc _ _
      cases he : currentCall (T.map Prod.fst).reverse [] with
      | none =>
        -- Without a current invocation the rule is silent, so no reply was admitted.
        simp only [callRule, hc, he, Option.map_none] at hym
        exact (Part.notMem_none _ hym).elim
      | some ur =>
        obtain ⟨u, rs⟩ := ur
        rw [he, Option.map_some] at hc
        have hn := next _ _ _ y hc hym
        simp only [List.length_append, List.length_singleton] at hn
        simp only [remaining, he] at hi
        rw [outsideInputs_inside, List.map_nil, List.sum_nil, Nat.add_zero]
        simpa only [remaining, List.map_append, List.map_singleton] using
          (Nat.add_assoc _ _ _).le.trans ((Nat.add_le_add_left hn _).trans hi)

/-- Every transcript of the canonical direct-call converter satisfies its payload-charge bound,
including a final inside request whose reply is pending. -/
lemma callConverter_query_charge_le {O J : Type} {U V : O → Type} {X Y : J → Type}
    (call : (u : Σ o, U o) → List (Σ j, Y j) → V u.1 ⊕ (Σ j, X j))
    -- `charge x` is the work of an issued request, and `charges u` reserves work for invocation u.
    (charge : (Σ j, X j) → Nat) (charges : (Σ o, U o) → List Nat)
    (hcharge : ∀ u rs x, call u rs = .inr x →
      charge x + ((charges u).drop (rs.length + 1)).sum ≤ ((charges u).drop rs.length).sum)
    -- `F` admits outside histories; `T` is a transcript of the resulting converter.
    (F : List (Σ o, U o) → Prop) (T : List (_ × _))
    (hr : Replies (callConverter call F) (T.map Prod.fst) (T.map Prod.snd)) :
    ((insideQueries (T.map Prod.snd)).map charge).sum ≤
      ((outsideInputs (T.map Prod.fst)).map fun u => (charges u).sum).sum :=
  callRule_query_charge_le call charge charges hcharge T
    (hr.mono fun h y hy => canon_mem ((filterDom_mem_iff _ _ h y).mp hy).2)

end SystemAlgebra
