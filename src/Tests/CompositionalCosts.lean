import RandomSystems.DDC.SerialCost
import RandomSystems.Converter.ConverterDomain

/-!
# Restricted converters and weighted serial bounds

Two tests, on arbitrary and on concrete interfaces.

* **Weighted serial bound.** The forwarding converter `𝟙` (`idConverter`) on labels `J` with
  alphabets `X`, `Y` answers `j(x)` with the inside query `j(x)` and `j ⇒ y` with the reply
  `j ⇒ y`, so its run is at most `1`. Twice in series:

  ```text
          j(x)   ┌───┐   j(x)   ┌───┐   j(x)
    ────────────►│   ├─────────►│   ├─────────►
                 │ 𝟙 │          │ 𝟙 │
    ◄────────────┤   │◄─────────┤   │◄─────────
          j ⇒ y  └───┘   j ⇒ y  └───┘   j ⇒ y
  ```

  With certificates loosened to `100` each, `IsDDC.comp` gives `100 · 100 = 10000`;
  `IsDDC.comp_of_query_cost` with `cost m = 1` and `charge = run` of the outer `𝟙` gives `1`.
* **Outside restriction of a partial converter.** The forwarding converter limited to `q` queries
  on one port with naturals as queries and replies, `limitedForwarder q`, is a DDC from
  `queryDomain q` to `queryDomain q` that is undefined on the admissible history with `q + 1`
  outside queries, so it is not responsive. `IsDDCFrom.eq_filterDom_of_replies_le` shows that
  the one-query converter is the two-query converter restricted to one outside query.
-/

namespace SystemAlgebra.Tests.CompositionalCosts

/-- **`𝟙 ⊙ 𝟙` has run at most `1`**, from certificates loosened to `100`: each query `m(x)` of the
outer `𝟙` costs `1` inner query, and the outer charge is its own run. -/
example (J : Type) (X Y : J → Type) :
    IsDDC 1 (trim (serialM (idConverter J X Y) (idConverter J X Y))) := by
  have hi := (idConverter_isResponsiveDDC (J := J) (X := X) (Y := Y)).isDDC
  apply (hi.mono (show 1 ≤ 100 by omega)).comp_of_query_cost
    (hi.mono (show 1 ≤ 100 by omega)) (fun _ => 1) (insideRun (idConverter J X Y)) 1
  -- A query `m(x)` of the outer `𝟙` extends its run by one: `run(h z) = run(h) + 1`.
  · intro h z m x hx
    simp only [insideRun_snoc_of_mem hx, IsInside, ↓reduceIte]
  -- The charge `run` of the outer `𝟙` is at most `1`.
  · exact hi.bound
  -- The run of the inner `𝟙` is at most `1 = cost m`.
  · intro h hd m _
    exact hi.bound h hd

/-- The domain of the nonempty query histories of length at most `q`, on one port with natural
queries: `queryDomain q h ↔ 1 ≤ |h| ≤ q`. -/
def queryDomain (q : Nat) (h : List (Σ _ : Unit, Nat)) : Prop :=
  0 < h.length ∧ h.length ≤ q

/-- `queryDomain q` excludes `[]` and is closed under nonempty prefixes. -/
lemma queryDomain_prefix (q : Nat) :
    ¬ queryDomain q [] ∧ ∀ {p h}, p <+: h → p ≠ [] → queryDomain q h → queryDomain q p := by
  refine ⟨fun h => Nat.lt_irrefl 0 h.1, ?_⟩
  intro p h hp hn hh
  exact ⟨List.length_pos_iff.mpr hn, hp.length_le.trans hh.2⟩

/-- **The forwarding converter limited to `q` queries**, the filter `[q]` of CR18, §3.4.3, printed
p. 62: “[q]s is the system s restricted to q queries and is undefined as of the (q+1)-st query.”
On an admissible input history `h` with outside queries `out(h)`:

```text
  limitedForwarder q (h · ()(n))     = inside query ()(n)     if 1 ≤ |out(h · ()(n))| ≤ q
  limitedForwarder q (h · () ⇒ n′)   = outside reply () ⇒ n′  if |out(h)| ≤ q
  limitedForwarder q h               undefined               otherwise, and on h = []
```

Its domain is the alternating histories `()(n₁), () ⇒ n₁′, ()(n₂), …` with at most `q` outside
queries. -/
noncomputable def limitedForwarder (q : Nat) :
    InsideOutsideSystem Unit Unit (fun _ => Nat) (fun _ => Nat)
      (fun _ => Nat) (fun _ => Nat) :=
  (DDC.filter (fun h => h = [] ∨ queryDomain q h)
    (prefix_or_nil (queryDomain_prefix q).2)).1

/-- `limitedForwarder q` is a DDC from `queryDomain q` to `queryDomain q` with run at most `1`. -/
lemma limitedForwarder_isDDCFrom (q : Nat) :
    IsDDCFrom (queryDomain q) (queryDomain q) 1 (limitedForwarder q) :=
  isDDCFrom_filter (queryDomain_prefix q)

/-- **The one-query filter is the two-query filter restricted to one outside query.** The
two-query filter enters only through its `IsDDC` certificate: it is undefined on the third
outside query, so it is not responsive. -/
example : limitedForwarder 1 =
    filterDom (fun h => outsideInputs h = [] ∨ queryDomain 1 (outsideInputs h))
      (limitedForwarder 2) := by
  apply (limitedForwarder_isDDCFrom 1).eq_filterDom_of_replies_le
    (limitedForwarder_isDDCFrom 2).isDDC (queryDomain_prefix 1).2
  -- Remaining: every transcript of the one-query filter is one of the two-query filter. Each
  -- reply is a reply of `𝟙` on a history with at most `1 ≤ 2` outside queries.
  intro xs ys hr
  apply hr.mono
  intro h y hy
  obtain ⟨hd, hy⟩ := (filterDom_mem_iff _ _ _ _).mp hy
  apply (filterDom_mem_iff _ _ _ _).mpr
  refine ⟨?_, hy⟩
  rcases hd with he | he
  · exact Or.inl he
  · exact Or.inr ⟨he.1, he.2.trans (by omega)⟩

end SystemAlgebra.Tests.CompositionalCosts
