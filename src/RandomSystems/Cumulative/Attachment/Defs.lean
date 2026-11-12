module

public import RandomSystems.Converter.FiniteCuts
public import RandomSystems.Converter.ConverterAttachment
public import RandomSystems.Cumulative.FiniteCuts

/-!
# Cumulative attachment through finite observations

`IsRandomSystem.attachCut` attaches a fixed converter through `q` outside queries to the
resource cut at any sufficient inside horizon `n ≥ k q`. The bounded attachment samples the
resource once and retains it throughout the interaction. `IsRandomSystem.attachMass` reads
these attachments at the observed transcript's length.

```text
outside horizon q ──▶ α restricted to q ──▶ resource cut at n ≥ k q
```
-/

@[expose] public section

namespace SystemAlgebra.IsRandomSystem

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

/-- Attach through outside horizon `q`, using a resource horizon `n` covering `k q`. -/
noncomputable def attachCut (q n : ℕ) (hkn : k q ≤ n) :
    RandomSystem (Σ o, U o) (Σ o, V o)
      (cutDomain (fun h x => F (h.map Prod.fst ++ [x])) q) := by
  let aq := filterDom (fun xs => (outsideInputs xs).length ≤ q) α
  -- The outside cut's inside certificate widens to the chosen sufficient horizon.
  have small := ha.filterDom_of_insideQueriesBounded hk mono q
  have certified : IsDDCFrom (fun xs => E xs ∧ xs.length ≤ n)
      (fun xs => F xs ∧ xs.length ≤ q) b aq :=
    small.inside_mono (fun xs hx => ⟨hx.1, hx.2.trans hkn⟩)
  -- Both finite domains retain the original nonempty-prefix contracts.
  have inside : ¬ (E [] ∧ 0 ≤ n) ∧
      ∀ {s t}, s <+: t → s ≠ [] → (E t ∧ t.length ≤ n) → E s ∧ s.length ≤ n :=
    ⟨fun hx => hE.1 hx.1, fun hs hn hx => ⟨hE.2 hs hn hx.1, hs.length_le.trans hx.2⟩⟩
  have outside : ¬ (F [] ∧ 0 ≤ q) ∧
      ∀ {s t}, s <+: t → s ≠ [] → (F t ∧ t.length ≤ q) → F s ∧ s.length ≤ q :=
    ⟨fun hx => hF.1 hx.1, fun hs hn hx => ⟨hF.2 hs hn hx.1, hs.length_le.trans hx.2⟩⟩
  let R : RandomSystem (Σ j, X j) (Σ j, Y j)
      (Domain.ofInputs (fun xs => E xs ∧ xs.length ≤ n) n (fun _ hx => hx.2)) :=
    ⟨SystemAlgebra.cutMass p n, by
      rw [← Domain.cutDomain_ofInputs]
      exact IsRandomSystem.cutMass _ p hp n⟩
  have tags : R.RepliesAtQueriedInterface := by
    intro h x y hne
    change SystemAlgebra.cutMass p n (h ++ [(x, y)]) = 0
    unfold SystemAlgebra.cutMass
    split_ifs
    · exact ports h x y hne
    · rfl
  -- The existing bounded attachment supplies normalization on the output cut.
  let result : RandomSystem (Σ o, U o) (Σ o, V o)
      (Domain.ofInputs (fun xs => F xs ∧ xs.length ≤ q) q (fun _ hx => hx.2)) :=
    PDCBehavior.attach inside outside
    (PDCBehavior.ofDDC aq certified) R tags
  exact ⟨result, by rw [Domain.cutDomain_ofInputs]; exact result.2⟩

/-- Read each outside transcript from an attachment whose horizon is its own length. -/
noncomputable def attachMass : List ((Σ o, U o) × (Σ o, V o)) → ℝ :=
  RandomSystem.limitMass (fun h x => F (h.map Prod.fst ++ [x]))
    (fun q => attachCut (hE := hE) (hF := hF) (ha := ha) (hk := hk) (mono := mono)
      (hp := hp) (ports := ports) q (k q) le_rfl)

end SystemAlgebra.IsRandomSystem
