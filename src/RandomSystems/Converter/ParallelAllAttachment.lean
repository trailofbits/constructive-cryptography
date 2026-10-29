import RandomSystems.Converter.ParallelAll
import RandomSystems.System.ParallelWiring

/-!
# Componentwise attachment of parallel converters

Attaching a parallel family of deterministic converters `α k` to a parallel family of
deterministic resources `R k` is the parallel family of the attachments `α k • R k`; each
converter exchanges inside messages only with the resource of its own tag:

```text
  ⟨k,o⟩(u) ──▶ ┌──────┐ ──▶ ⟨k,j⟩(x) ──▶ ┌──────┐
  ⟨k,o⟩ ⇒ v ◀─ │ α k  │ ◀── ⟨k,j⟩ ⇒ y ◀─ │ R k  │      one pair of boxes per tag k
               └──────┘                  └──────┘
```

With `ρ` the regroupings `⟨⟨k, j⟩, x⟩ ↦ ⟨k, ⟨j, x⟩⟩` (`Equiv.sigmaAssoc`) of each alphabet:

  `apply (tensorAllRaw α) (relabel (parAll R) ρ ρ⁻¹)`
  `  = relabel (parAll (k ↦ apply (α k) (R k))) ρ ρ⁻¹`.

Proof: `apply` is `interconnect` of a `pair`; `pair_parAll` regroups the two families as a
family of pairs, and `parAll_interconnect_all` wires each pair separately. Its convergence
hypothesis comes from the bounded internal interaction of each DDC.

The raw law needs no finiteness of `K`. The canonical law compares trimmed behavior; it needs
`Finite K` for the bound `Finset.univ.sup b` of `tensorAllL α`, and resources replying at the
queried port for `trim_apply_canon`.

## Main results

* `apply_tensorAllRaw_parAll`: raw componentwise attachment
* `trim_apply_tensorAllL_parAll`: canonical componentwise attachment, on trimmed behavior

Sources: Jost, Thesis, printed p. 17 (finite disjoint-interface resources viewed as one);
Def. 2.2.2, printed pp. 17–18 (finite bound on consecutive inside queries).
-/

namespace SystemAlgebra


variable {K : Type} {O J : K → Type} {U V : ∀ k, O k → Type} {X Y : ∀ k, J k → Type}
  {α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)} {b : K → ℕ}

open Classical in
/-- **Raw componentwise attachment.** With `ρ_X`, `ρ_Y`, `ρ_U`, `ρ_V` the `Equiv.sigmaAssoc`
regroupings,

  `apply (tensorAllRaw α) (relabel (parAll R) ρ_X ρ_Y⁻¹)`
  `  = relabel (parAll (k ↦ apply (α k) (R k))) ρ_U ρ_V⁻¹`.

`K` need not be finite. Each `α k` has a finite bound `b k` on consecutive inside queries
(Jost, Thesis, Def. 2.2.2, printed pp. 17–18), so its wiring to `R k` converges on every
outside history (`IsDDC.converges_resource`). -/
lemma apply_tensorAllRaw_parAll (hα : ∀ k, IsDDC (b k) (α k))
    (R : ∀ k, InterfaceSystem (J k) (X k) (Y k)) :
    apply (tensorAllRaw α)
      (relabel (parAll R) (Equiv.sigmaAssoc fun k j => X k j)
        (Equiv.sigmaAssoc fun k j => Y k j).symm) =
      relabel (parAll fun k => apply (α k) (R k))
        (Equiv.sigmaAssoc fun k o => U k o)
        (Equiv.sigmaAssoc fun k o => V k o).symm := by
  -- Regroup the converter and resource families into corresponding pairs.
  simp only [apply_eq, tensorAllRaw, pair_relabel, pair_parAll, interconnect_relabel]
  -- Wire each pair `(α k, R k)` separately; every pair converges since `α k` is a DDC.
  rw [parAll_interconnect_all (fun k => (hα k).converges_resource (R k)),
    relabel_interconnect]
  congr 1
  -- The composite regroupings agree message by message: split on tag, side and port.
  · funext z
    rcases z with ⟨k, ⟨(_ | ⟨⟨⟩⟩), z⟩⟩
    · rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩ <;> rfl
    · rcases z with ⟨i, z⟩; rfl

open Classical in
/-- **Canonical componentwise attachment**, on trimmed behavior:

  `trim (apply (tensorAllL α) (relabel (trim (parAll R)) ρ_X ρ_Y⁻¹))`
  `  = relabel (trim (parAll (k ↦ trim (apply (α k) (R k))))) ρ_U ρ_V⁻¹`.

Only trimmed (reachable) behavior is compared; no raw off-tree representatives are
identified. `Finite K` gives the bound `Finset.univ.sup b` of `tensorAllL α`; replies at the
queried port let `trim_apply_canon` remove the canonicalization. -/
lemma trim_apply_tensorAllL_parAll [_root_.Finite K]
    (hα : ∀ k, IsDDC (b k) (α k))
    {R : ∀ k, InterfaceSystem (J k) (X k) (Y k)}
    (hR : ∀ k, RepliesAtQueriedInterface (R k)) :
    trim (apply (tensorAllL α)
      (relabel (trim (parAll R)) (Equiv.sigmaAssoc fun k j => X k j)
        (Equiv.sigmaAssoc fun k j => Y k j).symm)) =
      relabel (trim (parAll fun k => trim (apply (α k) (R k))))
        (Equiv.sigmaAssoc fun k o => U k o)
        (Equiv.sigmaAssoc fun k o => V k o).symm := by
  let _ := Fintype.ofFinite K
  -- Proof chain, `ρ` the regroupings and `R̂ = relabel (parAll R) ρ_X ρ_Y⁻¹`:
  --
  --   trim (apply (tensorAllL α) (relabel (trim (parAll R)) …))
  --     = trim (apply (tensorAllL α) R̂)                     trim (parAll R) ≈ₛ parAll R
  --     = trim (apply (tensorAllRaw α) R̂)                   trim_apply_canon
  --     = trim (relabel (parAll (k ↦ apply (α k) (R k))) …)  apply_tensorAllRaw_parAll
  --     = relabel (trim (parAll (k ↦ trim (apply …)))) …      trim_relabel, trim_parAll_trim
  --
  -- Step 1: attachment respects `≈ₛ` of the resource, and both sides are silent at `[]`.
  have he := (EqOnReachable.rfl' (tensorAllL α)).apply
    ((trim_behEq (parAll R)).relabel (Equiv.sigmaAssoc fun k j => X k j)
      (Equiv.sigmaAssoc fun k j => Y k j).symm)
  have ht := he.trim_eq (by simp only [SilentAtEmpty, apply_eq, interconnect_nil,
    Part.not_none_dom, not_false_eq_true])
    (by simp only [SilentAtEmpty, apply_eq, interconnect_nil, Part.not_none_dom, not_false_eq_true])
  -- Steps 2–4: drop `canon` (`tensorAllL α` is a DDC; `R̂` replies at the queried port by
  -- `RepliesAtQueriedInterface.parallelAll`), apply the raw law, then move `trim` inward.
  rw [ht, tensorAllL, trim_apply_canon (IsDDC.tensorAllL hα)
    (RepliesAtQueriedInterface.parallelAll hR), apply_tensorAllRaw_parAll hα,
    trim_relabel, trim_parAll_trim]

end SystemAlgebra
