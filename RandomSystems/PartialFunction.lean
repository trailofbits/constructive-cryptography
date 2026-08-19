/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.PFun

/-!
# Partial functions: bisimulation and the finite-unrolling limit

Two facts about partial functions that the converter layer rests on and that
carry no random-systems content of their own.

`PFun.fix_bisim` is least-fixed-point theory, stated in the `PFun` namespace so
it can be upstreamed to `Mathlib.Data.PFun` verbatim.

`eventual` is the fuel-free limit of a fuel-indexed family.  Matt, Maurer,
Portmann, Renner, Tackmann, *Toward an Algebraic Theory of Systems* (2018) §6
shows that for causal systems the connecting fixed point is unique and reached
by a **finite unrolling** (Theorem 6.2).  The unrolling counter is a
bookkeeping device with no paper counterpart, so the applications below expose
only the counter-independent value: defined exactly where some finite unrolling
succeeds, undefined exactly where the unrolling diverges.  CR18 Definition 3.8's
"finite upper bound on the number of consecutive outputs of the form `(in, x)`"
is the witness that such a counter exists, and stays a predicate on converters
rather than a parameter of the drivers.
-/

namespace PFun

/-- A bisimulation principle for `PFun.fix`: if a state relation `R` and an
output relation `Q` are preserved by single steps — `f`-stops map to `Q`-related
`g`-stops, `f`-steps map to `R`-related `g`-steps — then `R`-related states have
`Q`-related fixed-point results. -/
theorem fix_bisim {σ τ β β' : Type*} {f : σ →. β ⊕ σ} {g : τ →. β' ⊕ τ}
    {R : σ → τ → Prop} {Q : β → β' → Prop}
    (hstop : ∀ a a', R a a' → ∀ b, Sum.inl b ∈ f a →
        ∃ b', Sum.inl b' ∈ g a' ∧ Q b b')
    (hstep : ∀ a a', R a a' → ∀ a₁, Sum.inr a₁ ∈ f a →
        ∃ a₁', Sum.inr a₁' ∈ g a' ∧ R a₁ a₁')
    {a : σ} {b : β} (hb : b ∈ f.fix a) :
    ∀ a', R a a' → ∃ b', b' ∈ g.fix a' ∧ Q b b' := by
  refine PFun.fixInduction hb
    (C := fun a₀ => ∀ a', R a₀ a' → ∃ b', b' ∈ g.fix a' ∧ Q b b') ?_
  intro a₀ hb₀ IH a' hR
  rw [PFun.mem_fix_iff] at hb₀
  rcases hb₀ with hl | ⟨a₁, hr, _⟩
  · obtain ⟨b', hb', hQ⟩ := hstop a₀ a' hR b hl
    exact ⟨b', PFun.fix_stop hb', hQ⟩
  · obtain ⟨a₁', hr', hR₁⟩ := hstep a₀ a' hR a₁ hr
    obtain ⟨b', hb', hQ⟩ := IH a₁ hr a₁' hR₁
    exact ⟨b', by rw [PFun.fix_fwd_eq hr']; exact hb', hQ⟩

end PFun

namespace Part

/-- The counter-independent value of a fuel-indexed family: defined where some
fuel succeeds. -/
noncomputable def eventual {W : Type*} (g : ℕ → Part W) : Part W :=
  Part.assert (∃ fuel, (g fuel).Dom) fun h => g h.choose

/-- For a family monotone in the fuel, the eventual value is membership at
*some* fuel, so the counter never appears in the statement. -/
theorem mem_eventual {W : Type*} {g : ℕ → Part W}
    (hmono : ∀ {f f' : ℕ} {w : W}, f ≤ f' → w ∈ g f → w ∈ g f') {w : W} :
    w ∈ eventual g ↔ ∃ fuel, w ∈ g fuel := by
  rw [eventual, Part.mem_assert_iff]
  constructor
  · rintro ⟨_, hw⟩; exact ⟨_, hw⟩
  · rintro ⟨fuel, hfuel⟩
    have hdom : ∃ f, (g f).Dom := ⟨fuel, Part.dom_iff_mem.mpr ⟨w, hfuel⟩⟩
    refine ⟨hdom, ?_⟩
    have hv : (g hdom.choose).get hdom.choose_spec ∈ g hdom.choose := Part.get_mem _
    have h1 : w ∈ g (max hdom.choose fuel) := hmono (le_max_right _ _) hfuel
    have h2 : (g hdom.choose).get hdom.choose_spec ∈ g (max hdom.choose fuel) :=
      hmono (le_max_left _ _) hv
    rw [Part.mem_unique h1 h2]; exact hv

end Part
