import RandomSystems.PDS.PDS

/-!
# Sampled functions

A function answers each query on an input domain with its value at the latest
query. Sampling the function once and retaining it gives a PDS.

## Main definitions

* `DDS.ofFunction E hE f`: the deterministic evaluator of `f` on the input domain `E`
* `PDS.ofFunction E hE bound hb f P`: sample `f k` with `k ∼ P`, then evaluate
* `PDS.uniformFunction`: the uniformly sampled function table

## Main results

* `DDS.replies_ofFunction_iff`: the transcripts of an evaluator are its pointwise
  replies
-/

namespace SystemAlgebra

open Classical

namespace DDS

/-- Evaluate one fixed function on the most recent admitted input. -/
noncomputable def ofFunction {X Y : Type} (D : List X → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (f : X → Y) : DDS X Y :=
  ⟨fun h => if D h then ((h.getLast?).map f : Part Y) else Part.none, by
    constructor
    · simp [SilentAtEmpty, hD.1]
    · intro p h hp hn hd
      have hh : D h := by
        by_contra hh
        simp [hh] at hd
      simp [hD.2 hp hn hh, hn]⟩

theorem ofFunction_dom {X Y : Type} (D : List X → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (f : X → Y) (h : List X) : ((ofFunction D hD f).1 h).Dom ↔ D h := by
  by_cases hd : D h
  · have hn : h ≠ [] := fun he => hD.1 (he ▸ hd)
    simp [ofFunction, hd, hn]
  · simp [ofFunction, hd]

theorem ofFunction_snoc {X Y : Type} (D : List X → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (f : X → Y) (xs : List X) (x : X) :
    (ofFunction D hD f).1 (xs ++ [x]) =
      if D (xs ++ [x]) then Part.some (f x) else Part.none := by
  simp [ofFunction]

/-- A fixed function's transcript consists precisely of its pointwise replies. -/
theorem replies_ofFunction_iff {X Y : Type} (D : List X → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (f : X → Y) (xs : List X) (ys : List Y) :
    Replies (ofFunction D hD f).1 xs ys ↔
      (xs = [] ∨ D xs) ∧ ys = xs.map f := by
  induction xs using List.reverseRecOn generalizing ys with
  | nil =>
    constructor
    · intro h
      exact ⟨Or.inl rfl, List.length_eq_zero_iff.mp h.length⟩
    · rintro ⟨_, rfl⟩
      exact replies_nil _
  | append_singleton xs x ih =>
    constructor
    · intro h
      have hn : ys ≠ [] := by intro he; have := h.length; simp [he] at this
      obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hn
      rw [List.concat_eq_append] at h ⊢
      obtain ⟨hp, he⟩ := replies_snoc.mp h
      have hd := (ofFunction_dom D hD f _).mp
        ((replies_snoc.mpr ⟨hp, he⟩).dom (by simp))
      rw [ofFunction_snoc, if_pos hd] at he
      have hy : f x = y := Part.some_injective he
      exact ⟨Or.inr hd, by simp [(ih ys).mp hp |>.2, hy]⟩
    · rintro ⟨hd, rfl⟩
      have hd' : D (xs ++ [x]) := hd.resolve_left (by simp)
      rw [List.map_append, List.map_singleton]
      apply replies_snoc.mpr
      refine ⟨(ih _).mpr ⟨?_, rfl⟩, ?_⟩
      · by_cases hn : xs = []
        · exact Or.inl hn
        · exact Or.inr (hD.2 (List.prefix_append xs [x]) hn hd')
      · rw [ofFunction_snoc, if_pos hd']

end DDS

namespace PDS

open Probability

variable {K X Y : Type} [Fintype X] [Fintype Y]

/-- Sample a function once and answer every query on the input domain `E` with its
value. The result is the finite distribution of the deterministic evaluators. -/
noncomputable def ofFunction (E : List X → Prop)
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) (bound : ℕ)
    (hb : ∀ h, E h → h.length ≤ bound) (f : K → X → Y) (P : Distribution K) :
    PDS X Y (Domain.ofInputs E bound hb) :=
  Distribution.fTransform (fun k => ⟨(DDS.ofFunction E hE (f k)).1, (DDS.ofFunction E hE (f k)).2,
    HasDomain.ofInputs (DDS.ofFunction_dom E hE (f k))⟩) P

/-- The uniformly sampled function table, as a PDS on the input domain `E`. -/
noncomputable def uniformFunction [DecidableEq X] [Nonempty Y] (E : List X → Prop)
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) (bound : ℕ)
    (hb : ∀ h, E h → h.length ≤ bound) : PDS X Y (Domain.ofInputs E bound hb) :=
  ofFunction E hE bound hb id (Distribution.uniform (X → Y))

instance (E : List X → Prop) (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (bound : ℕ) (hb : ∀ h, E h → h.length ≤ bound) (f : K → X → Y) (P : Distribution K)
    [Distribution.IsProbability P] : Distribution.IsProbability (ofFunction E hE bound hb f P) :=
  inferInstanceAs (Distribution.IsProbability (Distribution.fTransform _ P))

instance [DecidableEq X] [Nonempty Y] (E : List X → Prop)
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) (bound : ℕ)
    (hb : ∀ h, E h → h.length ≤ bound) :
    Distribution.IsProbability (uniformFunction (Y := Y) E hE bound hb) :=
  inferInstanceAs (Distribution.IsProbability (ofFunction E hE bound hb id (Distribution.uniform (X → Y))))

end PDS
end SystemAlgebra
