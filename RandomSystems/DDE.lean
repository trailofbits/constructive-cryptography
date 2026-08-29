/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DDS
import Mathlib.Data.Nat.Find

/-!
# Deterministic discrete environments

Lanzenberger, Definition 2.11 (printed p. 14): a DDE “is a partial function”
“with prefix-closed domain.”  Definition 2.12 on the same page defines the
resulting transcript as “the sequence of pairs.”

Lean admits the empty answer history when the partial function supplies an
opening query. Undefinedness represents stopping.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u v

variable {X : Type u} {Y : Type v}

/-! ## Deterministic discrete environments -/

/-- Lanzenberger, Definition 2.11 (printed p. 14): the DDE has a
“prefix-closed domain.”  Full prefix closure permits the empty answer history. -/
def DDE.Valid (e : Raw Y X) : Prop :=
  ∀ ⦃l₁ l₂ : List Y⦄, l₁ <+: l₂ → l₂ ∈ e.Dom → l₁ ∈ e.Dom

/-- Lanzenberger, Definition 2.11 (printed p. 14): a DDE “is a partial
function.”  Lean records prefix closure in the subtype predicate. -/
abbrev DDE (Y : Type v) (X : Type u) : Type (max u v) :=
  { e : Raw Y X // DDE.Valid e }

namespace DDE

/-- An environment that is defined anywhere is defined at the empty history. -/
theorem nil_mem_dom (e : DDE Y X) {l : List Y} (hl : l ∈ e.1.Dom) :
    [] ∈ e.1.Dom :=
  e.2 List.nil_prefix hl

/-- A deterministic environment halts when one round bound excludes every
longer answer history. This auxiliary condition extends the literal finite
system model to unbounded carriers. -/
def Halts (e : DDE Y X) : Prop :=
  ∃ N : ℕ, ∀ l : List Y, N ≤ l.length → l ∉ e.1.Dom

end DDE

/-! ## Transcripts -/

/-- Lanzenberger, Definition 2.12 (printed p. 14): “The transcript ... is the
sequence of pairs.” -/
abbrev Transcript (X : Type u) (Y : Type v) : Type (max u v) :=
  List (X × Y)

/-- Lanzenberger, Definition 2.12 (printed p. 14): “`xᵢ = e(y₁, ..., yᵢ₋₁)` and
`yᵢ = s(x₁, ..., xᵢ)`.”  The two partial functions therefore receive their
complete respective histories; undefinedness leaves the transcript unchanged. -/
def trExtend (e : DDE Y X) (s : DDS X Y) (t : Transcript X Y) : Transcript X Y :=
  if hx : (t.map Prod.snd) ∈ e.1.Dom then
    let x := (e.1 (t.map Prod.snd)).get hx
    if hy : (t.map Prod.fst ++ [x]) ∈ dom s then
      t ++ [(x, output s (t.map Prod.fst ++ [x]) hy)]
    else t
  else t

/-- The first `n` stages of Definition 2.12's “sequence of pairs” (printed
p. 14). -/
def trN (e : DDE Y X) (s : DDS X Y) : ℕ → Transcript X Y
  | 0 => []
  | n + 1 => trExtend e s (trN e s n)

/-- A transcript's input history is empty or belongs to the system domain. -/
theorem trN_map_fst_mem_dom_or_nil (e : DDE Y X) (s : DDS X Y) (n : ℕ) :
    trN e s n = [] ∨ (trN e s n).map Prod.fst ∈ dom s := by
  -- Inductively, the empty transcript has no query history.
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      show trExtend e s (trN e s n) = [] ∨
        (trExtend e s (trN e s n)).map Prod.fst ∈ dom s
      by_cases hx : (trN e s n).map Prod.snd ∈ e.1.Dom
      · by_cases hy : (trN e s n).map Prod.fst ++
            [(e.1 ((trN e s n).map Prod.snd)).get hx] ∈ dom s
        -- A successful extension records exactly the newly admitted query.
        · rw [trExtend, dif_pos hx, dif_pos hy]
          right
          simpa using hy
        -- If the system is undefined, the preceding invariant persists.
        · rw [trExtend, dif_pos hx, dif_neg hy]
          exact ih
      -- If the environment stops, the preceding invariant persists.
      · rw [trExtend, dif_neg hx]
        exact ih

/-- Once a transcript stalls, it remains equal to the stalled stage. -/
theorem trN_eq_of_le {e : DDE Y X} {s : DDS X Y} {n : ℕ}
    (h : trN e s (n + 1) = trN e s n) :
    ∀ m, n ≤ m → trN e s m = trN e s n := by
  intro m hm
  -- Each later stage applies the same transcript function to the fixed value.
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => show trExtend e s (trN e s m) = _; rw [ih]; exact h

/-- Lanzenberger, Definition 2.12 (printed p. 14): “If `e(y₁, ..., yᵢ₋₁)` is
undefined (the environment stops), the transcript ends.”  Stabilization is the
Lean formulation of that undefinedness. -/
def Stops (e : DDE Y X) (s : DDS X Y) : Prop :=
  ∃ n, trN e s (n + 1) = trN e s n

/-- Lanzenberger, Definition 2.12 (printed p. 14): “The transcript ... is the
sequence of pairs.”  Lean exposes it as a partial value, defined exactly when
the sequence stabilizes. -/
def tr (e : DDE Y X) (s : DDS X Y) : Part (Transcript X Y) :=
  ⟨Stops e s, fun h => trN e s (Nat.find h)⟩

/-- Lanzenberger, Definition 2.12 (printed p. 14): the transcript is “denoted by
`tr(s, e)`.” -/
scoped notation "tr(" s ", " e ")" => tr e s

/-- The transcript's value is its stage at stabilization. -/
theorem tr_get (e : DDE Y X) (s : DDS X Y) (h : Stops e s) :
    (tr e s).get h = trN e s (Nat.find h) :=
  rfl

/-- Lanzenberger, Definition 2.12 (printed p. 14): “the environment must not
query `s` outside of the system's domain.” -/
def Compatible (e : DDE Y X) (s : DDS X Y) : Prop :=
  ∀ n x, x ∈ e.1 ((trN e s n).map Prod.snd) →
    (trN e s n).map Prod.fst ++ [x] ∈ dom s

/-- Compatibility with a named domain: the environment is compatible with
every deterministic system having that domain. -/
def CompatibleD (e : DDE Y X) (D : Set (List X)) : Prop :=
  ∀ s : DDS X Y, dom s = D → Compatible e s

/-- For a compatible pair, a transcript stalls exactly when the environment
is undefined on the answer history at that stage. -/
theorem trN_succ_eq_iff_of_compatible {e : DDE Y X} {s : DDS X Y}
    (h : Compatible e s) (n : ℕ) :
    trN e s (n + 1) = trN e s n ↔ (trN e s n).map Prod.snd ∉ e.1.Dom := by
  constructor
  -- Compatibility rules out a system-side failure after an environment query.
  · intro hst hdom
    have hx : (e.1 ((trN e s n).map Prod.snd)).get hdom ∈
        e.1 ((trN e s n).map Prod.snd) := Part.get_mem hdom
    have hy := h n _ hx
    -- Hence a defined query appends one pair and cannot be a fixed point.
    have : trN e s (n + 1) = trN e s n ++
        [((e.1 ((trN e s n).map Prod.snd)).get hdom,
          output s _ hy)] := by
      show trExtend e s (trN e s n) = _
      rw [trExtend, dif_pos hdom, dif_pos hy]
    rw [this] at hst
    simpa using congrArg List.length hst
  · intro hnd
    -- Environment undefinedness leaves the transcript fixed.
    show trExtend e s (trN e s n) = trN e s n
    rw [trExtend, dif_neg hnd]

/-- The stopped transcript, read at any stage at which the interaction has
already stabilized. -/
theorem tr_get_eq_trN {e : DDE Y X} {s : DDS X Y} (h : Stops e s) {N : ℕ}
    (hN : trN e s (N + 1) = trN e s N) : (tr e s).get h = trN e s N := by
  classical
  rw [tr_get]
  -- Both stages lie beyond the first stabilization point.
  exact (trN_eq_of_le (Nat.find_spec h) N (Nat.find_le hN)).symm

/-- One transcript round either leaves the transcript unchanged or appends one
query-answer pair. -/
theorem trExtend_eq_or_append (e : DDE Y X) (s : DDS X Y) (t : Transcript X Y) :
    trExtend e s t = t ∨ ∃ p, trExtend e s t = t ++ [p] := by
  rw [trExtend]
  by_cases hx : (t.map Prod.snd) ∈ e.1.Dom
  · rw [dif_pos hx]
    by_cases hy : (t.map Prod.fst ++ [(e.1 (t.map Prod.snd)).get hx]) ∈ dom s
    -- When both sides are defined, one query-answer pair is appended.
    · exact Or.inr ⟨_, dif_pos hy⟩
    -- System undefinedness leaves the transcript fixed.
    · exact Or.inl (dif_neg hy)
  -- Environment undefinedness leaves the transcript fixed.
  · exact Or.inl (dif_neg hx)

theorem trN_length_le (e : DDE Y X) (s : DDS X Y) (n : ℕ) :
    (trN e s n).length ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      -- A stage either preserves length or increases it by exactly one.
      show (trExtend e s (trN e s n)).length ≤ n + 1
      rcases trExtend_eq_or_append e s (trN e s n) with h | ⟨p, h⟩ <;> rw [h]
      · exact Nat.le_succ_of_le ih
      · simpa using Nat.succ_le_succ ih

/-- A transcript shorter than its stage bound has already stabilized. -/
theorem trN_succ_eq_of_length_lt (e : DDE Y X) (s : DDS X Y) :
    ∀ {n : ℕ}, (trN e s n).length < n → trN e s (n + 1) = trN e s n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by simp)
  | succ n ih =>
      intro h
      rcases trExtend_eq_or_append e s (trN e s n) with hstep | ⟨p, hstep⟩
      -- A fixed stage remains fixed at the next stage.
      · have hfix : trN e s (n + 1) = trN e s n := hstep
        show trExtend e s (trN e s (n + 1)) = trN e s (n + 1)
        rw [hfix]
        exact hstep
      -- An appended pair would force the prior transcript to be short too.
      · exfalso
        have hlen : (trN e s (n + 1)).length = (trN e s n).length + 1 := by
          show (trExtend e s (trN e s n)).length = _
          rw [hstep]
          simp
        have hlt : (trN e s n).length < n := by omega
        have := ih hlt
        rw [show trN e s (n + 1) = trExtend e s (trN e s n) from rfl, hstep] at this
        simpa using congrArg List.length this

theorem trN_succ_of_stop {e : DDE Y X} {s : DDS X Y} {n : ℕ}
    (h : ((trN e s n).map Prod.snd) ∉ e.1.Dom) : trN e s (n + 1) = trN e s n := by
  show trExtend e s (trN e s n) = trN e s n
  rw [trExtend, dif_neg h]

theorem trN_succ_of_query {e : DDE Y X} {s : DDS X Y} {n : ℕ}
    (hdom : ((trN e s n).map Prod.snd) ∈ e.1.Dom)
    (hy : (trN e s n).map Prod.fst ++
      [(e.1 ((trN e s n).map Prod.snd)).get hdom] ∈ dom s) :
    trN e s (n + 1) = trN e s n ++
      [((e.1 ((trN e s n).map Prod.snd)).get hdom,
        output s ((trN e s n).map Prod.fst ++
          [(e.1 ((trN e s n).map Prod.snd)).get hdom]) hy)] := by
  show trExtend e s (trN e s n) = _
  rw [trExtend, dif_pos hdom, dif_pos hy]

/-- A halting environment's interaction has stabilized by its own round
bound. -/
theorem trN_succ_eq_of_halts_bound {e : DDE Y X} {N : ℕ}
    (hN : ∀ l : List Y, N ≤ l.length → l ∉ e.1.Dom) (s : DDS X Y) :
    trN e s (N + 1) = trN e s N := by
  rcases Nat.lt_or_ge (trN e s N).length N with hlt | hge
  -- A short transcript has already stabilized.
  · exact trN_succ_eq_of_length_lt e s hlt
  -- Otherwise the environment's bound excludes its current answer history.
  · exact trN_succ_of_stop (hN _ (by simpa using hge))

/-- A halting environment stops against every deterministic system. -/
theorem stops_of_halts {e : DDE Y X} (h : DDE.Halts e) (s : DDS X Y) :
    Stops e s := by
  obtain ⟨N, hN⟩ := h
  -- The environment's finite bound supplies a stabilization witness.
  exact ⟨N, trN_succ_eq_of_halts_bound hN s⟩

end

end System

end RandomSystems
