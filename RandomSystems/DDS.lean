/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.PFun

/-!
# Deterministic discrete systems

Lanzenberger, Definition 2.9 (printed p. 13): a DDS “is a partial function”
“with prefix-closed domain.”

The Lean carrier uses nonempty finite input histories and represents memory by
dependence on the complete history; it introduces no separate state object.
-/

namespace RandomSystems

universe u v

/-- A predicate on input histories is prefix-closed when it holds for every
prefix of any history for which it holds. -/
abbrev PrefixClosed {X : Type u} (P : List X → Prop) : Prop :=
  ∀ ⦃l₁ l₂⦄, l₁ <+: l₂ → P l₂ → P l₁

/-- A history predicate is `q`-extensible when every admitted history shorter
than `q` has an admitted one-query extension. -/
def QExtensible {X : Type u} (P : List X → Prop) (q : ℕ) : Prop :=
  ∀ l, P l → l.length < q → ∃ x, P (l ++ [x])

/-- A history predicate is `q`-bounded when every admitted history has length
at most `q`. -/
def QBounded {X : Type u} (P : List X → Prop) (q : ℕ) : Prop :=
  ∀ l, P l → l.length ≤ q

/-- The length-bounded history predicate is prefix-closed. -/
theorem prefixClosed_length_le {X : Type u} (q : ℕ) :
    PrefixClosed (fun l : List X => l.length ≤ q) :=
  fun _ _ hpre hlen => le_trans hpre.length_le hlen

/-- The query-avoiding history predicate is prefix-closed. -/
theorem prefixClosed_forall_not_mem {X : Type u} (Q : Set X) :
    PrefixClosed (fun l : List X => ∀ q ∈ l, q ∉ Q) :=
  fun _ _ hpre h q hq => h q (hpre.subset hq)

namespace System

noncomputable section

open Classical

/-- The raw partial function underlying a deterministic discrete system. -/
abbrev Raw (X : Type u) (Y : Type v) : Type (max u v) :=
  List X →. Y

/-- Lanzenberger, Definition 2.9 (printed p. 13): “whose domain is
prefix-closed.”  Since `Raw` is defined on all lists, Lean separately excludes
the empty history to represent the source's `X⁺`. -/
def Valid {X : Type u} {Y : Type v} (S : Raw X Y) : Prop :=
  [] ∉ S.Dom ∧
    ∀ {l₁ l₂ : List X},
      l₁ <+: l₂ → l₁ ≠ [] → l₂ ∈ S.Dom → l₁ ∈ S.Dom

/-- Lanzenberger, Definition 2.9 (printed p. 13): a DDS “is a partial function”
from nonempty input histories to outputs. -/
abbrev DDS (X : Type u) (Y : Type v) : Type (max u v) :=
  { S : Raw X Y // Valid S }

variable {X : Type u} {Y : Type v}

/-- The partial function underlying a deterministic discrete system. -/
def toPFun (S : DDS X Y) : Raw X Y :=
  S.1

/-- Allow a DDS to be used where its underlying partial function is expected.
This coercion is notation only; the DDS retains its validity proof. -/
instance : Coe (DDS X Y) (Raw X Y) where
  coe := toPFun

/-- The domain of a deterministic discrete system. -/
def dom (S : DDS X Y) : Set (List X) :=
  S.1.Dom

@[simp]
theorem dom_def (S : DDS X Y) : dom S = S.1.Dom :=
  rfl

/-- The output on an input history in the system's domain. -/
def output (S : DDS X Y) (l : List X) (h : l ∈ dom S) : Y :=
  S.1.fn l h

/-- Output depends on the history, not on its domain-membership proof. -/
theorem output_congr (S : DDS X Y) {l₁ l₂ : List X} (hl : l₁ = l₂)
    (h₁ : l₁ ∈ dom S) (h₂ : l₂ ∈ dom S) :
    output S l₁ h₁ = output S l₂ h₂ := by
  subst hl
  rfl

/-- The validity proof carried by a deterministic discrete system. -/
theorem valid (S : DDS X Y) : Valid S.1 :=
  S.2

theorem empty_not_mem (S : DDS X Y) : [] ∉ dom S :=
  (valid S).1

theorem prefix_closed (S : DDS X Y) {l₁ l₂ : List X}
    (hprefix : l₁ <+: l₂) (hne : l₁ ≠ []) (hdom : l₂ ∈ dom S) :
    l₁ ∈ dom S :=
  (valid S).2 hprefix hne hdom

/-! ## Systems defined by ordinary functions -/

/-- A stateless function as a system: every nonempty history is admitted and
the answer is the function value on the latest query. -/
def functionEvaluator (f : X → Y) : DDS X Y :=
  ⟨(fun l : List X =>
      (⟨l ≠ [], fun h => f (l.getLast h)⟩ : Part Y)),
    ⟨by simp, by
      intro _ _ _ hne _
      exact hne⟩⟩

@[simp]
theorem dom_functionEvaluator (f : X → Y) :
    dom (functionEvaluator f) = {l : List X | l ≠ []} := by
  ext l
  rfl

@[simp]
theorem output_functionEvaluator (f : X → Y) (l : List X)
    (h : l ∈ dom (functionEvaluator f)) :
    output (functionEvaluator f) l h = f (l.getLast h) :=
  rfl

/-- The ordinary function is recovered from singleton histories. -/
theorem functionEvaluator_injective :
    Function.Injective (functionEvaluator : (X → Y) → DDS X Y) := by
  intro left right equal
  funext query
  have leftMember : left query ∈ (functionEvaluator left).1 [query] := by
    refine ⟨List.cons_ne_nil query [], ?_⟩
    simp [functionEvaluator]
  have rightMember : right query ∈ (functionEvaluator right).1 [query] := by
    refine ⟨List.cons_ne_nil query [], ?_⟩
    simp [functionEvaluator]
  rw [equal] at leftMember
  exact Part.mem_unique leftMember rightMember

@[simp]
theorem functionEvaluator_output (f : X → Y) (l : List X) (x : X)
    (h : l ++ [x] ∈ dom (functionEvaluator f)) :
    output (functionEvaluator f) (l ++ [x]) h = f x := by
  rw [output_functionEvaluator]
  exact congrArg f (List.getLast_concat (l := l))

/-- A system defined directly as a function of every nonempty input history. -/
def historyEvaluator (g : (l : List X) → l ≠ [] → Y) : DDS X Y :=
  ⟨(fun l : List X =>
      (⟨l ≠ [], fun h => g l h⟩ : Part Y)),
    ⟨by simp, by
      intro _ _ _ hne _
      exact hne⟩⟩

@[simp]
theorem dom_historyEvaluator (g : (l : List X) → l ≠ [] → Y) :
    dom (historyEvaluator g) = {l : List X | l ≠ []} := by
  ext l
  rfl

@[simp]
theorem historyEvaluator_output (g : (l : List X) → l ≠ [] → Y)
    (l : List X) (h : l ∈ dom (historyEvaluator g)) :
    output (historyEvaluator g) l h = g l h :=
  rfl

/-- Every system defined on all nonempty histories is its own history
function. -/
theorem eq_historyEvaluator_of_total (S : DDS X Y)
    (total : ∀ l : List X, l ≠ [] → l ∈ dom S) :
    S = historyEvaluator (fun l nonempty => output S l (total l nonempty)) := by
  apply Subtype.ext
  funext l
  apply Part.ext'
  · change (l ∈ dom S) ↔ l ≠ []
    constructor
    · intro member equalNil
      subst l
      exact S.property.1 member
    · exact total l
  · intro leftDomain rightDomain
    change output S l leftDomain = output S l (total l rightDomain)
    rfl

@[simp]
theorem historyEvaluator_getLast_eq_functionEvaluator (f : X → Y) :
    historyEvaluator (fun l hne => f (l.getLast hne)) = functionEvaluator f :=
  rfl

end

end System

end RandomSystems
