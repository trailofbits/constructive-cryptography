import RandomSystems.Converter.ProgramAttachment
import ConstructiveCryptography.DSL.Probability
import Mathlib.Data.Fintype.Order

/-!
# Program bodies

The DSL compiles a procedure into a deterministic body: a function of the inside exchanges of
the current invocation, giving the next inside query or the reply. A return statement replies;
a call statement queries and continues with the reply; a loop folds its body over a list.
Every sampling statement has already become a call to a source. `CallBound` and `CallCost`
count the inside queries along the exchanges a body makes itself.

## Main definitions

* `returnProg`, `callProg`, `forEach`: the bodies of return, call and loop statements
* `lawType`, `sampleWitness`: the type of a law, and a value of it
* `TypeOf`: the type of the private bindings, from their initial values

## Main results

* `callBound_return`, `callBound_call`, `callBound_ite`, `callBound_foldr`,
  `callBound_uniform`: bounds of the statement forms
* `callCost_return`, `callCost_call`, `callCost_foldr`: costs of the statement forms
* `preservesAt_return`, `preservesAt_call_self`, `preservesAt_call_other`, `avoids_return`,
  `avoids_call`: port preservation of the statement forms
-/

namespace SystemAlgebra.DSL

open Classical Probability
open Program (CallBound CallCost ExchangesOf PreservesAt)

variable {J A : Type} {X Y : J → Type}

/-- The type of the samples of a law. -/
abbrev lawType {T : Type} (_ : Distribution.ProbDist T) : Type := T

/-- The type of a value: the private bindings of a component, from their initial values. -/
abbrev TypeOf {T : Type} (_ : T) : Type := T

/-- A total cost bound is closed under prefixes. -/
theorem cost_prefix_closed {T : Type} (f : T → ℕ) (q : ℕ) :
    ∀ p h : List T, p <+: h → (h.map f).sum ≤ q → (p.map f).sum ≤ q := by
  rintro p h ⟨e, rfl⟩ hh
  simp only [List.map_append, List.sum_append] at hh
  omega

/-- An exact domain intersected with a budget of `k` inputs is again silent before the first
input and closed under nonempty prefixes. -/
theorem budget_nonempty_prefix {A : Type} {P : List A → Prop} {k : ℕ}
    (hP : ¬ P [] ∧ ∀ {p h}, p <+: h → p ≠ [] → P h → P p) :
    ¬ (P [] ∧ ([] : List A).length ≤ k) ∧
      ∀ {p h : List A}, p <+: h → p ≠ [] → P h ∧ h.length ≤ k → P p ∧ p.length ≤ k :=
  ⟨fun h => hP.1 h.1, fun hp hne hd => ⟨hP.2 hp hne hd.1, hp.length_le.trans hd.2⟩⟩

/-- A value of the type of a law. -/
noncomputable def sampleWitness {T : Type} (P : Distribution.ProbDist T) : T :=
  Classical.choice P.nonempty

/-- A loop: fold its body over the list, then continue with the bindings. -/
abbrev forEach {T C R : Type} (xs : List T) (step : T → (C → R) → C → R) (finish : C → R)
    (c : C) : R :=
  xs.foldr step finish c

/-- The body of a return statement. -/
def returnProg (a : A) : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j) := fun _ => .inl a

/-- The body of a call statement: query `x` at `j`, and continue with the reply. -/
noncomputable def callProg (j : J) (x : X j)
    (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) :
    List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)
  | [] => .inr ⟨j, x⟩
  | (_, ⟨j', y⟩) :: h => if hj : j' = j then k (hj ▸ y) h else .inr ⟨j, x⟩

theorem callBound_return (b : ℕ) (a : A) :
    CallBound (X := X) (Y := Y) b (returnProg a) := by
  intro h q _ hq
  cases hq

theorem _root_.SystemAlgebra.Program.CallBound.mono {a b : ℕ} {f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)}
    (hf : CallBound a f) (hab : a ≤ b) : CallBound b f :=
  fun h q hc hq => (hf h q hc hq).trans_le hab

/-- The exchanges of a call statement: its query, answered at its label, then the exchanges of
its continuation. -/
theorem exchangesOf_callProg {j : J} {x : X j}
    {k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)}
    {z : (Σ j, X j) × (Σ j, Y j)} {h : List ((Σ j, X j) × (Σ j, Y j))}
    (hc : ExchangesOf (callProg j x k) (z :: h)) :
    ∃ y : Y j, z = (⟨j, x⟩, ⟨j, y⟩) ∧ callProg j x k (z :: h) = k y h ∧ ExchangesOf (k y) h := by
  obtain ⟨hq, hl⟩ := hc 0 (by simp)
  simp only [List.take_zero, callProg, List.getElem_cons_zero] at hq hl
  rcases z with ⟨q, ⟨j', y⟩⟩
  obtain rfl : ⟨j, x⟩ = q := Sum.inr.inj hq
  change j' = j at hl
  subst hl
  refine ⟨y, rfl, by simp [callProg], fun i hi => ?_⟩
  obtain ⟨hq', hl'⟩ := hc (i + 1) (by simpa using hi)
  simpa [callProg] using And.intro hq' hl'

theorem callBound_call {b : ℕ} (j : J) (x : X j)
    (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (hk : ∀ y, CallBound b (k y)) : CallBound (b + 1) (callProg j x k) := by
  intro h q hc hq
  rcases h with _ | ⟨z, h⟩
  · exact Nat.succ_pos _
  · obtain ⟨y, rfl, he, hc'⟩ := exchangesOf_callProg hc
    rw [he] at hq
    simpa using hk y h q hc' hq

/-- Either branch uses at most the larger of their bounds. -/
theorem callBound_ite (p : Prop) [Decidable p] {a b : ℕ}
    {f g : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)}
    (hf : CallBound a f) (hg : CallBound b g) :
    CallBound (max a b) (if p then f else g) := by
  split_ifs
  · exact hf.mono (le_max_left _ _)
  · exact hg.mono (le_max_right _ _)

/-- A loop costs its final continuation plus a fixed bound per element. -/
theorem callBound_foldr {T C : Type} (xs : List T)
    (step : T → (C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) →
      C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (finish : C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (a b : ℕ) (ha : ∀ c, CallBound a (finish c))
    (hb : ∀ x n k, (∀ c, CallBound n (k c)) → ∀ c, CallBound (n + b) (step x k c))
    (c : C) : CallBound (a + xs.length * b) (xs.foldr step finish c) := by
  induction xs generalizing c with
  | nil => simpa only [List.foldr_nil, List.length_nil, zero_mul, Nat.add_zero] using ha c
  | cons x xs ih =>
    simpa only [List.foldr_cons, List.length_cons, Nat.add_mul, one_mul, Nat.add_assoc] using
      hb x (a + xs.length * b) (xs.foldr step finish) ih c

/-- Finite inputs and private bindings turn per-invocation bounds into one uniform bound. -/
theorem callBound_uniform {S O : Type} {U V : O → Type}
    [_root_.Finite S] [_root_.Finite O] [∀ o, _root_.Finite (U o)]
    (body : Program S O J U V X Y) (hb : ∀ s o u, ∃ b, CallBound b (body s o u)) :
    ∃ b, body.Bounded b := by
  choose cost hcost using hb
  obtain ⟨b, hbound⟩ := _root_.Finite.exists_le
    (fun p : S × (Σ o, U o) => cost p.1 p.2.1 p.2.2)
  exact ⟨b, fun s o u => (hcost s o u).mono (hbound (s, ⟨o, u⟩))⟩

theorem _root_.SystemAlgebra.Program.CallCost.of_eq {m n : ℕ} {f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)}
    (e : m = n) (hf : CallCost m f) : CallCost n f := e ▸ hf

theorem callCost_return (a : A) : CallCost (X := X) (Y := Y) 0 (returnProg a) := by
  intro h hc
  refine ⟨fun q hq => by simp [returnProg] at hq, fun a' _ => ?_⟩
  rcases h with _ | ⟨z, h⟩
  · rfl
  · exact absurd (hc 0 (by simp)).1 (by simp [returnProg])

theorem callCost_call {n : ℕ} (j : J) (x : X j)
    (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (hk : ∀ y, CallCost n (k y)) : CallCost (n + 1) (callProg j x k) := by
  intro h hc
  rcases h with _ | ⟨z, h⟩
  · exact ⟨fun _ _ => Nat.succ_pos _, fun a ha => by simp [callProg] at ha⟩
  · obtain ⟨y, rfl, he, hc'⟩ := exchangesOf_callProg hc
    obtain ⟨h₁, h₂⟩ := hk y h hc'
    exact ⟨fun q hq => by rw [he] at hq; simpa using h₁ q hq,
      fun a ha => by rw [he] at ha; simpa using h₂ a ha⟩

/-- A loop spends a fixed cost per element on top of its final continuation. -/
theorem callCost_foldr {T C : Type} (xs : List T)
    (step : T → (C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) →
      C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (finish : C → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (a b : ℕ) (ha : ∀ c, CallCost a (finish c))
    (hb : ∀ x n k, (∀ c, CallCost n (k c)) → ∀ c, CallCost (n + b) (step x k c))
    (c : C) : CallCost (a + xs.length * b) (xs.foldr step finish c) := by
  induction xs generalizing c with
  | nil => simpa only [List.foldr_nil, List.length_nil, zero_mul, Nat.add_zero] using ha c
  | cons x xs ih =>
    simpa only [List.foldr_cons, List.length_cons, Nat.add_mul, one_mul, Nat.add_assoc] using
      hb x (a + xs.length * b) (xs.foldr step finish) ih c

section Preservation

variable {O : Type} (ι : O → Option J)

/-- A body that makes no query at the labels `ι o`. -/
def Avoids (f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)) : Prop :=
  ∀ h q, ExchangesOf f h → f h = .inr q → ∀ o, ι o ≠ some q.1

theorem avoids_return (a : A) : Avoids (X := X) (Y := Y) ι (returnProg a) := by
  intro h q _ hq
  cases hq

theorem avoids_call {j : J} (x : X j)
    (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (hk : ∀ y, Avoids ι (k y)) (hj : ∀ o, ι o ≠ some j) : Avoids ι (callProg j x k) := by
  intro h q hc hq
  rcases h with _ | ⟨z, h⟩
  · cases hq
    exact hj
  · obtain ⟨y, rfl, he, hc'⟩ := exchangesOf_callProg hc
    rw [he] at hq
    exact hk y h q hc' hq

theorem preservesAt_return (o : O) (a : A) :
    PreservesAt (X := X) (Y := Y) ι o (returnProg a) := by
  intro h q _ hq
  cases hq

/-- A call at a label `ι` names at most for `o`, after which the body makes no query at the labels
`ι o'`. -/
theorem preservesAt_call_self {o : O} {j : J} (x : X j)
    (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (hk : ∀ y, Avoids ι (k y)) (hι : ∀ o', ι o' = some j → o' = o) :
    PreservesAt ι o (callProg j x k) := by
  intro h q hc hq o' hq'
  rcases h with _ | ⟨z, h⟩
  · cases hq
    exact ⟨hι o' hq', fun e he => absurd he List.not_mem_nil⟩
  · obtain ⟨y, rfl, he, hc'⟩ := exchangesOf_callProg hc
    rw [he] at hq
    exact absurd hq' (hk y h q hc' hq o')

/-- A call at a label no `ι o'` names. -/
theorem preservesAt_call_other {o : O} {j : J} (x : X j)
    (k : Y j → List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j))
    (hk : ∀ y, PreservesAt ι o (k y)) (hj : ∀ o', ι o' ≠ some j) :
    PreservesAt ι o (callProg j x k) := by
  intro h q hc hq o' hq'
  rcases h with _ | ⟨z, h⟩
  · cases hq
    exact absurd hq' (hj o')
  · obtain ⟨y, rfl, he, hc'⟩ := exchangesOf_callProg hc
    rw [he] at hq
    obtain ⟨ho, hfree⟩ := hk y h q hc' hq o' hq'
    refine ⟨ho, fun e he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · intro hjq
      exact hj o' (hq'.trans (congrArg some hjq.symm))
    · exact hfree e he'

end Preservation

end SystemAlgebra.DSL
