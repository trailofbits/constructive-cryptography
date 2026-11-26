module

public import RandomSystems.Typed.DSL.Collect

/-!
# Canonical collection traces

A two-port schedule receives a Boolean at its first port and a natural number at its second.
The forward certificate checks this dependent reply tuple. The empty schedule has no exchanges
and returns its selected result immediately.
-/

@[expose] public section

namespace Tests.CollectCallsTrace

open SystemAlgebra SystemAlgebra.DSL

/-- Port `false` returns a Boolean; port `true` returns a natural number. -/
def Reply : Bool → Type
  | false => Bool
  | true => Nat

/-- Ask the Boolean port, then the natural-number port; both inputs are unit. -/
def request : Fin 2 → Σ _ : Bool, Unit :=
  Fin.cases ⟨false, ()⟩ (fun _ => ⟨true, ()⟩)

/-- The two replies are `true` and `7`, each in its requested port's type. -/
def answers : (i : Fin 2) → Reply (request i).1 :=
  Fin.cases true (fun _ => (7 : Nat))

/-- Return the ordered Boolean/natural pair. -/
def finish (ys : (i : Fin 2) → Reply (request i).1) : Bool × Nat :=
  (ys 0, ys 1)

/-- The scheduled dependent replies give this concrete ordered trace. -/
lemma recorded_trace :
    (List.ofFn fun i => (request i, (⟨(request i).1, answers i⟩ : Σ port, Reply port))) =
      [(⟨false, ()⟩, ⟨false, true⟩), (⟨true, ()⟩, ⟨true, (7 : Nat)⟩)] := rfl

/-- The concrete heterogeneous trace follows collection's own query order. -/
theorem dependent_exchanges : Program.ExchangesOf
    (collectCalls (Y := Reply) 2 request finish)
    [(⟨false, ()⟩, ⟨false, true⟩), (⟨true, ()⟩, ⟨true, (7 : Nat)⟩)] := by
  rw [← recorded_trace]
  exact collectCalls_exchangesOf (Y := Reply) 2 request finish answers

/-- The same trace returns the selected pair. -/
example : collectCalls (Y := Reply) 2 request finish
    [(⟨false, ()⟩, ⟨false, true⟩), (⟨true, ()⟩, ⟨true, (7 : Nat)⟩)] = .inl (true, 7) := by
  rw [← recorded_trace]
  exact collectCalls_reply (Y := Reply) 2 request finish answers

/-- A zero-call schedule certifies the empty trace. -/
theorem empty_exchanges : Program.ExchangesOf
    (collectCalls (X := fun _ : Bool => Unit) (Y := Reply)
      0 (fun i => Fin.elim0 i) (fun _ => (17 : Nat))) [] := by
  simpa only [List.ofFn_zero] using
    collectCalls_exchangesOf (X := fun _ : Bool => Unit) (Y := Reply)
      0 (fun i => Fin.elim0 i) (fun _ => (17 : Nat)) (fun i => Fin.elim0 i)

/-- Empty collection returns 17 without an inside exchange. -/
example : collectCalls (X := fun _ : Bool => Unit) (Y := Reply)
    0 (fun i => Fin.elim0 i) (fun _ => (17 : Nat)) [] = .inl 17 := rfl

#print axioms collectCalls_exchangesOf
#print axioms dependent_exchanges
#print axioms empty_exchanges

end Tests.CollectCallsTrace
