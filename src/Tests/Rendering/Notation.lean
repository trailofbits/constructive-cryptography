import Rendering.Notation

/-! Compact predicates preserve scope, unknown syntax, and the difference between implication
and quantification over a type. These tests exercise expression recognition, not text matching. -/

open Lean Meta Elab Command Term CCWidget

namespace Rendering.NotationTests

elab "assert_domain_notation " t:term " gives " expected:str : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let actual ← domainNotation (← instantiateMVars e)
    unless actual == expected.getString do
      throwError "domain notation differs:\n{actual}\nexpected:\n{expected.getString}"

assert_domain_notation (fun h : List Nat => h ≠ [] ∧ h.length ≤ 3)
  gives "{ h | h ≠ ε ∧ |h| ≤ 3 }"
assert_domain_notation (fun h : List Nat => (h ≠ [] ∧ h.length ≤ 7) ∧ h.length ≤ 2)
  gives "{ h | (h ≠ ε ∧ |h| ≤ 7) ∧ |h| ≤ 2 }"
assert_domain_notation (fun h : List Nat => (h = [] ∨ h.length ≤ 3) ∧ h.length < 5)
  gives "{ h | (h = ε ∨ |h| ≤ 3) ∧ |h| < 5 }"
assert_domain_notation (fun h : List Nat => h = [] ∨ h.length ≤ 3 ∧ h.length < 5)
  gives "{ h | h = ε ∨ |h| ≤ 3 ∧ |h| < 5 }"
assert_domain_notation (fun h : List Nat => ¬(h = [] ∨ h.length ≤ 3))
  gives "{ h | ¬(h = ε ∨ |h| ≤ 3) }"
assert_domain_notation (fun h : List Nat => h ≠ [] → h.length ≤ 3)
  gives "{ h | h ≠ ε ⇒ |h| ≤ 3 }"
assert_domain_notation (fun h : List Nat => ∀ _i : Empty, h.length ≤ 3)
  gives "{ h | ∀ _i : Empty, |h| ≤ 3 }"
assert_domain_notation (fun h : List Nat => ∀ f : Nat → Nat, f h.length = 0)
  gives "{ h | ∀ f : (Nat → Nat), (f h.length) = 0 }"
assert_domain_notation (fun h : List Nat => (fun k => k ≠ [] ∧ k.length ≤ 7) h)
  gives "{ h | h ≠ ε ∧ |h| ≤ 7 }"

/-- A lookalike name is deliberately not list length. -/
def length (h : List Nat) : Nat := h.length + 1

run_cmd runTermElabM fun _ => do
  for stx in #[← `(length ([] : List Nat)), ← `(Nat → Bool),
      ← `((fun i : Bool => if i then Nat else Bool))] do
    let e ← elabTerm stx none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    unless (← predicateNotation e).text == (← ppExpr e).pretty (width := 100) do
      throwError "unsupported expression was reinterpreted"
    unless (← predicateNotation e 0).text == (← ppExpr e).pretty (width := 100) do
      throwError "display limit truncated the expression"

-- A history binder must not capture an existing budget named `h` in the display.
run_cmd runTermElabM fun _ => do
  withLocalDeclD `h (mkConst ``Nat) fun bound => do
    let listType ← mkAppM ``List #[mkConst ``Nat]
    withLocalDeclD `history listType fun history => do
      let size ← mkAppM ``List.length #[history]
      let condition ← mkAppM ``LE.le #[size, bound]
      let predicate ← mkLambdaFVars #[history] condition
      let actual ← domainNotation predicate
      unless actual == "{ h_1 | |h_1| ≤ h }" do
        throwError "display binder captured the budget: {actual}"

end Rendering.NotationTests
