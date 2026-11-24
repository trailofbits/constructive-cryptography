import Rendering.TypeNotation

/-! Exact type recognition, grouping, bounds and source identity for symbolic alphabets. -/

open Lean Meta Elab Command Term CCWidget

namespace Rendering.TypeNotationTests

elab "assert_type_notation " t:term " gives " expected:str : command =>
  runTermElabM fun _ => do
    let e ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let actual := (← typeNotation (← instantiateMVars e)).text
    unless actual == expected.getString do
      throwError "type notation differs: {actual}; expected {expected.getString}"

assert_type_notation Nat gives "ℕ"
assert_type_notation Int gives "ℤ"
assert_type_notation Bool gives "𝔹"
assert_type_notation Unit gives "{⋆}"
assert_type_notation Empty gives "∅"
assert_type_notation Fin 0 gives "∅"
assert_type_notation Fin 1 gives "{0}"
assert_type_notation Fin 2 gives "{0,1}"
assert_type_notation Fin 3 gives "{0,1,2}"
assert_type_notation Fin 16 gives "{0,…,15}"
assert_type_notation Bool → Bool gives "𝔹 → 𝔹"
assert_type_notation (Bool → Bool) → Bool gives "(𝔹 → 𝔹) → 𝔹"
assert_type_notation Bool → Bool → Bool gives "𝔹 → (𝔹 → 𝔹)"
assert_type_notation (Bool × Unit) × Fin 2 gives "(𝔹 × {⋆}) × {0,1}"
assert_type_notation Bool × (Unit × Fin 2) gives "𝔹 × ({⋆} × {0,1})"
assert_type_notation Sum Bool (Prod Unit (Fin 2)) gives "𝔹 ⊕ {⋆} × {0,1}"

/-- A named alphabet stays named, even if its definition is a familiar type. -/
abbrev NamedAlphabet := Bool

run_cmd runTermElabM fun _ => do
  for stx in #[← `(NamedAlphabet), ← `(Float), ← `(List Bool), ← `((n : Nat) → Fin n)] do
    let e ← elabTerm stx none
    let view ← typeNotation e
    unless view.text == (← ppExpr e).pretty (width := 100) do
      throwError "an unsupported or named type was reinterpreted"
    unless (← typeNotation e 0).text == (← ppExpr e).pretty (width := 100) do
      throwError "display depth limit truncated a type"
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let e := mkApp (mkConst ``Fin) n
    unless (← typeNotation e).text == (← ppExpr e).pretty (width := 100) do
      throwError "a symbolic bound was evaluated"

-- Numeral syntax alone is insufficient: the selected instance may denote a different number.
run_cmd runTermElabM fun _ => do
  let inst ← elabTerm (← `(show OfNat Nat 16 from ⟨17⟩)) none
  synthesizeSyntheticMVarsNoPostponing
  let inst ← instantiateMVars inst
  let misleading := mkApp3 (mkConst ``OfNat.ofNat [Level.zero])
    (mkConst ``Nat) (mkRawNatLit 16) inst
  unless (← finiteTypeLiteral? misleading).isNone do
    throwError "a noncanonical numeral instance was presented as its printed index"

-- Every nested symbol still carries its own exact Lean expression.
run_cmd runTermElabM fun _ => do
  let e ← elabTerm (← `(Bool × Fin 16)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let .binary source "×" _ (.atom left "𝔹" _) (.atom right "{0,…,15}" _) ← typeNotation e
    | throwError "missing source-linked product notation"
  unless source == e && left.consumeMData == Lean.mkConst ``Bool &&
      (← isDefEq right (mkApp (mkConst ``Fin) (mkNatLit 16))) do
    throwError "a symbol refers to a different Lean type"

end Rendering.TypeNotationTests
