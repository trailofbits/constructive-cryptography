module

public import Probability.List

/-!
# Expanding entries with a running allowance

A marker expands to zero, one, or two unit increments. The target predicate checks the
accumulated total before every increment. An empty block preserves that total; starting
too close to the allowance prevents the two-increment block from being admitted.
-/

@[expose] public section

namespace Tests.ForallScanFlatMap

/-- `none` adds nothing, `some false` adds one unit, and `some true` adds two units. -/
def increments : Option Bool → List Nat
  | none => []
  | some false => [1]
  | some true => [1, 1]

/-- Expanding two, zero, and one increments preserves every running-total check. -/
theorem expanded_scan :
    List.ForallScan (fun total n => total + n) (fun total n => total + n ≤ 5) 1 [1, 1, 1] := by
  let advance : Nat → Option Bool → Nat := fun total marker => total + (increments marker).length
  let admitted : Nat → Option Bool → Prop := fun total marker => advance total marker ≤ 5
  have update : ∀ total marker,
      (increments marker).foldl (fun total n => total + n) total = advance total marker := by
    intro total marker
    cases marker with
    | none => rfl
    | some bit =>
      cases bit <;>
        simp only [increments, advance, List.foldl_cons, List.foldl_nil,
          List.length_cons, List.length_nil]
  have block : ∀ total marker, admitted total marker →
      List.ForallScan (fun total n => total + n) (fun total n => total + n ≤ 5)
        total (increments marker) := by
    intro total marker legal
    cases marker with
    | none => trivial
    | some bit =>
      cases bit with
      | false => exact ⟨legal, trivial⟩
      | true =>
        change total + 2 ≤ 5 at legal
        refine ⟨?_, ?_, trivial⟩ <;> omega
  have scan : List.ForallScan advance admitted 1 [some true, none, some false] := by
    change 3 ≤ 5 ∧ 3 ≤ 5 ∧ 4 ≤ 5 ∧ True
    exact ⟨by omega, by omega, by omega, trivial⟩
  exact scan.flatMap increments update block

/-- Checking only the first increment would miss the second one's exhausted allowance. -/
theorem exhausted_allowance :
    ¬ List.ForallScan (fun total n => total + n) (fun total n => total + n ≤ 5) 4
      (increments (some true)) := by
  intro scan
  change 5 ≤ 5 ∧ 6 ≤ 5 ∧ True at scan
  omega

#print axioms List.ForallScan.flatMap
#print axioms expanded_scan
#print axioms exhausted_allowance

end Tests.ForallScanFlatMap
