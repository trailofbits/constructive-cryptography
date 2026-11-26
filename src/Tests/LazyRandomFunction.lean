module

public import Commons.Definitions.Ideal

/-!
# Lazy random-function checks

Concrete Boolean tables check hits, fresh inputs and repeated replies. The two-port table
checks independence between heterogeneous reply types. Attachment preserves the equality
between lazy and retained presentations at that interface.
-/

@[expose] public section

namespace LazyRandomFunctionTests

open Commons SystemAlgebra Probability Probability.Distribution
open scoped SystemAlgebra

/-- A Boolean-input, Boolean-reply port admitting at most two queries. -/
abbrev bitInput : Interface := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 2

-- The ports return `Bool` and `Bool × Bool`, with one shared total query allowance.
interface IndependentPorts
  bit() → Bool
  pair() → Bool × Bool

/-- Both reply alphabets admit uniform laws at every allowance `q`. -/
instance (q : ℕ) : ∀ i, Nonempty ((IndependentPorts q).Y i) := by
  intro i
  cases i <;> infer_instance

open Classical in
/-- The stored entry `false ↦ true` returns `true` and leaves the table unchanged. -/
example :
    let records : Unit → List (Bool × Bool) := fun _ => [(false, true)]
    URF.tableLaw bitInput records () false = ProbDist.single (records, true) := by
  intro records
  apply Subtype.ext
  simp only [URF.tableLaw, randomFunction.tableLaw, ProbStep.recordReplies,
    randomFunction.replyLaw, records, List.lookup_cons_self, Option.elim_some,
    Option.isNone_some, Bool.false_eq_true, ite_false, ProbDist.map_val,
    ProbDist.single, fTransform_single]

open Classical in
/-- Querying `true` after recording `false ↦ true` draws uniformly and appends that reply. -/
example :
    let records : Unit → List (Bool × Bool) := fun _ => [(false, true)]
    URF.tableLaw bitInput records () true =
      𝒰[Bool].map (fun y => (Function.update records () (records () ++ [(true, y)]), y)) := by
  intro records
  let : DecidableEq Bool := Classical.decEq Bool
  let : BEq Bool := instBEqOfDecidableEq
  have different : (true : Bool) ≠ false := by intro equal; cases equal
  simp only [URF.tableLaw, randomFunction.tableLaw, ProbStep.recordReplies,
    randomFunction.replyLaw, records, List.lookup_cons, List.lookup_nil,
    beq_eq_false_iff_ne.mpr different, Option.elim_none, Option.isNone_none, ite_true]
  congr 1
  funext y
  congr 1
  funext u
  cases u
  simp only [Function.update_self]

open Classical in
/-- Repeating the fresh query reuses its reply `y`, for either Boolean value. -/
example (y : Bool) :
    let records : Unit → List (Bool × Bool) := fun _ => [(true, y)]
    URF.tableLaw bitInput records () true = ProbDist.single (records, y) := by
  intro records
  apply Subtype.ext
  simp only [URF.tableLaw, randomFunction.tableLaw, ProbStep.recordReplies,
    randomFunction.replyLaw, records, List.lookup_cons_self, Option.elim_some,
    Option.isNone_some, Bool.false_eq_true, ite_false, ProbDist.map_val,
    ProbDist.single, fTransform_single]

open Classical in
/-- Recording either reply at `false` leaves the distinct input `true` uniform. -/
example (y : Bool) : URF.replyLaw bitInput (fun _ => [(false, y)]) () true = 𝒰[Bool] := by
  let : DecidableEq Bool := Classical.decEq Bool
  let : BEq Bool := instBEqOfDecidableEq
  have different : (true : Bool) ≠ false := by intro equal; cases equal
  simp only [URF.replyLaw, randomFunction.replyLaw, List.lookup_cons, List.lookup_nil,
    beq_eq_false_iff_ne.mpr different, Option.elim_none]

open Classical in
/-- A reply at the bit-valued port leaves the pair-valued port uniform. -/
example (reply : Bool) :
    URF.replyLaw (IndependentPorts 2)
      (Function.update (fun _ => []) .bit [((), reply)]) .pair () = 𝒰[Bool × Bool] := by
  have distinct : IndependentPorts.Port.pair ≠ .bit := by
    intro impossible
    cases impossible
  simp only [URF.replyLaw, randomFunction.replyLaw, Function.update_of_ne distinct,
    List.lookup_nil, Option.elim_none]

/-- A compatible adaptive converter sees the same two-port retained function. -/
example {B : Interface} (α : TypedConverter B (IndependentPorts 2)) :
    α • URF.lazy (IndependentPorts 2) = α • URF (IndependentPorts 2) := by
  rw [URF.lazy_eq]

#print axioms Commons.URF.lazy_eq

end LazyRandomFunctionTests
