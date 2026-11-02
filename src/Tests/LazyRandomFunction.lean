module

public import Commons.Definitions.Ideal

/-!
# Lazy random-function checks

The conditional laws verify exact replay after a recorded reply and uniform sampling at a
fresh input. Different inputs and ports stay uniform for every first reply, including
when the two ports have different reply types. `URF.lazy_eq` rewrites the full system under
an arbitrary typed converter, preserving its compatible adaptive interaction.
-/

@[expose] public section

namespace LazyRandomFunctionTests

open Commons SystemAlgebra Probability Probability.Distribution
open scoped SystemAlgebra

-- `A` fixes the ports, query/reply alphabets and admitted input domain.
variable (A : Interface) [∀ i, Nonempty (A.Y i)]

open Classical in
/-- A stored reply yields a point transition and keeps every port's records unchanged. -/
lemma tableLaw_lookup
    -- `table i` already returns `y` on input `x` at port `i`.
    (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i) (y : A.Y i)
    (hit : (table i).lookup x = some y) :
    URF.tableLaw A table i x = ProbDist.single (table, y) := by
  apply Subtype.ext
  simp only [URF.tableLaw, ProbStep.recordReplies, URF.replyLaw, hit, Option.elim_some,
    Option.isNone_some,
    Bool.false_eq_true, ite_false, ProbDist.map_val, ProbDist.single, fTransform_single]

open Classical in
/-- A fresh query draws uniformly and records the returned value only at its queried port. -/
example (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i)
    (miss : (table i).lookup x = none) :
    URF.tableLaw A table i x =
      𝒰[A.Y i].map (fun y => (Function.update table i (table i ++ [(x, y)]), y)) := by
  simp only [URF.tableLaw, ProbStep.recordReplies, miss, Option.isNone_none, ite_true,
    URF.replyLaw, Option.elim_none]

open Classical in
/-- After receiving `y` at a fresh input, repeating that input returns `y` with certainty. -/
example (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i) (y : A.Y i)
    (miss : (table i).lookup x = none) :
    URF.tableLaw A (Function.update table i (table i ++ [(x, y)])) i x =
      ProbDist.single (Function.update table i (table i ++ [(x, y)]), y) := by
  apply tableLaw_lookup
  simp only [Function.update_self, List.lookup_append, miss, Option.none_or,
    List.lookup_cons_self]

open Classical in
/-- A different input at the same port stays uniform for every previously returned reply. -/
lemma replyLaw_other_input
    -- `x` was queried at port `i`, yielding `y`; `different` makes `z` a fresh input there.
    (i : A.I) (x z : A.X i) (different : z ≠ x) (y : A.Y i) :
    URF.replyLaw A (Function.update (fun _ => []) i [(x, y)]) i z = 𝒰[A.Y i] := by
  simp only [URF.replyLaw, Function.update_self, List.lookup_cons, List.lookup_nil,
    beq_eq_false_iff_ne.mpr different, Option.elim_none]

open Classical in
/-- A different port stays uniform for every first reply, expressing conditional independence. -/
lemma replyLaw_other_port [DecidableEq A.I]
    -- `i` and `j` are distinct ports; `y` is the reply just recorded at `i(x)`.
    (i j : A.I) (different : j ≠ i) (x : A.X i) (y : A.Y i) (z : A.X j) :
    URF.replyLaw A (Function.update (fun _ => []) i [(x, y)]) j z = 𝒰[A.Y j] := by
  simp only [URF.replyLaw, Function.update_of_ne different, List.lookup_nil, Option.elim_none]

-- Each `bit(())` returns `Bool`; each `pair(())` returns `Bool × Bool`. The chosen allowance
-- bounds the total number of queries across both ports.
interface IndependentPorts
  bit() → Bool
  pair() → Bool × Bool

open Classical in
/-- Both reply types are inhabited for every total query allowance `q`. -/
instance (q : ℕ) : ∀ i, Nonempty ((IndependentPorts q).Y i) := by
  intro i
  cases i <;> infer_instance

open Classical in
/-- Uniformity at the pair-valued port is unchanged by either possible bit-valued reply. -/
example (reply : Bool) :
    URF.replyLaw (IndependentPorts 2)
      (Function.update (fun _ => []) .bit [((), reply)]) .pair () = 𝒰[Bool × Bool] := by
  have distinct : IndependentPorts.Port.pair ≠ .bit := by
    intro impossible
    cases impossible
  exact replyLaw_other_port (IndependentPorts 2) .bit .pair distinct () reply ()

open Classical in
/-- Any domain-preserving adaptive converter sees exactly the existing URF behavior. -/
example {B : Interface}
    -- `α` presents the URF interface `A` through the outside interface `B`.
    (α : TypedConverter B A) :
    α • URF.lazy A = α • URF A := by
  rw [URF.lazy_eq]

#print axioms Commons.URF.lazy_eq

end LazyRandomFunctionTests
