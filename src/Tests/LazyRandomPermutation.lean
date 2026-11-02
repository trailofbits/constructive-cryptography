module

public import Commons.Definitions.LazyPermutation

/-!
# Lazy random-permutation checks

The tests cover exact replay, equal positive mass on every unused output, and exhaustion: if all
outputs have occurred, every input is already recorded. The construction also accepts an
empty alphabet, and updates at one port leave another port's fresh-reply law unchanged.
The behavioral equality rewrites under an arbitrary typed converter.
-/

@[expose] public section

namespace LazyRandomPermutationTests

open Commons SystemAlgebra Probability Probability.Distribution
open scoped SystemAlgebra

-- `A` supplies finite alphabets, ports and the domain; each port has a bijection.
variable (A : Interface) [∀ i, Nonempty (A.X i ≃ A.Y i)]

open Classical in
/-- An existing record gives a point transition and leaves every port's records unchanged. -/
lemma tableLaw_lookup
    -- `hit` reads the stored reply `y` for query `i(x)` in `table`.
    (table : ∀ i, List (A.X i × A.Y i))
    (i : A.I) (x : A.X i) (y : A.Y i) (hit : (table i).lookup x = some y) :
    URP.tableLaw A table i x = ProbDist.single (table, y) := by
  apply Subtype.ext
  simp only [URP.tableLaw, ProbStep.recordReplies, URP.replyLaw, hit, Option.elim_some,
    ProbDist.map_val,
    ProbDist.single, fTransform_single, Option.isNone_some, Bool.false_eq_true, ite_false]

open Classical in
/-- Immediately repeating a fresh query returns exactly the previously sampled output. -/
lemma tableLaw_repeat
    -- `fresh` says the original `table` has no reply at `i(x)`; `y` is the first sampled reply.
    (table : ∀ i, List (A.X i × A.Y i))
    (i : A.I) (x : A.X i) (y : A.Y i) (fresh : (table i).lookup x = none) :
    URP.tableLaw A (Function.update table i (table i ++ [(x, y)])) i x =
      ProbDist.single (Function.update table i (table i ++ [(x, y)]), y) := by
  apply tableLaw_lookup
  simp only [Function.update_self, List.lookup_append, fresh, Option.none_or,
    List.lookup_cons_self]

omit [∀ i, Nonempty (A.X i ≃ A.Y i)] in
open Classical in
/-- When the recorded range is full, a consistent table has no fresh input. -/
lemma exhausted_lookup
    -- `consistent` supplies a completion of `table`; `full` says every port-`i` output is recorded.
    (table : ∀ i, List (A.X i × A.Y i))
    (consistent : (URP.completions A table).Nonempty) (i : A.I)
    (full : ∀ y : A.Y i, y ∈ (table i).map Prod.snd) (x : A.X i) :
    ∃ y, (table i).lookup x = some y := by
  cases hit : (table i).lookup x with
  | some y => exact ⟨y, rfl⟩
  | none =>
    obtain ⟨π, hπ⟩ := consistent
    exact (URP.apply_not_mem_range_of_mem_completions A table i x hit π hπ (full (π i x))).elim

open Classical in
/-- A partly filled consistent table gives every unused output positive mass, all equally. -/
lemma fresh_reply_uniform (table : ∀ i, List (A.X i × A.Y i))
    -- `consistent` gives a completing bijection; `fresh` selects a new input `i(x)`.
    (consistent : (URP.completions A table).Nonempty) (i : A.I) (x : A.X i)
    (fresh : (table i).lookup x = none) :
    (∀ y, y ∈ (URP.replyLaw A table i x).1.support ↔ y ∉ (table i).map Prod.snd) ∧
      (∀ y, y ∉ (table i).map Prod.snd → ∀ z, z ∉ (table i).map Prod.snd →
        URP.replyLaw A table i x y = URP.replyLaw A table i x z) := by
  let : Nonempty (A.Y i) :=
    ⟨(Classical.choice (inferInstance : Nonempty (A.X i ≃ A.Y i))) x⟩
  simp only [URP.replyLaw, fresh, Option.elim_none]
  constructor
  · obtain ⟨π, hπ⟩ := consistent
    exact fun y => ProbDist.mem_support_uniformOn_iff _
      ⟨π i x, URP.apply_not_mem_range_of_mem_completions A table i x fresh π hπ⟩ _ y
  · rw [← URP.completionLaw_map_eq_unusedLaw A table consistent i x fresh]
    exact fun y hy z hz => URP.completionLaw_apply_eq_of_unused A table consistent i x y z hy hz

open Classical in
/-- A direct call to the unused-output law on a full range uses its stated point fallback. -/
lemma unusedLaw_exhausted (table : ∀ i, List (A.X i × A.Y i))
    -- `full` exhausts the outputs at port `i`; `x` supplies the fallback image through a bijection.
    (i : A.I) (x : A.X i) (full : ∀ y : A.Y i, y ∈ (table i).map Prod.snd) :
    URP.unusedLaw A table i x = ProbDist.single
      ((Classical.choice (inferInstance : Nonempty (A.X i ≃ A.Y i))) x) := by
  let : Nonempty (A.Y i) :=
    ⟨(Classical.choice (inferInstance : Nonempty (A.X i ≃ A.Y i))) x⟩
  apply ProbDist.uniformOn_of_forall_not
  exact fun y hy => hy (full y)

open Classical in
/-- Updating a different port leaves this port's unused-output law unchanged. -/
lemma unusedLaw_other_port [DecidableEq A.I]
    -- `different` separates the updated port `i` from the queried port `j(x)`.
    (table : ∀ i, List (A.X i × A.Y i))
    (i j : A.I) (different : j ≠ i) (record : List (A.X i × A.Y i)) (x : A.X j) :
    URP.unusedLaw A (Function.update table i record) j x = URP.unusedLaw A table j x := by
  simp only [URP.unusedLaw, Function.update_of_ne different]

open Classical in
/-- A caller may replace the lazy presentation inside any compatible adaptive context. -/
lemma attached_lazy_eq
    -- `α` consumes the permutation at `A` and exposes the caller interface `B`.
    (B : Interface) (α : TypedConverter B A) :
    α • URP.lazy A = α • URP A := by
  rw [URP.lazy_eq]

open Classical in
/-- On a finite same-alphabet evaluation interface this is the source's random permutation. -/
example (X : Type) [Fintype X] (q : ℕ) :
    URP.lazy (Evaluation X X q) = URP (Evaluation X X q) := URP.lazy_eq _

-- The empty alphabet still admits its unique bijection; it has no possible input query.
example (q : ℕ) : URP.lazy (Evaluation Empty Empty q) = URP (Evaluation Empty Empty q) := by
  exact URP.lazy_eq _

#print axioms URP.lazy_eq
#print axioms exhausted_lookup
#print axioms fresh_reply_uniform

end LazyRandomPermutationTests
