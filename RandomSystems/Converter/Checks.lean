/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter

set_option autoImplicit false

/-!
# Query-indexed converter checks

This module verifies the public query-indexed converter root.
-/

namespace RandomSystems.Ambient.Checks

private inductive TableQuery
  | first
  | second

/-- A stateful DDS can be written directly as a recursive Lean function on
its complete attempted-query history. -/
private def tableSystem : DDS (Interface.single TableQuery Bool) :=
  fun history =>
    some (history.queries.foldl (fun answer query =>
      match query with
      | .first => !answer
      | .second => answer) false)

example : tableSystem (History.singleton .first) = some true :=
  rfl

example :
    tableSystem (History.snoc (History.singleton .first) .first) =
      some false :=
  rfl

/-- A history-sensitive DDC can likewise be assembled from an ordinary
predicate and ordinary Lean functions. -/
private noncomputable def atMostTwoQueries :
    DDC (Interface.single TableQuery Bool)
      (Interface.single TableQuery Bool) :=
  DDC.filter (fun history => history.length ≤ 2) id
    (fun _ answer => answer)

example :
    applySystem atMostTwoQueries tableSystem =
      fun history =>
        if history.queries.length ≤ 2 then
          tableSystem (History.map id history)
        else none := by
  rw [atMostTwoQueries]
  exact DDC.applySystem_filter_of_prefix_closed
      (fun history : List TableQuery => history.length ≤ 2)
      (by
        intro prior history isPrefix accepted
        exact isPrefix.length_le.trans accepted)
      id (fun (_ : TableQuery) (answer : Option Bool) => answer) tableSystem

/-! ## Finite inner-query bounds -/

private abbrev Outer := Interface.single Nat Unit
private abbrev Inner := Interface.single Unit Unit

/-- The outer query `n` selects exactly `n` consecutive inner queries. -/
private noncomputable def raw : DDC.Raw Outer Inner :=
  fun history =>
    if DDC.History.innerDepth history < history.lastOuter then
      Part.some (Sum.inl ())
    else
      Part.some (Sum.inr (some ()))

private theorem raw_complete : DDC.Raw.Complete raw := by
  intro history _
  unfold raw
  split <;> exact trivial

private theorem raw_branchFinite : DDC.Raw.BranchFinite raw := by
  let remaining := fun history : DDC.History Outer Inner =>
    (show Nat from history.lastOuter) - DDC.History.innerDepth history
  refine Subrelation.wf ?_ (measure remaining).wf
  intro after before continuation
  rcases continuation with ⟨query, reply, responds, rfl⟩
  have less : DDC.History.innerDepth before < before.lastOuter := by
    unfold raw at responds
    split at responds
    · assumption
    · simp at responds
  change remaining (before.snocInner query reply) < remaining before
  simp only [remaining, DDC.History.lastOuter_snocInner,
    DDC.History.innerDepth_snocInner]
  omega

private noncomputable def converter : DDC Outer Inner :=
  DDC.ofRaw raw raw_complete raw_branchFinite

private def history (limit : Nat) : Nat → DDC.History Outer Inner
  | 0 => DDC.History.singleton limit
  | depth + 1 => (history limit depth).snocInner () none

@[simp]
private theorem innerDepth_history (limit depth : Nat) :
    DDC.History.innerDepth (history limit depth) = depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [history, inductionHypothesis]

@[simp]
private theorem lastOuter_history (limit depth : Nat) :
    (history limit depth).lastOuter = limit := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [history, inductionHypothesis]

private theorem history_admissible (limit depth : Nat)
    (atMost : depth ≤ limit) :
    DDC.Raw.Admissible raw (history limit depth) := by
  induction depth with
  | zero =>
      exact DDC.Raw.Admissible.start
        (A := Outer) (B := Inner) (show Outer.query from limit)
  | succ depth inductionHypothesis =>
      exact DDC.Raw.Admissible.afterInner
        (inductionHypothesis (by omega)) (by
          change Sum.inl () ∈ raw (history limit depth)
          rw [raw, if_pos]
          · exact Part.get_mem trivial
          · simpa only [innerDepth_history, lastOuter_history] using
              (show depth < limit by omega)) none

/-- Branch-finiteness does not imply one finite inner-query bound shared by
all outer queries. -/
example : ¬ DDC.Raw.HasFiniteInnerQueryBound converter.toFun := by
  change ¬ DDC.Raw.HasFiniteInnerQueryBound (DDC.Raw.canonicalize raw)
  rw [DDC.Raw.hasFiniteInnerQueryBound_canonicalize_iff]
  rintro ⟨bound, bounded⟩
  have admissible := history_admissible (bound + 1) (bound + 1) le_rfl
  have atMost := bounded (history (bound + 1) (bound + 1)) admissible
  rw [innerDepth_history] at atMost
  omega

/-! ## Query-indexed inner replies -/

private inductive Route
  | left
  | right

private abbrev FlatReply := Option Route

private def replyMatchesQuery : Route → FlatReply → Prop
  | _, none => True
  | expected, some actual => actual = expected

private abbrev FlatHistory := List (Unit ⊕ FlatReply)

private def sameHistory : FlatHistory :=
  [Sum.inl (), Sum.inr (some Route.left)]

/-- Jost's inner reply is the response to the inner query selected by the
converter. The same unindexed history can be valid after a left inner query
and invalid after a right inner query, so validity cannot be recovered from
that history alone. -/
example :
    ¬ ∃ valid : FlatHistory → Prop,
      (valid sameHistory ↔ replyMatchesQuery Route.left (some Route.left)) ∧
      (valid sameHistory ↔ replyMatchesQuery Route.right (some Route.left)) := by
  rintro ⟨valid, leftExact, rightExact⟩
  have validHistory : valid sameHistory := leftExact.mpr rfl
  have invalidRight : ¬ replyMatchesQuery Route.right (some Route.left) := by
    simp [replyMatchesQuery]
  exact invalidRight (rightExact.mp validHistory)

end RandomSystems.Ambient.Checks
