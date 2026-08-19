/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Winnability
import RandomSystems.System.ClassDistance

/-!
# Goal-state display for the landed notations

The paper symbols are declared where their objects are defined —
`Adv(S, T)`/`Adv⊥(S, T)` and `tr(s, e)`/`tr(S, e)` in `System/Environment.lean`,
`ν(G)`/`ν[G]` in `System/Game.lean`, `ω(G)`/`ω[G]` in `System/Winnability.lean`,
`Δ(S, T)` in `System/ClassDistance.lean`, `·↓ₓ`/`·↓ᵧ` in
`System/Environment.lean`.  A `notation` whose expansion is one constant applied
to its own variables, in order, gets an unexpander from Lean for free, so most
of them already round-trip in a goal view: `Adv(S, T)`, `Adv⊥(S, T)`,
`Δ(S, T)`, `ν(G)`, `ω(G)`, `t↓ₓ`, `t↓ᵧ`.  The receipts below pin that.

Three do not, for two mechanical reasons, and this module supplies them:

* `ν[G]` and `ω[G]` expand to a *nested* application,
  `ENNReal.ofReal (supWinProb G)`, so no unexpander is generated and a bound
  against Definition 2.25 or 2.36 prints its coercion noise — exactly the noise
  the notation exists to hide.  The unexpander is registered on
  `ENNReal.ofReal` and fires only when the argument has already been displayed
  as `ν(G)` or `ω(G)`.
* `tr(s, e)` and `tr(S, e)` expand with their arguments *swapped*
  (`tr e s`, `trLaw e S`), because Lanzenberger writes the system first and the
  functions take the environment first.  Lean generates no unexpander for a
  permuted expansion.

Every unexpander here falls through to the default printer when its pattern
does not match, and all of them are suppressed by the standard
`set_option pp.notation false`, which is how one asks to see the raw terms.
-/

namespace RandomSystems.Notation

open Lean
open scoped RandomSystems.System RandomSystems.PDS RandomSystems.PDG

/-- Display `ENNReal.ofReal (ν(G))` as `ν[G]` and `ENNReal.ofReal (ω(G))` as
`ω[G]` — the metric-side readings of Lanzenberger Definitions 2.25 and 2.36.
`Adv⊥` is `ℝ≥0∞`-valued (Ruling R4) while `ν` and `ω` are reals, so every
statement relating them carries the coercion; the notation writes it once and
this unexpander keeps it written once in the goal too. -/
@[app_unexpander ENNReal.ofReal]
def unexpandOfRealWinning : PrettyPrinter.Unexpander
  | `($_ ν($G)) => `(ν[$G])
  | `($_ ω($G)) => `(ω[$G])
  | _ => throw ()

/-- Display `RandomSystems.System.tr e s` as Lanzenberger Definition 2.12's
`tr(s, e)`.  The expansion permutes its arguments, so Lean generates no
unexpander for the notation itself. -/
@[app_unexpander RandomSystems.System.tr]
def unexpandTr : PrettyPrinter.Unexpander
  | `($_ $e $s) => `(tr($s, $e))
  | _ => throw ()

/-- Display `RandomSystems.PDS.trLaw e S` as Lanzenberger Definition 2.12's
`tr(S, e)` at the probabilistic level.  Permuted expansion again. -/
@[app_unexpander RandomSystems.PDS.trLaw]
def unexpandTrLaw : PrettyPrinter.Unexpander
  | `($_ $e $S) => `(tr($S, $e))
  | _ => throw ()

/-! ## Firing receipts

Each notation is checked against the printed form of a term that uses it.  A
refactor that renames an object, reorders its arguments, or drops a scope
turns one of these into a `#guard_msgs` failure rather than into silently
raw goals. -/

section Receipts

variable {X Y : Type} (S T : PDS X Y) (G : PDG X Y) (e : System.DDE Y X)
  (s : System.DDS X Y) (t : List (X × Option Y))

/-- info: Adv(S, T) : ENNReal -/
#guard_msgs in
#check (PDS.Adv S T)

/-- info: Adv⊥(S, T) : ENNReal -/
#guard_msgs in
#check (PDS.advFullyDefined S T)

/-- info: Δ(S, T) : ENNReal -/
#guard_msgs in
#check (PDS.classDistance S T)

/-- info: ν(G) : ℝ -/
#guard_msgs in
#check (PDG.supWinProb G)

/-- info: ν[G] : ENNReal -/
#guard_msgs in
#check (ENNReal.ofReal (PDG.supWinProb G))

/-- info: ω(G) : ℝ -/
#guard_msgs in
#check (PDG.infWinnability G)

/-- info: ω[G] : ENNReal -/
#guard_msgs in
#check (ENNReal.ofReal (PDG.infWinnability G))

/-- info: tr(s, e) : Part (System.Transcript X Y) -/
#guard_msgs in
#check (System.tr e s)

/-- info: tr(S, e) : Probability.Distribution (Option (System.Transcript X Y)) -/
#guard_msgs in
#check (PDS.trLaw e S)

/-- info: t↓ₓ : List X -/
#guard_msgs in
#check (System.transcriptInputs t)

/-- info: t↓ᵧ : List (Option Y) -/
#guard_msgs in
#check (System.transcriptOutputs t)

end Receipts

end RandomSystems.Notation
