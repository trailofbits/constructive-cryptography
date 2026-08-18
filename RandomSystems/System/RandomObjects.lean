/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Absorb
import RandomSystems.System.Environment
import Probability.Counting

/-!
# The named random objects

CR18 Definition 3.15 presents a random function and a random permutation as
*function-valued random variables*, and Example 3.5 names the two the rest of
the notes use: the uniform random function `R_{m,n}` and the uniform random
permutation `P_m`.  That presentation is already the carrier's: a `PDS` **is** a
distribution over deterministic systems (Lanzenberger Definition 2.14), and
`System.functionEvaluator` is the map from a function to the system that
evaluates it.  So the objects here are one pushforward each,

  `object := fTransform (functionEvaluator ∘ ·) (uniform …)`,

and there is nothing to define beyond the names and their receipts.

## Scope: finite alphabets only (FLAG F-1)

Every object below carries `[Fintype]` on the type it randomizes, so every one
of them is an honest finitely supported distribution over deterministic
systems.  The variable-input-length objects of the source — the VIL-URF `V_n`
of Example 3.7 and Definition 6.1, CR18's `PO_k` — are **not** here and cannot
be: the source itself says their sample space is uncountable, so no `PDS`
realizes them (PHI-SPEC R1; LEDGER FLAG F-1).  They enter downstream as
*families of bounded slices*, which is how every quantitative statement uses
them anyway, and the slicing operation is `System.filterQueries`.

## The beacon is a slice, and its queries are its rounds

`beacon` is the one object whose printed form is not a function-valued random
variable.  CR18 Definition 3.1's `𝒴`-source has a *unary* input alphabet and
Example 3.2's beacon `B_n` answers each trigger with fresh randomness, so an
unbounded beacon needs unboundedly much randomness and is outside the carrier
for the same reason `V_n` is.  The bounded slice is `beacon Y n`, and it is
presented with the **round as the query**: `Fin n` is the trigger alphabet,
query `i` is the `i`-th trigger.  Under PHI-SPEC R3 (addressing is exogenous —
an interface is a set of queries) that is a legitimate interface, and on the
beacon's own query pattern — each round triggered once — it has exactly the
beacon's law, `n` independent uniform values.  What the presentation adds is
an answer to a question the beacon does not pose: a *repeated* round index is
answered consistently rather than freshly.  Consumers that need the printed
one-trigger interface should say so explicitly; nothing downstream of this
file assumes it.

## These live at their own alphabets

`urf X Y : PDS X Y`, not `Phi`.  The inclusion into the universal carrier is
`ofTyped`, which is an *isometry* (`PDS.advFullyDefined_ofTyped`), so no
distance statement is lost by stating these at the alphabet where the counting
happens and moving afterwards.
-/

namespace RandomSystems

open Probability (Distribution)

universe u v

noncomputable section

namespace PDS

variable {X : Type u} {Y : Type v}

/-! ## The objects -/

/-- **CR18 Definition 3.15 / Example 3.5's uniform random function `R_{m,n}`**:
the `(𝒳,𝒴)`-random function whose function-valued random variable is uniform
over `𝒳 → 𝒴`.

Definition 3.15's "random variable over functions" is the pushforward, and
`System.functionEvaluator` is the reading of a function as a system: every
nonempty history is answered, by applying the sampled function to the last
query. -/
def urf (X : Type u) (Y : Type v) [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    PDS X Y :=
  Distribution.fTransform System.functionEvaluator (Distribution.uniform (X → Y))

/-- **CR18 Definition 3.15 / Example 3.5's uniform random permutation `P_m`**:
the `𝒳`-random permutation whose function-valued random variable is uniform
over the permutations of `𝒳`.

The sampled object is an `Equiv.Perm X` and the system evaluates its underlying
function; keeping the permutation itself as the sample is what makes the
counting laws of `Probability.Counting` — `uniform_perm_consistent_mass_eq` —
apply to this system directly. -/
def urp (X : Type u) [Fintype X] [DecidableEq X] : PDS X X :=
  Distribution.fTransform (fun π : Equiv.Perm X => System.functionEvaluator (π : X → X))
    (Distribution.uniform (Equiv.Perm X))

/-- **CR18 Example 3.3's one-shot uniform source `U_n`**: one uniform value of
`𝒴`, delivered on every query.  The sampled object is the value; the system is
the constant function at it, so repeated queries see the *same* value — which
is what makes `U_n` a random *variable* made available as a system, and not a
beacon. -/
def unif (X : Type u) (Y : Type v) [Fintype Y] [Nonempty Y] : PDS X Y :=
  Distribution.fTransform (fun y : Y => System.functionEvaluator (fun _ : X => y))
    (Distribution.uniform Y)

/-- **CR18 Example 3.2's beacon `B_n`, at `n` rounds**: fresh uniform
randomness per round, presented with the round as the query (see the module
header — the unbounded beacon is outside the carrier by FLAG F-1, and this is
the bounded slice).

Definitionally the uniform random function on the round alphabet; the identity
is `beacon_eq_urf`, and it is a definitional unfolding rather than a theorem
about two objects. -/
def beacon (Y : Type v) [Fintype Y] [Nonempty Y] (n : ℕ) : PDS (Fin n) Y :=
  urf (Fin n) Y

theorem beacon_eq_urf (Y : Type v) [Fintype Y] [Nonempty Y] (n : ℕ) :
    beacon Y n = urf (Fin n) Y := rfl

/-! ## Receipt 1 — they are probability distributions

The sub-probability clauses of the parallel and converter layers
(`parF_left_mem_nonexpandingConverters`, `edist_parF_right_le`, …) are
discharged for all four objects at once by `Distribution.fTransform_isProbDist`
at `Distribution.uniform_isProbDist`. -/

theorem isProbDist_urf (X : Type u) (Y : Type v) [Fintype X] [DecidableEq X] [Fintype Y]
    [Nonempty Y] : (urf X Y).isProbDist :=
  Distribution.fTransform_isProbDist _ Distribution.uniform_isProbDist

theorem isProbDist_urp (X : Type u) [Fintype X] [DecidableEq X] : (urp X).isProbDist :=
  Distribution.fTransform_isProbDist _ Distribution.uniform_isProbDist

theorem isProbDist_unif (X : Type u) (Y : Type v) [Fintype Y] [Nonempty Y] :
    (unif X Y).isProbDist :=
  Distribution.fTransform_isProbDist _ Distribution.uniform_isProbDist

theorem isProbDist_beacon (Y : Type v) [Fintype Y] [Nonempty Y] (n : ℕ) :
    (beacon Y n).isProbDist :=
  isProbDist_urf (Fin n) Y

/-! ## Receipt 2 — one domain, and it is the whole of `𝒳⁺`

Lanzenberger Definition 2.14's common-domain clause is `PDS.HasDomain`, at a
*named* domain so that two systems can be said to share one.  Every object here
has the same one — all nonempty histories — which is exactly what makes them
usable as the ideal side of a two-system distance statement. -/

/-- Every pushforward of *function evaluators* has the total domain: an atom of
the pushforward is an evaluator, and an evaluator answers every nonempty
history.  The four receipts below are this lemma at their sampling maps. -/
theorem hasDomain_fTransform_functionEvaluator {A : Type*} (g : A → (X → Y))
    (D : Distribution A) :
    HasDomain (Distribution.fTransform (fun a => System.functionEvaluator (g a)) D)
      {l : List X | l ≠ []} := by
  intro s hs
  obtain ⟨a, -, rfl⟩ := Distribution.exists_mem_support_of_mem_support_fTransform _ _ hs
  exact System.dom_functionEvaluator (g a)

theorem hasDomain_urf (X : Type u) (Y : Type v) [Fintype X] [DecidableEq X] [Fintype Y]
    [Nonempty Y] : HasDomain (urf X Y) {l : List X | l ≠ []} :=
  hasDomain_fTransform_functionEvaluator (fun f => f) _

theorem hasDomain_urp (X : Type u) [Fintype X] [DecidableEq X] :
    HasDomain (urp X) {l : List X | l ≠ []} :=
  hasDomain_fTransform_functionEvaluator (fun π : Equiv.Perm X => (π : X → X)) _

theorem hasDomain_unif (X : Type u) (Y : Type v) [Fintype Y] [Nonempty Y] :
    HasDomain (unif X Y) {l : List X | l ≠ []} :=
  hasDomain_fTransform_functionEvaluator (fun y : Y => fun _ : X => y) _

theorem hasDomain_beacon (Y : Type v) [Fintype Y] [Nonempty Y] (n : ℕ) :
    HasDomain (beacon Y n) {l : List (Fin n) | l ≠ []} :=
  hasDomain_urf (Fin n) Y

/-! ## Receipt 3 — the URP consistency mass

`Probability.Counting.uniform_perm_consistent_mass_eq` is the exact mass of the
uniform permutation realizing `q` distinct constraints, `(|𝒳|−q)!/|𝒳|!`.  It is
stated about `Equiv.Perm`; what makes it a statement about the *system* `urp X`
is that the sampling map is injective on the observable — a permutation is
recovered from the answers of its evaluator. -/

/-- What a function evaluator answers, read through `System.answer` (the
`⊥`-completion's answer, which is what every metric statement observes): the
sampled function at the query, after any history. -/
theorem answer_functionEvaluator (f : X → Y) (l : List X) (x : X) :
    System.answer (System.functionEvaluator f) l x = some (f x) := by
  rw [System.answer_eq]
  rw [dif_pos (show System.keptPrefix (System.functionEvaluator f) l ++ [x]
      ∈ System.dom (System.functionEvaluator f) by
    rw [System.dom_functionEvaluator]
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil x []))]
  rw [System.functionEvaluator_output]

/-- **The uniform random permutation's exact consistency mass, at the system.**
For `q` distinct queries and `q` distinct answers, the mass of the laws of
`urp X` that answer the queries that way is `(|𝒳|−q)!/|𝒳|!`.

This is `Probability.Counting.uniform_perm_consistent_mass_eq` transported
along `Distribution.mass_fTransform`; the event is stated with `System.answer`,
at the empty history, because that is the observable every distance statement
reads. -/
theorem mass_urp_answer_eq {X : Type u} [Fintype X] [DecidableEq X] {q : ℕ}
    (xs : Fin q → X) (hx : Function.Injective xs)
    (ys : Fin q → X) (hy : Function.Injective ys) (h_le : q ≤ Fintype.card X) :
    (urp X).mass (fun s => ∀ i, System.answer s [] (xs i) = some (ys i)) =
      ((Fintype.card X - q).factorial : ℝ) / ((Fintype.card X).factorial) := by
  rw [urp, Distribution.mass_fTransform,
    ← Probability.Counting.uniform_perm_consistent_mass_eq xs hx ys hy h_le]
  refine Distribution.mass_congr _ fun π => ?_
  simp only [answer_functionEvaluator, Option.some.injEq]

end PDS

end

end RandomSystems
