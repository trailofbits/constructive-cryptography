---
name: random-systems-proofs
description: "Formalize, repair, or review fixed-interface Random Systems advantage and distance proofs in Lean 4. Route a specified comparison through live exact/hybrid bounds, transcript factorization, H-coefficient estimates, strict conditional equivalence, MPR07 symmetric common-part games, honest coupling, games and blind winning, bounded observation restriction, counting, or an explicit lower-bound environment. Use for standalone RS results and RS leaves inside CC proofs; do not use as the sole workflow for CC composition or resource lifting."
---

# Random Systems proof techniques

Start from one exact comparison between two observable systems and select only
techniques with a checked mathematical path and explicit production status.
This package routes current APIs and source-backed formalization work; it is
not mathematical authority. Verify source claims on rendered primary pages and
Lean claims against live signatures, focused builds, and axiom receipts.

## Fix the comparison before choosing a technique

Record:

- the two `PDS` values and their query/answer interfaces;
- the observation family: pair-admissible DDEs, a named common domain, or a
  narrower explicitly justified class;
- whether the root is `PDS.advantage`, `PDS.Adv`, a transcript-law
  `Probability.statDist`, an equality, or a lower bound;
- the orientation and all weight, nonnegativity, probability, domain,
  compatibility, and stopping hypotheses; and
- the finite target statement.

Keep this comparison as the root. A transcript factor, bad event, game,
monitor, coupling, cell partition, or explicit environment is a certificate
object only after a named theorem connects it to the root.

## Route through checked technique surfaces

Read only the references used by the selected proof spine:

| Technique | Use it when | Reference |
| --- | --- | --- |
| Exact equality, data processing, triangle/hybrid, or identical-until-bad | The comparison can be reshaped or bounded directly | [exact-hybrid-and-metric.md](references/exact-hybrid-and-metric.md) |
| Transcript factorization | A transcript-law comparison should cancel the common environment factor | [transcript-factorization.md](references/transcript-factorization.md) |
| H-coefficient | System transcript factors satisfy a ratio or finite-cell defect bound | [h-coefficient.md](references/h-coefficient.md) |
| Strict conditional equivalence | A probabilistic game conditioned on not winning matches a target PDS | [conditional-equivalence.md](references/conditional-equivalence.md) |
| MPR07 symmetric common-part games | Exact per-observer distance should be realized as the winning probability of two enhanced systems | [mpr07-symmetric-common-part.md](references/mpr07-symmetric-common-part.md) |
| Honest coupling | A nonnegative joint law with proved marginals makes disagreement tractable | [coupling.md](references/coupling.md) |
| Games and blind winning | The proof uses a `PDG`, winning probability, blindness, or game equivalence | [games-and-winning.md](references/games-and-winning.md) |
| Bounded observation restriction | A literal common-domain comparison needs a finite compatible stopping observer | [observation-restriction.md](references/observation-restriction.md) |
| Counting or event mass | A selected route has produced a concrete probability, fiber, or sum obligation | [counting.md](references/counting.md) |
| Direct computation or lower bound | The proof supplies an explicit environment, transcript event, or exact law | [direct-and-lower-bounds.md](references/direct-and-lower-bounds.md) |

Use [sketch-and-plan.md](references/sketch-and-plan.md) when the route creates
several obligations. Use [creative-search.md](references/creative-search.md)
only when the mathematical route or finite bound is genuinely unknown.

The MPR07 row is a primary-source-backed formalization route, not yet a single
live constructor theorem. Its forward game-equivalence bound has production
support, but the recursive common-part construction and exact-attainment
endpoint remain explicit obligations. Do not report that route as formalized
until those declarations compile and pass their axiom checks.

Techniques compose only through explicit bridges. Typical spines include:

```text
Adv(S,T)
  <= weighted transcript cells
  <= numerical sum
```

```text
Adv(game.underlying,target)
  <= supWinProb(blind game)
  <= epsilon
```

```text
statDist(trLaw D S,trLaw D T)
  = winProb D leftHat
  = winProb D rightHat
```

```text
Adv(S,T)
  <= Adv(S,H) + Adv(H,T)
  <= epsilon₁ + epsilon₂
```

Do not turn the certificate name into a new security objective.

## Do not advertise unavailable routes

Equivalent-representative attainment, abstract winnability `ω`, and a signed
or virtual joint are not current default production routes merely because an
older proof plan mentioned them. Use one only after locating its live import,
checking the exact endpoint, compiling it, and obtaining an acceptable axiom
receipt. A signed witness is never an honest `Probability.Coupling`.

The MPR07 construction is likewise not permission to assume an attaining pair
of games. Follow its reference as an implementation DAG until the symmetric
constructor and exact equalities exist in the current library.

Likewise, do not cite obsolete `RandomSystems/HTechnique/*`,
`RandomSystems/CondEquiv.lean`, `RandomSystems/SwitchingLemma.lean`, or the old
`maxAdvantage`/`PFunPDS` wrappers. The current fixed-interface surface is under
`RandomSystems.Technique`, `RandomSystems.TranscriptFactor`,
`RandomSystems.Game`, `RandomSystems.Distance`, and the owning `Probability`
modules.

## Control declaration growth

For a multi-declaration RS proof, or an RS leaf inside a CC construction, use
`$constructive-cryptography-proof-engineering` for the functional contract,
obligation DAG, implementation gate, and pruning pass. For a standalone RS
comparison, use the same root-path invariant locally: every task-created
production declaration must name its consumer and reach the comparison.

Apply the selected endpoint early and seed obligations from its exact
hypotheses and actual Lean goals. Do not create a family of likely H, CE,
coupling, or counting lemmas before a route consumes them.

## Preserve certificate boundaries

Keep these objects distinct:

- H-coefficient ratios concern `PDS.transcriptSystemFactor` and cancel an
  environment factor through `RandomSystems.TranscriptFactor`.
- Conditional equivalence is
  `ConditionalEquivalence.ConditionallyEquivalent` between a game and target
  and carries an initially-false condition.
- `EquivalentAsGames` compares pre-winning behavior; it is not conditional
  equivalence and not ordinary system equality.
- MPR07 Lemma 5 constructs two MBO-enhanced systems with a common pre-winning
  part; it is not completeness of the one-sided `game |≡ target` relation.
- A coupling is a nonnegative joint distribution with proved marginals.
- `PDG.supWinProb` is a supremum over winners; it is not abstract winnability.
- Counting discharges a leaf produced by another certificate and does not
  establish the reduction that produced it.

## Use the live automation surface

`RandomSystems.Tactics.ProofAutomation` currently exposes:

- `rs_normalize` and `rs_normalize?` for curated shrinking rewrites;
- `rs_routine` for assumptions, reflexivity, and registered structural side
  conditions; and
- `rs_conditional_equivalence domain using equivalent, winning` for the live
  CE advantage endpoint with explicit semantic witnesses.

These tactics do not select systems, domains, games, monitors, couplings,
partitions, or bounds. If one fails, inspect the import, target signature,
remaining goal, and inferred instances before changing the model.

## Work and verify from the goal state

1. Read `AGENTS.md`, `README.md`, `THEORY.md`, the owning module documentation,
   and the cited primary source required by repository policy.
2. Inspect the live endpoint and apply it DIRECTLY IN THE TARGET MODULE. Do not
   develop the result in a scratch file and re-derive it afterwards.
3. Search exact declarations before adding a helper.
4. Keep the displayed equality/inequality chain aligned with the paper
   argument; isolate normalization and coercion plumbing.
5. Compile the changed source, then the owning RS and downstream CC targets.
6. Inspect axioms for the root and important intermediate endpoints.
7. Scan for admissions, forbidden options, unused automation, and task-created
   declarations disconnected from the comparison.

If the result remains a paper sketch, partial formalization, conjectured bound,
or blocked migration surface, report exactly that.
