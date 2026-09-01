# Paper sketch, obligation ledger, and reuse search

This is the repository's recommended planning workflow. It is not a theorem
about how every proof must be discovered.

Organize every new security argument around one comparison spine: the exact
distance or advantage between two specified observable systems. Alternative
techniques may provide different and composable certificates for that same
quantity, but every auxiliary object must be connected to it by a displayed,
justified equality or inequality.

## Contents

- [Choose the starting point](#choose-the-starting-point)
- [Write the paper sketch](#write-the-paper-sketch)
- [Audit a paper adaptation](#audit-a-paper-adaptation)
- [Build the obligation ledger](#build-the-obligation-ledger)
- [Search for reuse](#search-for-reuse)
- [Probe the endpoint](#probe-the-endpoint)

## Choose the starting point

For a new result whose argument is not fixed, start with mathematics: determine
the systems, observation model, metric, finite statement, and proof idea before
letting the available API choose the bound.

For a repair or refactor where the theorem statement and route already exist,
start by inspecting the current Lean goal, imports, declaration signature, and
build status. A paper-first prohibition is counterproductive when the problem
is an elaboration or migration mismatch.

Lean can refute a proposed statement or expose a missing hypothesis, but it
does not substitute for the intended cryptographic argument.

## Write the paper sketch

For a new security theorem, keep a Markdown sketch under `sketches/` when the
repository convention calls for one. Use ordinary mathematical notation and
include:

### 1. Objects

- the two systems `S` and `T`, often the real and ideal systems;
- query/answer interfaces;
- adversary or environment class;
- simulator, monitor, joint law, or transcript predicate, when applicable; and
- all parameters and domain restrictions.

### 2. Claim

State the intended finite theorem as a bound or characterization of the chosen
system distance, with its orientation, observation model, query restriction,
and domain hypotheses. If only an asymptotic target is known, label it as such
and record the missing finite form.

### 3. Argument

Display the sequence of equalities and inequalities. For each hop, state:

- the theorem or direct argument used;
- its material hypotheses;
- where numerical slack enters; and
- whether the hop is exact.

The first displayed quantity must be the original system distance. If a route
introduces representatives, a monitor, a game, a coupling, a transcript
predicate, or a signed law, show the theorem that connects it to the preceding
quantity.

### 4. Competing routes

Record the routes considered and a mathematical reason for the choice. Do not
claim the list is exhaustive.

### 5. Open claims

Give every unproved step a name and exact statement. Distinguish a conjectured
estimate from a verified source theorem.

## Audit a paper adaptation

When adapting a source proof to a modified construction, make a term/event
table:

| Source term or event | Construction-specific status | Evidence |
| --- | --- | --- |
| retained | same mechanism remains | exact lemma or argument |
| reduced | the mechanism survives with a smaller count | exact replacement |
| eliminated | a construction invariant makes it impossible | invariant proof |
| unresolved | no proof yet | named open claim |

This table is unnecessary for an original proof with no source decomposition.
For a paper adaptation, it prevents inherited terms from being accepted without
checking whether the new construction changes them.

Use text extraction to locate passages when available, then verify the rendered
PDF page. A zero search result is not evidence that a scanned paper omits a
definition.

## Build the obligation ledger

Select a candidate Lean endpoint and copy its exact current hypotheses. Those
hypotheses seed the ledger; they are not necessarily the whole ledger. Add:

- model/representation bridges;
- normalization, nonnegativity, and totality facts;
- filtering or domain equalities;
- construction-specific counting or simulation lemmas;
- arithmetic conversions; and
- final metric/security-shell bridges.

For each node record:

```text
name:
statement:
needed by:
origin: REUSE | ADAPT | NEW
fate: INLINE | SCRATCH | PRODUCTION
status: OPEN | CLOSED
automation candidate: optional tactic or NONE
evidence or search record:
```

The comparison theorem is the root. `needed by` names the direct consumer, so
every task-created `PRODUCTION` node must have a path to that root. Seed the
ledger from the checked endpoint and actual Lean goals rather than from a
speculative helper family. If the route changes, replace the affected branch
and prune task-created nodes that no longer have a consumer path; preserve
pre-existing and unrelated work.

Typical principal obligations—not complete signatures—include:

| Route | Principal mathematical obligations |
| --- | --- |
| H equality-on-good | fixed-query equality; uniform adaptive ideal bad mass |
| H ratio | pointwise one-sided ratio; uniform adaptive ideal bad mass |
| Strict CE | monotonicity; conditioned-law equality; uniform blind winning bound |
| Honest coupling | joint law; two marginals; disagreement estimate |
| Finite union | event cover; individual masses; sum estimate |

Prefer leaves-first implementation once the interfaces are stable. Top-down
restatement is legitimate when a leaf reveals that the intended statement is
wrong.

## Search for reuse

For each node:

1. inspect `CHEATSHEET.md` and current route/status notes;
2. use `rg` for the mathematical concept and likely declaration fragments;
3. inspect exact declarations with Lean-LSP;
4. use local/goal-state search;
5. search Mathlib for construction-independent lemmas; and
6. check the primary source when theorem scope is uncertain.

Classify the result:

- `REUSE`: a current declaration matches after checking hypotheses;
- `ADAPT`: an existing theorem can be responsibly generalized or wrapped;
- `NEW`: no suitable declaration was found; preserve the search record.

Do not stop merely because the first hit has a familiar name. Check its
strength, orientation, proof route, build status, and axioms. Do not generalize
in place without considering ownership, dependency direction, and callers.

## Probe the endpoint

Use a focused scratch file or the target theorem to apply the endpoint and
inspect generated goals. Prefer Lean-LSP; otherwise run
`lake env lean <single-file>`.

Compare the goals with the ledger. A mismatch can come from:

- a wrong endpoint or paper plan;
- omitted implicit hypotheses;
- imports or namespaces;
- coercions and inferred instances;
- a stale declaration or olean; or
- an additional model bridge.

Do not diagnose the cause from the mismatch alone. Inspect the actual goal.
Once the skeleton is stable, fill named leaves, remove temporary admissions,
run focused gates, and audit the final theorem's axioms.
