# Constructive Cryptography proof-routing subworkflow

Use this subworkflow after the CC construction root is known but its
composition, simulation, context, transport, or lower-layer comparison route
is not. Its output is one visible CC proof spine and a seeded obligation DAG,
not a collection of potentially useful lemmas.

## Freeze the formal root

Write the exact theorem or API endpoint, including orientation, parameters,
interfaces, domains, and hypotheses. Keep the functional contract beside it so
that a tempting theorem with a different conclusion cannot become the new task
by accident.

For a repair with an established route, begin from the current Lean goal and
signature. For a new mathematical theorem, begin from the paper-level
argument. Choose the starting evidence that matches the uncertainty.

## Display the semantic spine

Write the shortest known sequence from the requested conclusion to facts that
can be proved or reused. Expose every material equality, inequality,
equivalence, induction step, construction, or reduction. For each hop record:

- the exact theorem or direct argument;
- its substantive hypotheses;
- whether it is exact or loses strength;
- any representation or coercion bridge; and
- the owning layer.

The first quantity or proposition must be the formal root. Auxiliary objects
do not become new objectives; connect them to the root by an explicit hop.

## Preserve the CC proof layers

A common spine has this direction:

```text
requested CC construction or realization
<- deterministic composition, context, transport, or simulator assembly
<- exact converter/resource equality or selected RS distance leaf
<- conditional-equivalence, H, coupling, counting, or other owning-layer fact
```

Not every proof uses every layer, but do not start from a numerical RS bound
and silently treat it as the CC theorem. Name the CC rule that consumes the
leaf. Keep simulator choice, ideal resource, corruption pattern, context, and
other non-canonical cryptographic choices explicit rather than delegating them
to broad automation.

## Compare routes without growing production

When several proof techniques are plausible, compare them in scratch using:

- mathematical validity and source fidelity;
- match with the current model and endpoint signatures;
- theorem strength and scope;
- number and difficulty of genuinely new obligations;
- dependency direction; and
- downstream readability.

Do not implement complete production branches in parallel merely to see which
one works. A focused Lean probe may test a doubtful signature, false lemma, or
missing hypothesis. Preserve a failed probe in scratch only when it records
useful evidence.

For an exact Random Systems comparison exposed by the CC spine, use
`$random-systems-proofs` and its route-specific references rather than
reconstructing H, conditional-equivalence, coupling, or counting logic here.
If the requested result itself is only an RS comparison, leave this suite and
use that skill alone.

## Select and probe the endpoint

Inspect the live declaration and copy its exact hypotheses. Apply it in the
target or a focused scratch skeleton. Compare the generated goals with the
semantic spine.

Classify a mismatch before changing code:

- **model mismatch:** the carrier, equality, domain, action, or ownership is
  wrong; return to the modeling subworkflow;
- **route mismatch:** the endpoint proves the wrong shape or creates false
  obligations; choose another route;
- **elaboration mismatch:** imports, namespaces, coercions, or instances hide
  the intended application; resolve it during implementation; or
- **genuine leaf:** the selected route requires a new mathematical fact.

Do not generalize the endpoint merely to avoid understanding a mismatch.

## Seed the obligation DAG

Use [dag-schema.md](dag-schema.md). Add the root, the selected endpoint or
outer proof hop, and only the exact children exposed by its signature, the
paper spine, or actual Lean goals.

For every leaf search current signatures before marking it `NEW`. Record its
direct consumer and preliminary fate. If a route changes, replace the affected
branch and reclassify reusable nodes against the new route. Investment in the
old branch is not a consumer edge.

## Exit artifact

Hand implementation:

```text
formal root:
selected route and endpoint:
displayed proof spine:
material hypotheses:
seeded DAG:
rejected route(s) and concrete reason:
open modeling issue: NONE or exact issue:
```

Do not begin production implementation while an open modeling issue changes
the meaning of the root.
