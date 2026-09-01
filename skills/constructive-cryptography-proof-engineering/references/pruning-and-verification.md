# Constructive Cryptography pruning and verification subworkflow

Use this subworkflow after the formal root works, and during cleanup reviews of
an existing diff. Its purpose is to prove that the delivered source needs the
retained task-created surface, not merely that Lean can build in its presence.

## Freeze the delivered CC root

Record the exact root statements and obtain a focused source build before
pruning. Keep unrelated user changes and pre-existing declarations outside the
automatic deletion scope. Repository cleanup is preservation-first.

Include representative builds for the CC surface and every changed lower-layer
RS or probability dependency. A clean RS leaf does not validate the CC
composition that consumes it, and a compiling CC wrapper does not validate an
admitted or stale lower-layer theorem.

## Audit diff closure

For every declaration added or materially generalized by the task, answer:

1. Which final DAG node is it?
2. What exact declaration or proof step consumes it?
3. What path reaches a formal root?
4. Why is it `PRODUCTION` instead of `INLINE` or `SCRATCH`?
5. Which current source location exercises it?

Search for usages with source-aware tools, but do not equate text matches with
semantic consumers. Check imports, qualified and unqualified references,
attributes such as `[simp]`, generated instances, and tactic registries.

Task-created nodes without satisfactory answers are cleanup work. Pre-existing
unused declarations require a separate preservation and ownership judgment;
do not delete them merely because the current task does not use them.

## Separate kernel and elaboration dependencies

The final kernel term records constants retained in the proof, while source
elaboration may additionally use simp lemmas, tactics, instances, macros, and
notation. Therefore:

- absence from the kernel closure suggests but does not prove source deadness;
- a source usage may guide elaboration without appearing in the final term;
- deleting an elaboration helper requires rewriting its firing site and
  rebuilding from source; and
- a stale `.olean` is not a deletion test.

For a named definitional reduction or one-off simp lemma, replace its source
use with the underlying definition or a local proof, remove the task-created
declaration, and rebuild the affected source. Retain it only if the deletion
test exposes a durable API role.

## Remove abandoned-route residue

Prune task-created:

- declarations disconnected from all final roots;
- wrappers for a rejected model or endpoint;
- duplicate `rfl` and one-step `simp` theorems;
- theorem families whose members merely repeat tactic syntax;
- imports and attributes needed only by removed helpers;
- scratch probes accidentally placed in production; and
- comments or documents that describe obsolete work-in-progress architecture.

Move useful experiments to the repository's ignored scratch area when future
work is intended. Do not destroy work that the user asked to preserve.

## Verify in increasing scope

Run the repository-specific equivalent of:

1. focused elaboration of each changed source;
2. the owning module or package build;
3. representative downstream consumer builds;
4. axiom inspection for important roots and headline corollaries;
5. scans for `sorry`, `admit`, unintended axioms, forbidden options, and
   repository-specific anti-patterns; and
6. diff hygiene and warning checks, including new unused simp or tactic rules.

Use the repository's prescribed commands and accepted axiom envelope. A full
build without an axiom check does not establish proof completion. A clean
kernel term without rebuilding the source does not establish cleanup.

## Produce the closure receipt

Report:

```text
functional contract:
formal root(s):
retained declaration -> direct consumer -> root path:
inlined or removed task-created residue:
preserved scratch material:
focused build:
downstream build:
axiom receipt:
static checks:
known pre-existing issue:
```

Do not use line-count reduction or deletion volume as evidence of correctness.
The relevant result is that all required roots work and every retained
task-created production declaration has a justified role.
