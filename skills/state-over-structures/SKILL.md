---
name: state-over-structures
description: Part of the CC skills (`skills/README.md`); fires after `plan-the-work` and `instantiate` (or an accepted design), at the moment a statement is written. Use before writing or changing any theorem or lemma statement, security definition, assumption, predicate used in statements, or endpoint in the constructive-cryptography library or a project built on it, when auditing or deleting existing statements, and when a plan step says "statement available". Statements are made over structures, with contracts and assumptions as hypotheses, in the owning layer. A consumer states only instance obligations and endpoints (a theorem applied); it never restates a law for its own object or proves a statement about one concrete algorithm.
---

# State over structures

A statement is about every value of a structure, with contracts and assumptions as hypotheses;
a consumer shows its object is such a value (instance obligations) and reads off the theorem
(endpoints). This applies `README.md` rules 1–3 and `instantiate` fields 1, 2 and acceptance.

## Classify every new statement first

0. **Answer `README.md` "Before writing anything" first.** Every statement is one line of a
   written chain (rule 12), or the endpoint that composes the chain. Name its line. A hop
   is stated as a relation between `K • X` and `K • X'` for the one component `X` it
   replaces, at that component's layer, and then lifted by congruence. Never state it about
   the whole experiment with a changed interface.

One row per statement in the step's record:

| Statement | Kind | Owner (module) | Over (structure) | Hypotheses (contracts, assumptions) |
| --- | --- | --- | --- | --- |

"Over" names the structure or type quantified over (`TypedSystem A`, `ResourceTheory`); the
particular object goes in the Statement column. Three kinds are allowed in sources:
- **Law.** Generic, over S, in S's owning layer, never in a consumer module; a class axiom
  (`advantage_self`) counts. Random-systems laws are stated over systems (`README.md` rule 1); a
  statement about a presentation's states is a presentation law, described as one. Before
  stating a law or object on automata, look for its systems-level form (built by attachment or
  sampling, the hypothesis a condition on transcripts); if it exists, it is the law and the
  automaton case an instance obligation. "A function of the transcript" names the interface read.
- **Instance obligation.** X meets one of S's contracts: an equality of two existing objects, a
  contract field, or a value. It mentions X, and its proof uses facts about X.
- **Endpoint.** T applied to the instance obligations; its statement is T's conclusion at X. A
  stock law applied at a definition's interface with its hypotheses discharged there (the
  guessing hop at a game, with "one final query" and the accept set discharged) is "endpoint
  (law applied)", not a specialization to forbid.

**Tests** (`Tests/`) are a fourth kind: a law or endpoint applied to a test object (negative
examples included), or at the owner's constructors with variable arguments. Name a result that
`#print axioms` cites, otherwise use `example`. A generic statement in a test module is
classified like a source statement (a law moves to its owner; a restatement is deleted or
instantiated at a test object). Glue that is a law of an owner the step does not extend is a
local `have`, recorded as an upstream candidate. Probe-local statements are exempt.

**Not statements.** A definition goes in the assembly table, and here only as "definition" when
later statements quantify over its type; a well-formedness field is "contract (field)"; a
Mathlib class instance on a carrier is "definition (instance)".

**Forbidden:** a lemma that is a law of S specialized to X, or a bound or reduction stated for
one scheme (e.g. a consumer's `…Law_map_snd` that is `ProbDist.map_map` plus its realization
contract). Use the law where it is needed: one application, or under binders a
`congrArg`/`funext` chain ending in it (`prove-from-laws` rule 4). A local `have` inside a proof
is allowed; a top-level declaration is not.

## Security definitions and assumptions

A pair of systems compared with an error (`PRG.Secure`, `KEM.INDCCA`, `CDH.Assumption`) is
always named in its owner, in the shape of the sibling of its kind (indistinguishability:
`INDCCA`; search: `CDH.Assumption`), outside the predicate order below; where the owner has a
system and converter style (`KEM.system`, `KEM.CCA`), its systems compose them. Its field-6
"operations" are what consumers do with it (substitution through a context, budget typings,
instantiation); its T is what they apply (`substitutesWithin_attach`, `cc_calc`).
- The **conversion law** to the source's own inequality (`Secure … → guessingProbability − 1/2 ≤
  ε`) is a law of the definition's owner, built with the definition when every later endpoint
  uses it. Apart from it, rule 3's paper-units corollary is for theorems, not definitions.
- **The admissible class** is a parameter, never hardwired into the worlds or the definition.
  When the natural systems-level predicate (`DecidesBy accept`) is larger than the source's
  adversaries, the instance's class is the source's adversaries (randomized ones included, if
  the source's are), contained in the predicate by a proved instance obligation; theorems keep
  the predicate as their hypothesis. Docs say plainly where a statement holds only for that class.

## Decidability

A statement or function that reads a decision (`Finset.filter`, `if`, a `Bool` function of a
`Prop` predicate such as `KI.outcome` reading `Sound` and `Fresh`) takes the decision as an
instance binder (`[DecidableEq β]`, `[DecidablePred p]`), per the policy in
`Probability/Distribution.lean`; a definition that uses the function passes the binders on.
Never seal the classical instance in a wrapper to keep "one form". A finite set that is an
object of its own (`mapFiber`) may fix the classical decision inside its definition, with a
membership lemma. A binder cannot quantify over
a variable the predicate ignores ("invalid parametric local instance"): state it without it.

## Predicates and specifications

Any other predicate or specification used in statements (a set such as
`{R | ∀ h, R.1 h ≠ 0 → P h}`) is placed in this order:
1. If an owner's law *consumes* it to conclude something else (as `ProbStep.Memoryless` gives
   memoryless systems), it is defined and named in that owner.
2. Otherwise, if it is short, it is written inline at each use; no alias only to avoid
   repetition, even when the property is generic.
3. Otherwise, a property of the consumer's protocol is instance data in the consumer.

A predicate with only its own closure laws and no consuming law stays unnamed (e.g. a
`Satisfies` predicate for trace contracts is declined on this ground).

## Auditing existing statements

When a step deletes or rewrites statements, one row per statement:

| Statement | Kind found | Action (delete / keep / defer to step N) | Use sites, including comments and `#print axioms` |
| --- | --- | --- | --- |

- Keep a generic law applied at X whose result names X's object (`exposed_hide` with the
  consumer's own system on the right): an endpoint. Delete it restated over a family of X's
  instances with an unnamed result. A test generic in a parameter but tied to one interface is a
  test. Instantiate a restatement at a test object when the module has one and the observation
  is otherwise untested; otherwise delete it.
- A deferred restatement whose planned replacement was declined is decided at its step by "Named
  law or T applied?". One found in a module the step may not edit (the consuming project during
  an upstream gate) is recorded in the plan for the step that owns that module.
- A forbidden statement that the plan defers stays until its step, with no new uses. If its proof
  breaks, re-prove it by the generic chain with its statement unchanged; if its type mentions a
  deleted object, make the minimal type substitution and say so.

## Rules

1. **Hypotheses are contracts and assumptions, never internals.** Contracts: correctness
   (`DiffieHellman.Correct`, `KEM.Correct`). Assumptions: a pair of systems with an error
   function (`CDH.Assumption`, `SignatureScheme.EUFCMA`, `KEM.INDCCA`, Gap-DH).
2. **No concrete algorithm in a law or a security theorem** (`README.md` rule 3: parameters in
   proofs, concrete algorithms as instances): only in an instance obligation or when an
   endpoint is instantiated.
3. **Security statements keep the existing shape:** `W₀ ≃[ε] W₁` per distinguisher, in
   two-world units (`|p₀ − p₁|`, each world's terms once per world), with a one-line corollary
   in the paper's units (for a bit-guessing game, `|g − ½|` by
   `advantage_eq_two_mul_abs_guessingProbability_sub_half`). A hop law (an exact relation between
   decision probabilities of two pairs of worlds, such as the guessing hop) is not a security
   statement: it keeps its owner precedent's form (`|·|` in `ℝ`); consumers convert in one line.
4. **Generalize, don't bend.** A statement that must change to fit an instance is generalized
   where it lives, with the same proof, and the change is stated.
5. **Probe the statement first** (`instantiate` field 4), components as variables and contracts
   as hypotheses, before proving anything. If it follows from structural laws alone, it is
   right. If it needs internals, a law is missing in the owner; the exception is a contract
   about a presentation by nature ("a failing step keeps the state"): probe for a behavioral
   reading, and if there is none (an opener that keeps a key on failure meets "a failing step
   keeps the state" yet leaks, since a failure is informative) it is a primitive component's
   instance obligation,
   stated on its step or program body. If a component's contract holds only on a sub-class of
   arguments (inside automata) while the composition law needs all, the missing law is the
   bridge onto that sub-class (a representation law in the owner), not the contract re-proved
   in a second presentation.
6. **Follow precedent for the shape.** Search for statements of the same shape, not just the same
   structure (`∃ P, presentation P = R`: `TypedSystem.exists_ofPDS`); follow form and naming.
   - Prefer the existential form of a representation law unless a consumer needs the witness by
     name: naming a derived object adds an object.
   - Inside an owner, the theorem combining its laws into the result consumers use is a law (a
     main result), not a restatement; only a consumer specializing a law is forbidden.
   - **Whose law is it?** A law combines its owner's laws or speaks about an object the owner
     defines (not only its structure's fields). Test: replace the structure by its fields; if the
     statement becomes a lower layer's law instantiated, it is a restatement, even in the owner's
     module (e.g. a `KEM.gen_encaps_jointLaw_map` is `ProbDist.jointLaw_map` instantiated).
     For a consumer's operation, unfold it: a generic law at one field is a restatement (delete);
     a statement needing the operation's own case split is an instance obligation (keep). A
     typed statement that uses only the `.1` projections of its arguments is the raw owner's law
     (conditional equivalence in transcript form belongs to `Game.MBO`, not `Typed`).
   - **Named law or T applied?** If every consumer would add the same glue to T (a mass rewrite,
     a sum argument), glue plus T is a law in T's owner. Count consumers the plan names *and*
     that fit when probed (named consumers often do not all fit); a later step's objects are checked
     against the source, probed at the presentation, and recorded as "source-checked".
   - **Minimal law or its generalization?** State the minimal law the probe-confirmed consumers
     need. A cost-free generalization with no consumer is an Idea with its trigger (upstream
     `AGENTS.md`: "generalization only when a concrete requirement … calls for it"); a repeat in
     scratch files counts only when a planned step consumes it. When the brief asks for a more
     general form than the named consumer uses (e.g. `DecidesBy` for a law supported on
     probes, to cover randomized adversaries), the brief is the requirement; keep the special
     case as a one-line corollary if a consumer cites it.
   - Keep the conclusion minimal (`ProbStep.mem_support_belief_of_invariant`: `∃ s, inv h s`);
     leave a composition hypothesis such as `∀ h s, inv h s → Q h` to the consumer. Add a
     typed or specialized corollary only when a consumer needs it, even if precedent has some.
7. **Check consumers against their sources.** Check each consumer's need against the text it
   formalizes, not the plan's summary (e.g. a plan may say "dual-PRF of the KDF" where the
   source uses a PRF in one key position). For an EXISTS step ("New: none"), probe each named
   consumer's need; the six fields are not a catalogue. A need that depends on a later step's
   design: record each shape with its trigger and build nothing. Reading the source itself
   (readings, errata, items outside its model) is `plan-the-work` question 6.
8. **Cite the source.** A statement cites the source line it formalizes (`AGENTS.md` "Sources")
   and names any deviation (e.g. forks of MBO games in place of the source's aborts,
   `README.md` rule 7). A generic upstream module cites the generic source (the notion's
   origin paper or a textbook, as its sibling) and never its
   applications; if only an application's paper states the definition precisely, cite it by
   number without naming the application. A main result with no generic source cites nothing
   and is described generically. Both are cleanup candidates. The bibliography keeps the paper's
   title as it is and names the notion's origin as the paper cites it ([OP01] for Gap-DH), "as
   cited in [n]" when the origin is not on disk; quote only from what is on disk. Check every
   quotation and page against the source itself (`pdftotext -f p -l p`, printed page), never a
   step record (records carry page slips); without the source's path, ask for it first. Keep
   the source's words, with ASCII quotes and apostrophes. A source line that two components serve
   is cited at both, each with its part. A public specification read online: record its URL,
   revision and date in the step record.

## Stop signs

| Sign | Move |
| --- | --- |
| A consumer module gains a lemma whose proof is one generic law plus a hypothesis | delete it; use the law where it is needed |
| A theorem below the top floor names the consuming project or a concrete primitive | restate it over the structure |
| A law's hypotheses are about a whole inside system (its transcript masses), so a consumer discharges them only through the wiring or other components | restate it over the component it is about; ask the supervisor before building (`README.md` rule 12) |
| A statement needs an object's internals (a state, a table, a transition) | make it T applied to equalities; find T, or put the missing law upstream. A primitive component's state-level contract is the exception (rule 5) |
| An endpoint is not T's conclusion at X | rewrite it as T applied |
