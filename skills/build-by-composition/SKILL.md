---
name: build-by-composition
description: Part of the CC skills (`skills/README.md`); fires after `plan-the-work` and `instantiate` (or an accepted design), at the moment a definition is written. Use before writing or changing any Lean definition in the constructive-cryptography library or a project built on it (def, abbrev, structure, class, instance, system, converter, game, protocol, automaton, DSL program), and whenever a plan or task says "define", "build", "add" or "implement". The object is the source's decomposition, written as an assembly of existing building blocks joined by the library's operations, or as a value of an existing structure. Nothing is built standalone by hand. A missing block is built first, generically, in its owning layer.
---

# Build by composition

Every object is a **value of an existing structure** or an **expression in existing blocks**
joined by the library's operations. This skill applies `README.md` rules 1 and 3–6, `instantiate`
fields 3–6 and `AGENTS.md` "Modeling workflow" 1–5 at the moment a definition is written.

## Before the first definition

0. **Answer `README.md` "Before writing anything" first.** Write the definition as an
   operator sketch (`C • (‖ s, X_s) • wire • (Y ∥ R)`) before any Lean. For a proof object (an
   MBO game, a game variant, a reduction), the sketch shows which one component it replaces and
   that the outer interface is unchanged (rule 12).

1. The step's six-field record exists in the project's step records (`instantiate`; for a
   handed-over or resumed step, "Resuming an accepted record"), or the step builds a design the
   plan accepted (`plan-the-work`, "Gate or build").
2. Exempt: definitions local to a probe or a `Tests/` module (test objects, a refuted candidate).
   A `Prop`-valued predicate added to a source is an object: rule 3 applies, and
   `state-over-structures` decides its place. A step of laws plus predicates has table rows only
   for the predicates; a predicate's "operation" is how it is formed from the owner's objects (a
   quantifier over a law's support, an equality on a transcript set). A step that adds only laws
   writes "No definition"; rule 2 applies to laws as well as objects.
3. After a deletion, remove each import or `open` it leaves unused. If the deleted declaration
   was a convention's entry point, point `REUSE.md` and the module doc at the laws replacing it.
4. Add the **assembly table** to the record, one row per component:

   | Component | Existing block (declaration, module) | Operation joining it | Owner of anything new |
   | --- | --- | --- | --- |

   The operations: attachment `•`, serial `≫`, parallel `∥` / tensor; sampling (`smul_sample`,
   `keyed`); routing (`routingAt`, `rename`) and projections (`leftProjection`); `ofProgram`;
   `ProbDist.map`, `jointLaw`, `pi`; specifications and constructions (sets of systems,
   `Specification.Constructs` as `Set.MapsTo`, `Set.image2` for products); presentations with
   their correspondence and representation laws (`ofConditional`, `ofProbAutomaton`, `ofPDS`,
   `ofFunction`, `ofProgram`; `exists_ofPDS`, `exists_ofProbAutomaton`,
   `eq_ofConditional_of_snoc`). Before building a law, a step or a reply distribution, check
   whether a presentation gives it (`conditional` is the normalized next-reply law). A structure
   of data has no joining operation: write "field". A row with no existing block names the owner
   of the new block, which gets its own record and is built first.
5. The definition is the assembly expression from the table, and nothing else.

## Rules

**Model first, with no proof in mind.** While a model is written, read no proof law and plan no
hop. A step that writes a model contains no proof material. The model is reviewed against
the source on its own. Whatever form a later proof needs is reached inside that proof by
bridging lines (`README.md` rule 12), never by anticipating it in the model.

**The definition follows the source, never the proof.** Write each block in the DSL as the
source describes it, and compose the blocks with `•`, `∥` and `‖`. Never shape a definition
(a hand-written `ofProgram`, an inlined sub-body, a reordered draw) so that it matches the form
some law consumes. If the composed definition does not have the form a law needs, the gap is
a missing law (a compile equation, associativity, a context law at the component). Build that
law. If the DSL cannot express a block, ask before writing it by hand, and name the missing
construct.

0. **The source's decomposition** (`README.md` rule 4). A reader who knows only the source
   matches every factor of the top-level definition to a part of the source's figure. A single
   block that implements several named objects of the source is a stop sign, whatever its laws.
1. **Parameters, never concrete algorithms** (`README.md` rule 3: parameters in proofs,
   concrete algorithms as instances). An algebraic object over an abstract structure
   (power DH in `(G, g, q)`) is a structure-level parameter; a concrete algorithm is a specific
   group or implementation (X25519), a separate value of the same structure, plugged in last. A
   protocol, game or converter takes its primitives as values of their scheme structures
   (`SignatureScheme`, `KEM`, a NIKE with `DiffieHellman.Correct`, `interface AEAD N AD M T`, a
   KDF function). A function that a later step replaces by a system (a KDF as a random oracle or
   PRF) is not a function parameter: the algorithm reaches it through an oracle port, as an
   invocation body (the codomain of `Program`), and the function-argument form is derived. A
   scheme structure carries a proof field only for well-formedness needed to build its
   systems-level object (a call bound; precedent `BlockCipher.decrypt_encrypt`); correctness and
   security stay separate predicates, as in the siblings.
2. **Generic first, owner first.** A missing block is a generic object of its owning layer,
   stated over the structure above. Import order is strict: `Probability → RandomSystems →
   ConstructiveCryptography → Commons`; a systems-level law uses the notion beneath a class
   (`Set.MapsTo` for `Constructs`) and connects at the instance (`README.md` rule 1). A block goes
   in the lowest module that owns its meaning (upstream `AGENTS.md`). If a needed block
   (`Commons.Evaluation`) lies above the intended owner, raise the owner to the lowest module
   holding the blocks (`Commons` holds scheme-level systems, as `KEM.system`); if a named block
   lies above its user, write its expression inline with a comment naming it. Either way, moving
   the block down is an upstream candidate (with a rename table). The consuming project (the
   top floor) holds only values of upstream structures, instance data and endpoints.
3. **Use the existing convention, with no wrapper.** Use the shape upstream already gives a
   notion (a coin realization is unbundled: `(G, g)` with `G.map g = P`, as in
   `KEM.LeakRBindSS`). Add no structure, record or alias that only repackages it (`README.md` rule 1: no intermediate
   duplicates).
   An example in a rule names a precedent, not a proof for the case at hand: still probe it.
   - **Stock block before a hand-written component.** If a stock block (`routingAt`, `rename`, a
     projection) expresses a converter, use it (its laws come free); write the siblings' DSL style
     only when the stock block needs glue (lemmas beyond its own laws; a parameter such as a
     reply map is data), and record the alternative.
   - **Restricted domains.** `Interface.restrict` at two reply types gives interfaces that are
     not defeq: restrict once, at the richest reply type; get the others by `withReplies`.
   - **Budgets.** Follow the sibling's per-port or scalar typing. If the DSL cannot type a
     component per port (a procedure calling several inside ports), use the scalar budget and
     record why. A budget is never a reason to merge blocks: a layer that multiplies the inside
     allowance is accepted, and the allowance is a parameter.
   - **Naming a reused assembly.** Name it neutrally (`KEM.system`) when it is a resource used by
     more than the definition that builds it (`AGENTS.md`); otherwise follow the sibling
     (`PRG.Secure` inlines its real system). When a consumer must name a type its owner writes
     inline, add the abbreviation in the owner and use it there too (`Protocol.PartiesOracles`):
     that names the owner's object and is not a repackaging alias.
   - **A main declaration that turns out to be an instance of a new local block** stays: the
     truth set is upstream `main` plus local layers on top that keep it intact, and nothing is
     pushed. The correspondence is a test (`rfl` or `Iff.rfl`); rebodying it is an upstream
     candidate.
4. **Automata only for primitive components.** A primitive component is a block whose retained
   state is not a function of its transcript (a protocol's session state). Having state does not
   make a component primitive (`KEM.CCA`'s decapsulated table is a function of the transcript).
   State that is a fold of the transcript (flags, a tested session, counters) is computed from
   the transcript by a generic block, not kept by a hand-written converter. A new primitive
   needs a recorded argument that it cannot be split into the source's named objects. A
   composite's behavior follows from its parts' laws: never write a `transition`,
   `sessionTransition` or `ProbStep` as its definition. Computing a composite's automaton in a
   proof needs `prove-from-laws`, "Opening a composite"; presenting an arbitrary system as an
   automaton by a generic representation law is not computing one.
5. **One presentation.** An object with two presentations (a DSL program and a hand-written
   automaton) keeps one; the other is one correspondence lemma.
6. **State lives in its owner.** Retained state and shared draws sit in the component that owns
   them, not in the assembly around it. A draw that two components read sits in one `sample`
   node directly around them (precedent `Keyed.exposed`).

## Names, notation, comments, layout

These are the details of `README.md` rules 5 and 6.
- **The algebra is visible.** A composite is written in operator notation (`≫`, `⊗`, `𝟙`, `•`,
  `∥`, `⨂`), never as nested `TypedConverter.comp` / `parallel` / `id` applications, so its
  definition reads as its operator equation. A scheme is one value of a structure (carriers,
  algorithms, instances as fields), so every definition takes that one argument; no statement
  threads a list of carriers. Interfaces and budgets are not spelled out where the operands
  determine them. Where the library cannot yet express one of these, write the plainest form and
  list the gap as an upstream candidate.
- **Readable names.** Definitions get words (`session`, `parties`, `context`, `Challenger`), never
  single letters (`π`, `P`, `W`, `C`); a paper symbol appears only as notation that elaborates to
  such a named definition. Variables follow the source where it names them (`KE`, `b`, `RO`) and
  are otherwise readable words.
- **Names.** A public name is the source's term (a BR game: `Send`, `Test`, `CorruptLTKey`, session
  `π_U^i`, `fresh`, `sound`, the experiment `G^KI`) or the library's term for a library notion
  (`restrict`, `sample`, `parallelAll`): a reader of the source recognises the object from its
  name alone. An invented name needs a reason in the record.
- **Notation.** One scoped notation module per owner (precedents: `ConstructiveCryptography/
  Notation`, `Probability/Distribution`'s PMF notation). Each notation elaborates to a named
  definition, uses the source's (or library's) symbol, carries a one-line quote of the source,
  and goals pretty-print in it; port queries use the DSL call syntax (`Send(U, i, m)`). Beneath
  it, systems-level and `Commons` definitions use the sibling's systems names
  (`Interface.tensor`, `TypedSystem.parallel`); CC notation goes in consumer statements where
  elaboration needs it. No `∀` or dependent arrow on a notation's right-hand side (precheck). No
  local notation in an instance binder: in a `variable` block it gives a silent `sorry`.
- **Two `HSMul` instances for one attachment** (the CC hom instance, the typed converter one): no
  `erw` in sources; add one `rfl` bridge lemma in the owner of the hom instance and `rw` with
  it; do not restate the typed laws at the other instance.
- **DSL.** Components with behaviour are written in the DSL (`converter`, `system`) when it can
  express them; a missing feature is added generically, as an upstream candidate. A protocol
  algorithm that calls an oracle is a converter, composed, never inlined into its caller. A term
  of a DSL line (an `inside` port's type, a `return`) continues on the next line only inside
  brackets, else the parser ends the declaration ("A system must declare at least one
  procedure").
- **Typing over an `interface`.** A program or reply function is typed with the generated
  families (`I.Port`, `I.Input …`, `I.Output …`), with no alias for the applied interface and no
  budget-0 projection `(I … 0).X`.
- **Mathlib class instances** (`Fintype (SessionView …)`): `deriving` first; if the handler fails
  (enum proof, instance size limit), by hand (an explicit finset for an enum, `Fintype.ofEquiv`
  along a tuple equivalence for a structure), never by setting options.
- **Layout.** A definitions module states the model in reading order with short docs, the full
  shape in one place; laws, invariants, correspondence lemmas and helpers go in the owner's
  separate laws module.
- **Comments** (upstream `AGENTS.md` "Documentation policy"). Module intro: purpose, objects,
  main results by name, role in the proof chain, one diagram; at most 25 lines plus the diagram;
  no chapters of readings, deviations or checks, line tables, caveat lists or design discussion.
  A reading or deviation is one sentence with its quotation and page, at its declaration.
  Parameters are explained beside their binders. A docstring is the defining equation plus one
  quoted line of the source. Test modules: one line per test object.

## Stop signs

| Sign | Move |
| --- | --- |
| A hand-written state machine for something that has parts | write the assembly of the parts |
| A definition written by hand, or reshaped, so that it fits a law's form ("so that line 1's law applies") | write it in the DSL as the source says; build the missing law, or ask |
| A new `structure` repackages an existing structure, or a contract already written as a hypothesis | use the existing structure or the unbundled convention |
| A concrete primitive (X25519, XEdDSA, AES, HKDF, SHA) outside an instance module | make it a parameter |
| A consumer renames a generic expression and proves laws about the new name | use the generic expression; at most a source-cited name, with no restating lemmas |
| "Build it standalone now, connect it later" | stop; find the block, or build it generically first |
| An isDefEq timeout or a large `unfold` while defining | the object is not an assembly yet; rewrite it |
| One converter answers several oracles of the source, or keeps flags or a tested session as state | split into the source's objects; compute transcript-determined state from the transcript |
| A public name the source and the library do not use | the source's term (`README.md` rule 5) |
| A module intro with chapters ("What is checked", "Deviations", "Readings"), line tables or caveat lists | apply "Comments" above |

## Done when

- The top-level definition reads as the source's figure with its names, and is the assembly
  expression; every new block lives in its owner with its own record; the inheritance table is
  complete (`instantiate` field 6).
- The owner's housekeeping is done: the import in the library index (`Commons.lean`, …), a
  `REUSE.md` row, README entries where the owner lists main declarations, the test module in the
  test index, and `#print axioms` lines in the axioms audit for definitions and main results,
  following the owner's precedent and placed beside that owner's lines (otherwise in the probe).
  - A structure of data and its values get no audit line when the owner lists none (`KEM`,
    `SignatureScheme`); the test prints a value's axioms. A law in a module whose audit file
    lists no sibling law gets none either: the result that uses it covers it, else the step's
    test module (not a scratch file) prints its axioms.
  - A module built over several sub-steps: its index lines (library, test) go with the first, so
    that `lake build --wfail Tests` builds it; the `REUSE.md` row, README entries and audit lines
    with the last. An owner README with no entry for the module gets none.
  - A record naming a target that does not exist ("a row beside X"): place it by the nearest
    entry and correct the record. A named owner module that does not exist: create it in the
    lowest layer that owns the meaning, with a module doc, and add it to the layer's index.
  - **Line anchors.** After inserting into a module, grep every `*.md` outside `.lake` (other
    layers' per-directory READMEs too) for `<file>#L` anchors into it. Compute the shifts from
    `git diff -U0` of the edited file (by hand for an untracked file). When the checkout already
    holds uncommitted work, save `git diff -U0` of each file before the first edit and compute
    the shifts from the two diffs. Apply them once, check that each anchor lands on the same
    line text as before, then add the new declarations' anchors. An anchor already off its
    declaration before the step is shifted, not repaired; say so under "Not verified".
