# Language reference corpus

This is the normative experimental non-regression corpus shared by `/verbose` and
`/informalization`. It contains complete mathematical passages rather than
isolated slogans. A passage is reviewed as one unit: its source form, semantic
record, and reader realization must work together.

S1 is an accepted experimental API contract. Its exact source, checked event
sequence, typed operand fingerprints, source licenses, routine-support roots,
and theorem signature are frozen by the switching acceptance test. The broader
systems/converters/games corpus remains a design gate rather than an accepted
public grammar.

## 1. Non-regression contract

For each accepted passage we freeze four distinct things:

1. the checked mathematical content and its typed operands;
2. the discourse structure, including names that later steps reference;
3. the canonical `/verbose` source form; and
4. constraints on acceptable `/informalization` prose.

The exact Verbose source is a controlled-language interface and may be tested
textually after approval. Each module maps its own checked input through the
shared ontology and grammar. Different proofs need not yield identical node
sequences or prose. When both modules recover the same validated claim or
derivation—meaning the same registered schema and canonical operands—they
assign it the same semantic identity. Occurrence context and presentation cues
may yield different realizations. An already accepted rendering may not
silently be replaced by a less informative one.

Changing an accepted passage requires a review that states:

- which semantic or linguistic defect requires the change;
- which earlier requirements remain preserved;
- the before-and-after complete passage; and
- the positive, negative, and whole-passage tests that prevent recurrence.

A compiling Lean file is necessary but not sufficient evidence of acceptance.

## 2. Named assertions

`Fact NAME:` is a discourse anchor around a mathematical assertion. It is not a
generic proposition language and it does not replace the assertion's ontology
rule.

```text
AssertionDestination ::= closeMain | localFact(NAME)

CheckedAssertion =
  rule identity
  + typed claim operands and entities
  + exact conclusion
  + checked evidence root whose proof has type definitionally equal to the
      exact conclusion
  + checked evidence graph below that root
  + preserved proof surface, when present
  + licensed clause plan

AssertionOccurrence =
  CheckedAssertion
  + AssertionDestination
```

The realized local binding exists if and only if the destination is
`localFact(NAME)`; it has exactly that name and the exact conclusion type.

The following two occurrences have the same mathematical identity:

```lean
The game G is conditionally equivalent to S by h
```

```lean
Fact conditionalLaw: The game G is conditionally equivalent to S by h
```

The second occurrence additionally introduces the Lean anchor
`conditionalLaw`. Its event remains a conditional-equivalence assertion; it
must not become an opaque `structuralNamedFact` event.

There is no canonical `Fact name : proposition` form. An unsupported claim uses
ordinary Lean `have`. A supported claim whose formula is clearer than prose
uses a registered formula assertion inside the same envelope:

```lean
Fact equalWeight: restrictedGame.weight = restrictedURP.weight by ...
```

The local anchor and the spelling of its evidence are excluded from the claim
fingerprint. The exact proof and evidence anchors receive separate identities.
A claim fingerprint is value-sensitive: it recursively follows registered
definition edges for named operands, while never globally unfolding arbitrary
cryptographic definitions.

## 3. Reference passage S1: URF-URP switching

### 3.1 Provenance and scope

S1 is a **CR18-fallback application fixture** corresponding to the switching
argument in Section 4.11.3. It licenses only this registered use of the
conditional-equivalence argument, the MBO-forgetting step, and the reduction to
non-adaptive winning. S1 alone does not admit new generic Random Systems
vocabulary or declaration rules; a generic form needs independent primary
attestation.

Jost supplies general Random Systems and game/equivalence structure but does
not state this finite URF–URP switching application. It therefore neither adds
a hypothesis nor replaces the application-scoped fallback license for S1.
Jost printed pp. 33–34 does, however, supply the ontology used in the MBO
declaration: an MBO is an additional output that changes from 0 to 1 but not
back, and an event is a named monotone condition. That ontology is recorded
separately from the switching argument.

The live Lean theorem proves the sharper finite-alphabet expression
`q(q-1)/(2|X|)`. CR18 displays the coarser `q^2/(2t)` form. The former is a
checked-library strengthening and must not be attributed to CR18.

`Theorem NAME "TITLE"`, the `Given`/`Conclusion`/`Proof`/`QED` block, and
`Fact NAME:` are project-controlled compositions. Their exact syntax and
punctuation are not attributed verbatim to Massot, Jost, or CR18.

The generic pattern “bind an exact mathematical object and give a separately
checked equivalent characterization” is attested by Liu–Maurer 2020,
Definition 6, pp. 9–10, where a converter is defined by conditional laws and
then equivalently characterized by their joint law. Our exact-term-plus-theorem
syntax is a project-controlled realization of that pattern, not a quotation.
Thus the characterized-MBO form has split provenance: Jost for the MBO/event
ontology, Liu–Maurer for the definition-plus-characterization discourse
pattern, and `projectControlled` for the exact Lean-facing sentence.

`LanguageDesign/Corpus.lean` is implementation metadata rather than an
independent linguistic authority. The obsolete `structuralNamedFact` license
is withdrawn; `Fact NAME:` retains the wrapped domain assertion's rule.
`structuralTheorem` licenses only the declaration layout, while each natural
binder profile remains separately typed and tested.

### 3.2 Mathematical record

The passage contains these foreground nodes, in this order:

1. the query-restricted URF;
2. the exact collision MBO and its checked same-answer characterization;
3. the game obtained by enhancing the URF with that assignment;
4. the query-restricted collision game and query-restricted URP;
5. conditional equivalence of the restricted game and restricted URP;
6. the system obtained by ignoring the game's MBO;
7. equality-guided reshaping of the advantage comparison;
8. the explicit advantage bound by the supremum of winning probabilities
   achievable by non-adaptive strategies;
9. the fixed-query-list collision argument; and
10. the real-valued birthday bound on that winning probability.

`conditionalLaw` and `forgettingIdentity` are proof anchors because later steps
use them. The final collision estimate is single-use and remains unlabelled.
Nonnegativity, equal weight, and the `ENNReal.ofReal` bridge remain in the
checked support graph. They may disappear from the foreground only through an
accepted bounded classifier.

The exact assignment is `Switching.collisionCondition`; prose does not
reconstruct or guess it. Its checked implementation tests non-injectivity of
`fun x => System.answer s [] x` on the queried finite set. Ordinary “output
collision” language is licensed only after the checked specialization to
`System.functionEvaluator f` supplied by
`Switching.collisionCondition_functionEvaluator_mem_iff`.

### 3.3 Proposed Verbose source

This is the accepted whole-passage regression fixture. The `calc` shell and
the game-specific `let` bindings remain Lean syntax where no independently
attested controlled declaration form has been accepted. The restricted PDS
bindings use the typed system constructor. `Theorem`/`Given`/`Conclusion`/
`Proof`/`QED`, `Fact`, the characterized-MBO declaration, and the mathematical
assertions are controlled forms.

The formula `forget(G)` lowers exactly to `PDG.forget G`, while `νᴺᴬ[G]`
lowers exactly to `ENNReal.ofReal (PDG.blindSupWinProb G)`. The implementation
keeps the final real-to-`ENNReal` lift explicit until a general, unambiguous
scalar grammar has been accepted; it does not claim a blocked-replies
realization for an arbitrary typed game.

The binder “a finite nonempty alphabet `X`” lowers to the exact formal bundle
`(X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]`. The reader sees the
mathematical object; the full instance telescope remains available in formal
detail and in the differential declaration test.

The second calculation step uses the accepted bounded Verbose proof-synthesis
registry for the two nonnegativity premises and equal weight. Each synthesized
proof is retained as a typed receipt and must occur below the checked assertion
root. Informalization's evidence classifiers remain separate: they decide
whether already checked premise evidence may be collapsed and never construct
missing Lean proofs.

```lean
Theorem urf_urp_switching "URF–URP switching"
  Given:
    a finite nonempty alphabet X
    Let q ∈ ℕ
  Conclusion:
    Adv⊥([q] URF(X), [q] URP(X)) ≤
      ENNReal.ofReal
        ((q : ℝ) * ((q : ℝ) - 1) / (2 * (Fintype.card X : ℝ)))
Proof:
  classical
  Let restrictedURF be the system [q] URF(X)
  Let collisionMBO be the MBO given by
    (Switching.collisionCondition (X := X)), which is set on a query history
    exactly when two distinct queries in that history receive the same answer,
    as shown by
    (Switching.collisionCondition_functionEvaluator_mem_iff (X := X))
  let collisionGame : PDG X X := (PDS.adjoin URF(X) collisionMBO).1
  let restrictedCollisionGame := Switching.limitGame q collisionGame
  Let restrictedURP be the system [q] URP(X)

  Fact conditionalLaw: The game restrictedCollisionGame is conditionally
    equivalent to restrictedURP by
    Switching.limit_urf_collision_condEquiv_limit_urp X q

  Fact forgettingIdentity: Ignoring the MBO of restrictedCollisionGame yields
    restrictedURF by
    Switching.forget_limitGame_adjoin q URF(X) collisionMBO

  calc
    Adv⊥(restrictedURF, restrictedURP) =
        Adv⊥(forget(restrictedCollisionGame), restrictedURP) := by
      Replacing forget(restrictedCollisionGame) by restrictedURF using
        forgettingIdentity yields Adv⊥(restrictedURF, restrictedURP)
    _ ≤ νᴺᴬ[restrictedCollisionGame] := by
      The conditional equivalence in conditionalLaw gives
        Adv⊥(forget(restrictedCollisionGame), restrictedURP) ≤
          νᴺᴬ[restrictedCollisionGame]
    _ ≤ ENNReal.ofReal
        ((q : ℝ) * ((q : ℝ) - 1) / (2 * (Fintype.card X : ℝ))) := by
      The supremum of the winning probabilities achievable by non-adaptive
        strategies against restrictedCollisionGame is at most
        (ENNReal.ofReal
          ((q : ℝ) * ((q : ℝ) - 1) /
            (2 * (Fintype.card X : ℝ)))) by
          (Switching.blindSupWinProb_limit_urf_collision_le X q)
QED
```

The checked proof of
`Switching.blindSupWinProb_limit_urf_collision_le` has the required subordinate
fixture S1a in Section 3.6. That expansion is never classified as routine. It
may be collapsed at the theorem-application site, but must remain linked and
inspectable.

### 3.4 Reference informalization

The following is a paragraph-level reference realization, not required output
text. Other realizations are accepted when they preserve the same checked
discourse relations, mathematical register, and substantive expansion.

> For a finite nonempty alphabet \(X\) and a query budget \(q\), let
> \(\widehat R_q\) be the \(q\)-query game obtained by adjoining to the uniform
> random function the MBO that signals when two distinct queries receive the
> same answer. This game is conditionally equivalent to
> \([q]\operatorname{URP}(X)\), and the system obtained from the game by
> ignoring its MBO is \([q]\operatorname{URF}(X)\). Conditional equivalence
> therefore bounds the fully defined distinguishing advantage by the supremum
> of the winning probabilities achievable by non-adaptive strategies. Such a
> strategy fixes a list of at most \(q\) queries. Repeated inputs cannot witness
> a collision between distinct inputs. Counting the uniform functions that are
> injective on the remaining finite set and applying the birthday estimate
> bounds the collision probability by
> \(q(q-1)/(2|X|)\). Hence
> \[
> \operatorname{Adv}_{\bot}([q]\operatorname{URF}(X),
>   [q]\operatorname{URP}(X)) \leq \frac{q(q-1)}{2|X|}.
> \]

The collapsed view must communicate all substantive transitions in this
paragraph. Nonnegativity, equal-weight bookkeeping, and scalar packaging may be
collapsed after evidence coverage is complete; their expansion remains
available.

The following are forbidden:

- `PDG.CondEquiv G S from h` as reader prose or canonical Verbose source;
- “monitoring the system for collisions”;
- “by construction; call this fact ...”;
- expanding `[q] URF(X)` or `[q] URP(X)` into invented English;
- describing `Adv⊥` as a generic distance `Δ`;
- mentioning a paper name or number as part of generic vocabulary;
- calling the supremum an attained optimum without a witness; and
- translating `rw`, `simp`, `grind`, or another tactic name into prose.

### 3.5 Foreground semantic event sequence

These are proposed semantic roles, not current implementation identifiers. A
role marked `S1` remains local to this fixture; one fallback passage cannot
license it generically. A definition role marked pending cannot be implemented
until the breadth corpus independently attests the generic schema.

```text
structuralTheorem                 -> theorem root
rsDeclareRestrictedURF [pending cross-corpus attestation]
                                   -> addLocalEntity(restrictedURF)
defineCharacterizedEntity [project syntax + Jost MBO ontology + LiuMau20 Definition 6]
                                   -> addLocalEntity(collisionMBO)
  support: exact assignment + function-evaluator characterization
rsDeclareEnhancedGame [pending cross-corpus attestation]
                                   -> addLocalEntity(collisionGame)
rsDeclareRestrictedGame [pending cross-corpus attestation]
                                   -> addLocalEntity(restrictedCollisionGame)
rsDeclareRestrictedURP [pending cross-corpus attestation]
                                   -> addLocalEntity(restrictedURP)
rsConditionalLaw [checked library; S1 occurrence]
                                   -> localFact(conditionalLaw)
rsForgetGame [checked library; S1 occurrence] -> localFact(forgettingIdentity)
proofRewriting                    -> calculation equality, consumes forgettingIdentity
rsConditionalBlindComparison [checked library; S1 occurrence]
                                   -> close calculation rung, consumes conditionalLaw
rsBlindWinningBound [checked library; S1 occurrence] -> closeMain
  evidence: Switching.blindSupWinProb_limit_urf_collision_le
```

The support graph, although absent from this foreground list, contains the
exact nonnegativity and equal-weight premises, the `proofScalarClosure` node
that lifts the final real inequality, and the fixed-list/birthday expansion
below `rsBlindWinningBound`. The typed formula layer records the other
real-to-`ENNReal` insertion without inventing a proof step. Claim fingerprints
are computed from the claim schema and typed operands; evidence identities
separately record theorem applications and proof roles.

The displayed quantity `νᴺᴬ[G]` is the exact canonical
`blindSupWinProb G` quantity. The separate blocked-replies theorem
`PDG.supWinProb_blockRepliesGame` applies on the universal carrier and is not
silently asserted by this generic typed-game notation.

`rsConditionalBlindComparison` retains restricted URP as a claim operand. It
is a closing inference distinct from the existing transitive
`rsConditionalBlindBound` reduction that replaces a goal by a later arbitrary
bound; one RuleId may not carry both effects. There is no nested or replacement
`structuralNamedFact` event. Removing an anchor changes occurrence/binding
metadata, not the canonical mathematical claim.
Changing the game, underlying URF, MBO assignment, restriction budget, ideal
law, or bound changes the claim fingerprint. This is implemented through
alpha-stable canonical entity and definition fingerprints, not local names,
free-variable identities, proof declarations, or unbounded delta reduction.

### 3.6 Subordinate fixture S1a: blind winning to birthday bound

The expansion below the final theorem application has these explicit semantic
nodes, in this order:

```text
rsBlindUniversal [S1, CR18-fallback + checked library]
  -> fix an arbitrary total environment e, its non-adaptivity proof, and horizon n
rsDefineReferenceQueryList [S1, checked library]
  -> define L from e, n, q, and one reference function evaluator
rsNonadaptiveScheduleIdentity [S1, CR18-fallback + checked library]
  -> prove that, for every sampled function f, the exact answered-query
     schedule against the filtered function evaluator for f is L
rsRestrictedQueryCount [S1, checked library]
  -> establish L.length ≤ q
rsWinningMassCollisionIdentity [S1, checked library]
  -> identify winningMass e n with the uniform-function mass of
     non-injectivity on L.toFinset
rsUniformFunctionInjectiveMass [S1, checked library]
  -> compute the mass of functions injective on L.toFinset as
     |X|^{\underline{k}}/|X|^k, where k = |L.toFinset|
rsCollisionMassComplement [S1, checked library]
  -> compute the collision mass as 1 - |X|^{\underline{k}}/|X|^k
rsBirthdayEstimate [S1, CR18-fallback + checked library]
  -> bound that collision mass by k(k-1)/(2|X|)
proofArithmeticClosure
  -> use |L.toFinset| ≤ L.length ≤ q to reach q(q-1)/(2|X|)
```

The reader realization says that non-adaptivity fixes the list, query
restriction bounds its length, repeated inputs are removed by passing to the
set of queries appearing in the list, and the uniform-function collision lemma
counts the functions that are injective on that set before applying the
birthday estimate. Only the final monotone arithmetic comparison may be
classified routine. Defining the list, proving its schedule equality,
identifying the collision experiment, and applying the birthday estimate are
substantive and remain independently expandable.

S1a is an informalization expansion recovered from the checked body of the
named helper; it is not a second Verbose source fixture. The compact Verbose
proof cites that helper, while `/informalization` must realize its expansion as
connected prose. The reference realization is:

> Fix a non-adaptive environment \(E\) and a horizon \(n\). Non-adaptivity makes
> the resulting query list \(L\) independent of the sampled function, while
> query restriction gives \(|L|\le q\). Winning the collision game is exactly
> the event that the sampled uniform function is non-injective on the distinct
> inputs appearing in \(L\). Counting the uniform functions that are injective
> on this finite set and applying the birthday estimate bounds this event by
> \[
> \frac{|L_{\mathrm{set}}|(|L_{\mathrm{set}}|-1)}{2|X|}.
> \]
> Since \(|L_{\mathrm{set}}|\le |L|\le q\), this is at most
> \(q(q-1)/(2|X|)\).

## 4. Acceptance gates

The `Fact NAME:` envelope and S1 proof shape were selected for the experimental
implementation on 2026-08-28. This accepts the whole-proof regression fixture,
not the pending system/game declaration frames and not the production breadth
gate in Section 5.

### 4.1 Decisions fixed for the experimental slice

The whole passage is treated as one regression unit, including:

- the natural theorem binder and scalar-formula conventions;
- the exact-term-plus-characterization form of the collision MBO declaration;
- the wording and direction of the equality-guided calculation step;
- the separate advantage-to-winning rung;
- the reference informalization as a paragraph-level naturalness baseline;
  and
- the S1a expansion as the required non-routine probabilistic subargument.

### 4.2 Tests blocking implementation acceptance

Positive tests must establish that:

- a bare domain assertion closes the matching goal;
- `Fact NAME:` followed by the same assertion preserves the outer goal and
  introduces exactly one local fact of the assertion's exact conclusion;
- both occurrences retain the same rule identity, operands, and claim
  fingerprint;
- rendering and parsing preserve the anchor and assertion separately;
- theorem-header and scalar notation lower to the exact live theorem;
- `νᴺᴬ[G]` lowers to the exact canonical blind-winning quantity;
- the collision MBO declaration retains the exact Lean object and the checked
  function-evaluator characterization;
- the bounded Verbose proof-synthesis registry constructs exactly the two
  nonnegativity and one equal-weight proofs required by the
  conditional-equivalence comparison;
- the independent informalization classifiers recognize and collapse exactly
  those already checked premise proofs without being able to synthesize them;
  and
- the foreground and support events match Sections 3.5 and 3.6.

Negative tests must reject:

- wrapping a reduction, introduction, announcement, arbitrary tactic block,
  or multi-goal rule in `Fact NAME:`;
- an unrelated proof or wrong game/system operands;
- a duplicate, illegal, or self-referential anchor;
- unresolved metavariables or inferred mathematical choices;
- a characterized-definition parser branch tied to
  `Switching.collisionCondition` or another theorem-specific name;
- an unproved scalar coercion or an unmatched collision characterization;
- any failure that leaves goals, locals, or semantic events behind; and
- the obsolete `Fact name : proposition` syntax in the canonical scope.

The implementation suite must also compare `rw`/`simpa`/`calc`, inline/named
helpers, reordered independent premises, and routine automation/explicit
routine derivations at the recovered semantic level. The whole S1 passage is a
mandatory review and regression fixture; unit tests for individual macros
cannot substitute for it.

## 5. Breadth gate before production implementation

S1 tests the named-assertion composition defect; it does not by itself validate
the language as a whole. Production implementation remains frozen until the
corpus also contains accepted complete passages covering:

1. an abstract system and an operational system definition;
2. converter definition, serial composition, and attachment at a named
   interface;
3. a game/event definition followed by a probability or mass argument;
4. an MR16-track AC construction proof with a simulator or context step; and
5. one proof that moves from construction language into concrete Random
   Systems reasoning and then returns to the construction conclusion.

Each passage must exercise definition, theorem-statement, proof-step, and
later-reference contexts. Its source locator must respect the repository source
hierarchy: MauRen16 first, then Jost, LiuMau20, and Lanzenberger; CR18 may be
used only for an entry in the fallback register. CBC becomes a further
application passage only after its public semantic seams exist.

These passages instantiate the comprehensive ontology and context matrices in
[`LANGUAGE_DESIGN.md`](LANGUAGE_DESIGN.md). They are not separate ad hoc
grammars. No individual example, including Switching, may add a generic rule
without evidence that the rule works across the relevant accepted passages.
