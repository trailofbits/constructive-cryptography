# PDF validation contract

This file records the source-level values that the semantic switching example
must preserve.  It is a validation ledger, not a prose template: the backend
must recover these objects and relations from checked Lean expressions and
registered rule schemas.

## Sources inspected

- CR18, printed pp. 109--111 (PDF pages 61--62): Definition 4.20,
  Theorem 4.17, and Lemma 4.19.
- CR18, printed pp. 126--127 (PDF pages 69--70): the CBC conditional-
  equivalence proof, used to check that the schema is not switching-specific.
- Miller, ICERM slides 19--23 and 42--52: proof-state checkpoints,
  hierarchical proof expansion, the theorem-explainer architecture, entity
  construction, proposition explanation, and LeanTeX.

The cited pages were rendered to images and inspected visually.  Extracted
text was used only to locate them.

## Canonical switching values

Let

\[
R=\mathsf{URF}_{X,X},\qquad P=\mathsf{URP}_X,
\]

let \(A\) be the output-collision monotone condition, and let
\(\widehat R=\operatorname{adjoin}(R,A)\).  Query restriction is written
\([q]S\), never \(\theta_q S\).  The latter symbol is reserved in CR18 for
the CBC total-block restriction \(\theta_r\).

The checked argument must expose the following claims as typed values:

1. \(([q]\widehat R)^-=[q]R\).
2. \(\widehat R\mid\!\equiv P\).
3. \([q]\widehat R\mid\!\equiv[q]P\), obtained by restriction preservation
   from claim 2 and its total-answer obligations.
4. \(\operatorname{Adv}_{\bot}(([q]\widehat R)^-,[q]P)\leq\Gamma(b[q]\widehat R)\), obtained
   from claim 3 together with nonnegativity and equal-weight obligations.
5. For every non-adaptive environment and horizon, its winning mass is at
   most \(q(q-1)/(2|X|)\).
6. Taking the supremum gives
   \(\Gamma(b[q]\widehat R)\leq q(q-1)/(2|X|)\).
7. Rewriting by claim 1 and combining claims 4 and 6 gives
   \(\operatorname{Adv}_{\bot}([q]R,[q]P)\leq q(q-1)/(2|X|)\).

The order of quantification in claims 5--6 is essential.  For one fixed query
schedule \(L\), put \(S_L\) for its set of distinct inputs and
\(k_L=|S_L|\).  Its collision probability can be bounded by
\(k_L(k_L-1)/(2|X|)\), but the supremum \(\Gamma\) cannot be bounded by the
probability of an arbitrary particular schedule.  A repeated-query schedule
with \(k_L=1\) makes that erroneous right-hand side zero.

## Deliberate difference from CR18

CR18 Lemma 4.19 prints the coarser value

\[
\frac{q^2}{2|X|}
\]

(specialized there to \(|X|=2^n\)).  The internal theorem proves the sharper

\[
\frac{q(q-1)}{2|X|}.
\]

The generated statement and final line must show the checked sharper value.
Documentation may state that it implies the printed CR18 bound; the backend
must not silently replace one value by the other.

## Generic conditional-equivalence schema

The switching and CBC proofs share this rule shape:

```text
base source S + monotone condition A
  -> game G obtained by enhancing S with the MBO defined by A
  -> conditional equivalence G |equiv T
  -> optional converter/restriction preservation
  -> advantage of forget(G) versus T bounded by blind winning of G
  -> a uniform non-adaptive winning bound
  -> the original distinguishing-advantage bound
```

The canonical representation must therefore keep separate fields for the
source system, target system, MBO-enhanced game, condition, converter or
restriction, conclusion, and proof obligations.  A declaration adapter may
fill this schema; it may not supply a complete English paragraph.

## Implemented declaration schemas

The Random Systems adapter currently decodes the relevant declarations into
the following canonical applications.  “Operands” are non-proof arguments;
“obligations” are separately retained proof arguments.

| Mathematical rule | Canonical operands | Canonical obligations |
| --- | --- | --- |
| preserve conditional equivalence under query restriction | `queryBudget`, `game`, `target` | `sourceTotal`, `targetTotal`, `conditionalEquivalence` |
| conditional equivalence to blind winning | `game`, `target` | `sourceNonnegative`, `targetNonnegative`, `equalWeight`, `conditionalEquivalence` |
| fixed-set collision bound | `alphabet`, `queriedSet` | none |
| birthday bound | `sampleSpaceCardinality`, `sampleSize` | size admissibility, positivity |
| blind supremum from pointwise non-adaptive bounds | `game`, `pointwiseBound` | the uniform pointwise proof |

An MBO-enhanced game is not a label: it is the nested canonical value
`enhanceWithMBO(sourceSystem, condition)`, optionally beneath
`queryRestriction(queryBudget, ...)`.  Thus the conditional-equivalence claim
contains both systems and, through its game operand, the source system and
monotone condition used to build the game.

The generated fixed-schedule expansion now keeps the quantifiers in the PDF
order:

1. fix a non-adaptive schedule and its distinct queried set \(S\);
2. put \(k=|S|\leq q\);
3. bound its collision probability by \(k(k-1)/(2|X|)\);
4. take the supremum only after the bound is uniform; and
5. conclude the sharp \(q(q-1)/(2|X|)\) advantage bound.

## Miller presentation gates

- The theorem statement aggregates implementation binders into mathematical
  entities (for example, a finite nonempty alphabet and a query budget in
  \(\mathbb N\)).
- The collapsed proof is a normal symbolic proof, not a list of backend move
  labels.
- Expanding a claim reveals mathematical subclaims or equations attached to
  that claim.
- Proof-depth controls and proof-state checkpoints remain distinct.
- The proof-state panel shows a humanized context above a rule and the current
  goal below it.
- No reader surface contains kernel expressions, generated identifiers,
  declaration paths, evidence IDs, or a section called “Formal evidence.”

## Acceptance checks

1. Canonical claims and derivations are serialized separately from prose.
2. Renaming local hypotheses or changing tactic spelling does not change the
   canonical proof graph.
3. Changing an operand, budget variable, alphabet, or checked bound changes
   the rendered formula without editing a sentence template.
4. The switching renderer contains no theorem-shaped predicate or complete
   switching-proof string table.
5. Every displayed implication is either the exact checked conclusion or
   lists the material obligations suppressed from its collapsed reading.
6. The generated page contains `[q]`, not `theta`, and contains the sharper
   checked final bound.
7. Expand-all contains no `RandomSystems.*`, `_uniq`, `_hyg`, raw `Expr`,
   proof-step identifiers, or evidence headings.
