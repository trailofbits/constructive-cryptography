# Counting and event-mass obligations

Use this reference after a security reduction has produced a concrete mass,
probability, fiber-cardinality, or finite-sum goal. Counting is a downstream
layer, not a proof-family label for the whole security argument.

## Contents

- [Inspect the exact probability law](#inspect-the-exact-probability-law)
- [Finite union bounds](#finite-union-bounds)
- [Schedule scope](#schedule-scope)
- [Choose the least lossy calculation](#choose-the-least-lossy-calculation)
- [Verification](#verification)

## Inspect the exact probability law

Before decomposing an event, write down:

- the carrier and distribution;
- its nonnegativity or probability proof;
- the event and its decidability requirements;
- which variables are fixed and which are universally quantified; and
- the finite bound required by the calling security theorem.

Do not assume every counting leaf is a probability of a bad event. It may be a
raw `Dist.mass`, a likelihood-ratio defect, a disagreement mass under a joint
law, or an exact cardinality identity.

## Finite union bounds

The current finite-index probability union theorem is:

```lean
theorem probBad_iUnion_le {A ι : Type*} [Fintype A] [Fintype ι]
    {D : Dist A} (hD : D.NonNeg) (B : A → Prop) (P : ι → A → Prop)
    [∀ p, DecidablePred (P p)]
    (hB : ∀ a, B a → ∃ p, P p a) :
    probBad D B ≤ ∑ p, D.evalPred (P p)
```

A correct application supplies the nonnegativity proof first:

```lean
refine le_trans
  (RandomSystems.probBad_iUnion_le hD Bad pieces ?cover)
  ?sum_bound
```

For a finite `Finset` of indices, inspect
`RandomSystems.CR18.mass_biUnion_le` in
`RandomSystems/SwitchingLemma.lean`. Its current signature requires a finite,
nonempty carrier and `X.NonNeg`:

```lean
theorem mass_biUnion_le {A ι : Type*} [Fintype A] [Nonempty A]
    (X : Dist A) (hX : X.NonNeg) (s : Finset ι)
    (E : ι → A → Prop) :
    X.mass (fun a => ∃ i ∈ s, E i a)
      ≤ ∑ i ∈ s, X.mass (E i)
```

The event cover and the individual mass estimates are separate obligations.
Choose descriptors that make both statements true and tractable. A cover can
overlap; the resulting sum may be loose.

`probBad_le_of_ratio` is a different tool. It derives a bad-mass bound from a
pointwise one-sided ratio when both laws are normalized/nonnegative and the
comparison law assigns zero mass to the bad event. Inspect all hypotheses in
`RandomSystems/HTechnique/Derivation.lean` before using it.

## Schedule scope

Read the caller's quantifiers before proving a count.

- The packaged seeded CE endpoint asks for a bound on
  `D.mass (fun a => bad a (blindQueryList w q))` for every blind winner `w`.
  For each `w`, the list is fixed, but the theorem is uniform in `w`.
- The ordinary adaptive H endpoints ask for a bad-mass bound for every
  `QQueryEnvironment` under the ideal transcript law.
- A coupling leaf is governed by the chosen joint law and may retain adaptive
  state.

Do not replace one of these scopes with another without an explicit reduction.
In particular, exact compression of repeated queries is construction-specific.

## Choose the least lossy calculation

Use a union bound only when it matches the intended strength. Alternatives
include:

- exact fiber cardinalities;
- disjoint partitions;
- sequential conditional products;
- pointwise likelihood ratios;
- expectation of a transcript-dependent defect;
- orbit or symmetry counting; and
- direct disagreement mass under an honest coupling.

For standard pair-collision counting, the library contains
`pairCollisionUnionBound_le_birthday`, which bounds its particular
`pairCollisionUnionBound X r` expression by

```text
(1/2) * r^2 / card(X).
```

This theorem does not prove that an arbitrary construction's bad event equals
or is covered by that expression. Supply the construction-specific cover.

When using an exact cardinality argument, keep these layers explicit:

```text
event membership
→ descriptor or fiber statement
→ cardinality identity/inequality
→ mass under the specified law
→ numerical simplification
```

## Verification

- Check every nonnegativity and normalization premise rather than relying on
  a probability-looking notation.
- Use `classical` or decidability instances only where the selected theorem
  needs them.
- Inspect casts between `Nat`, `NNReal`, and `Real`; do not hide a changed
  inequality behind automation.
- Prefer focused algebra tactics after the probabilistic statement is fixed.
- Verify the final security theorem with `#print axioms`, not only the local
  counting lemma.

Rechecked 2026-08-06 in the working tree used by the post-rewrite audit,
`CBCStructureGraph.lean` contains an admitted central mass bound and its
focused source path is not clean. Do not cite it as a completed
beyond-birthday route. This status is snapshot-sensitive: before using it,
consult the current `STATUS.md`, run `lake env lean
RandomSystems/CBCStructureGraph.lean`, and obtain a clean `#print axioms`
receipt after the file elaborates.
