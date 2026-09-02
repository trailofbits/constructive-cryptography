# MPR07 symmetric common-part games

Use this route when the goal is to realize the transcript distance between two
systems exactly as game-winning probability. This is Maurer, Pietrzak, and
Renner, *Indistinguishability Amplification* (CRYPTO 2007), Lemma 5, printed
pp. 140-142. It is not CR18's strict one-sided conditional equivalence.

## Source contract

MPR07 Lemma 5 begins: “For any two `(X,Y)`-systems `S` and `T` there exist
`(X,Y × {0,1})`-random systems `Ŝ` and `T̂` with MBOs such that”:

1. `Ŝ⁻ ≡ S`;
2. `T̂⁻ ≡ T`;
3. `Ŝ† ≡ T̂†`;
4. for every distinguisher `D` and horizon `k`,
   `δₖᴰ(S,T) = νₖᴰ(Ŝ) = νₖᴰ(T̂)`.

Definitions 9-12 on printed pp. 138-140 define MBO erasure, masking,
restricted equivalence, winning probability, and transcript distance. Preserve
the quantifier order: one pair `Ŝ,T̂` works for every `D` and `k`.

Call this **symmetric common-part game equivalence**. “MPR07 CE” may be useful
shorthand in conversation, but it must not be presented as completeness of
the one-game/ordinary-target relation `game |≡ target`.

## Mathematical construction

For each query-answer history, define the cumulative common mass

```text
m(xⁱ,yⁱ) = min(pS(yⁱ | xⁱ), pT(yⁱ | xⁱ)).
```

The no-win branches of both enhanced systems receive exactly this mass. The
remaining source-specific mass is placed on the branch where the MBO has
fired. At the distribution level this is the familiar split

```text
common(x) = min(P(x),Q(x))
leftOnly(x) = P(x) - common(x)
rightOnly(x) = Q(x) - common(x).
```

The interactive construction is not a pointwise deletion on a fixed
representative. It recursively chooses allocations `r(xⁱ,yⁱ)` satisfying

```text
m(xⁱ,yⁱ) ≤ r(xⁱ,yⁱ) ≤ pS(yⁱ | xⁱ)
Σ_yᵢ r(xⁱ,yⁱ) = m(xⁱ⁻¹,yⁱ⁻¹),
```

and symmetrically for `T`. Existence follows from

```text
Σ_yᵢ m(xⁱ,yⁱ)
  ≤ m(xⁱ⁻¹,yⁱ⁻¹)
  ≤ Σ_yᵢ pS(yⁱ | xⁱ).
```

These allocations define normalized conditional kernels, including the
post-win branch. Induction on the round proves the cumulative common-mass
identity and monotonicity of the MBO.

Finally, the shared no-win transcript mass is the pointwise minimum of the two
transcript laws. Therefore

```text
δ(P,Q) = 1 - Σ_t min(P(t),Q(t))
```

is exactly the mass on which either MBO has fired, yielding both winning
equalities.

## Current Lean surface

The present library already provides useful forward components:

- `PDG.underlying` erases a game's condition;
- `PDG.EquivalentAsGames` compares pre-winning behavior;
- `PDG.equivalentAsGames_of_massYAfalse_eq` builds that relation from equal
  cumulative pre-winning masses; and
- `RandomSystems.statDist_trLaw_le_winProb_of_equivalentAsGames` bounds transcript
  distance by winning probability for equivalent games.

There is currently no production declaration constructing the MPR07 pair for
arbitrary `S,T`, and no theorem giving the exact two winning equalities. Do not
replace either missing declaration with `PDG.enhance_with_MBO`: that operation
copies a condition onto a target and supports CR18 strict CE; it does not
perform the recursive common-part split.

## Formalization DAG

Keep the intended exact theorem as the root and add only its consumers:

```text
MPR07 exact common-part games
├── cumulative common mass m = min(system factors)
├── finite-support allocation between lower and upper bounds
├── kernel-to-PDG realization
│   ├── nonnegativity and normalization
│   └── initially-false monotone condition
├── erased leftHat/rightHat recover S/T
├── pre-winning masses of leftHat/rightHat equal m
└── per-winner transcript calculation
    ├── equivalentAsGames leftHat rightHat
    └── statDist = winProb leftHat = winProb rightHat
```

The allocation and kernel-realization seams are the likely upstream owners.
Do not add global `Fintype Y` merely to enumerate answers: use the finite
support actually supplied by the random-system model unless the theorem's
mathematical object is genuinely finite.

The paper's horizon `k` and the current stopping-winner interface are not
definitionally identical. State the bounded-observer bridge explicitly rather
than silently dropping `k`. Likewise, choose the current library's justified
equality or observational equivalence when translating MBO erasure; raw
carrier equality is not automatic.

## Jost boundary

Jost's thesis, printed p. 33, says: “We model events as a generalization of
monotone binary outputs (MBO).” This treats an MPR07 MBO as the single-event
special case of a richer global event history. The richer structure is not
required by Lemma 5 and does not derive its common-part theorem. Keep the
fixed-interface RS construction Boolean; add an event-aware adapter only for a
downstream CC consumer that genuinely needs Jost's event algebra.

## Boundary checks

- This route constructs both enhanced systems; strict CE constructs or assumes
  one game against one ordinary target.
- Exactness comes from the common-part calculation, not from the generic
  forward game-equivalence inequality.
- The construction is not an honest coupling and does not identify paired
  executions.
- It is not merely the choice of a better bad predicate on the original
  representative: probability mass is redistributed between no-win and won
  branches.
- Until the constructor, bounded-observer bridge, focused build, and axiom
  receipt exist, report this as a source-backed formalization route rather than
  a completed Lean technique.
