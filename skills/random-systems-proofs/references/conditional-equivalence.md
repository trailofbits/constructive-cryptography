# Strict conditional equivalence

Use this reference only for the one-sided conditional-equivalence relation of
CR18 and its Lean implementation. Do not use “conditional equivalence” as a
name for every proof involving conditioning or a bad event.

Strict CE is one certificate for bounding the already specified distance
between a source system and a target system. The other techniques discussed
below may address the same comparison or appear in the same proof; what must
remain separate are their witness objects, hypotheses, and bridge theorems.

## Contents

- [The source notion](#the-source-notion)
- [Other certificates for the same comparison](#other-certificates-for-the-same-comparison)
- [What determines a bound](#what-determines-a-bound)
- [The packaged seeded endpoint](#the-packaged-seeded-endpoint)
- [Blindness and fixed query lists](#blindness-and-fixed-query-lists)
- [Proof obligations](#proof-obligations)
- [Current library map](#current-library-map)
- [Review checklist](#review-checklist)

## The source notion

CR18 Definition 4.19 relates:

1. one system enhanced with a monotone binary output (an MBO); and
2. one ordinary target system.

The relation equates the enhanced source's cumulative response law conditioned
on the monitor still being false with the target's ordinary cumulative
response law. CR18 Theorem 4.17 then bounds distinguishing advantage by a
blind winning probability for that monitored source, subject to its standing
game assumptions.

Lean represents this one-sided relation by:

```lean
def CondEquiv (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y) : Prop :=
  ∀ (i : ℕ) (xs : Vector X (i + 1)) (ys : Vector Y (i + 1)),
    massAfalse Shat xs.toList ≠ 0 → massDom T xs.toList ≠ 0 →
      massYAfalse Shat i ys xs * massDom T xs.toList =
        massY T i ys xs * massAfalse Shat xs.toList
```

This cross-multiplied equality avoids division. Read the current declaration in
`RandomSystems/CondEquiv.lean` before using it; its nonzero guards and
normalizers are part of the proposition.

The CE hypothesis is an equality, not an approximate inequality. Approximation
enters when the blind winning probability is bounded.

## Other certificates for the same comparison

Keep the following certificate types distinct without treating them as
unrelated security objectives. They may analyze the same system distance, but
one certificate cannot be substituted for another without a connecting
theorem.

### Symmetric monitored games

Maurer--Pietrzak--Renner 2007, Lemma 5 constructs an enhanced version of each
of two systems. Their masked or pre-winning parts are restricted-equivalent,
and for each distinguisher and horizon the two winning probabilities equal the
corresponding transcript distance. This is a symmetric exact construction. It
is not a completeness theorem for the one-enhanced-source/ordinary-target
relation above.

### Equivalent representatives and couplings

Lanzenberger's transcript-law equivalence classes and attainment theorems
select representatives in a finite common-domain setting. A coupling there is
an honest nonnegative joint distribution with the required marginals. These
are separate operations from proving `Shat |≡ T` for a chosen source and
target, although a representative or coupling step may occur elsewhere in the
same distance proof.

### H bad predicates and winnability

An H-technique bad predicate is part of a transcript-law comparison. A
winnability theorem concerns the success probability of a game. Neither term
should be substituted for strict CE without a theorem connecting the chosen
objects. With such a theorem, these may be alternative or chained
certificates for the same underlying system comparison.

## What determines a bound

Strict CE has no built-in birthday, cubic, or other asymptotic rate. A concrete
CE proof has two distinct mathematical parts:

1. prove the conditioned-law identity for the exact monitor and simulator;
2. bound the blind winning probability of that monitor.

For fixed source and target, the monitor is a design variable only among
conditions for which all required properties are proved. Replacing a monitor
requires fresh proofs of at least:

- prefix monotonicity;
- the strict CE identity; and
- the winning-probability bound.

A smaller event does not automatically preserve CE. A monotone closure makes
an event monotone but can change both the CE and probability problems.

Changing the ideal-world simulator is another valid design move. It changes
the target of the CE statement and therefore requires a separate proof that
the simulator realizes the intended ideal resource. Do not call this a
representative change unless an explicit transcript-law equivalence theorem is
also supplied.

## The packaged seeded endpoint

For a deterministic seeded construction `F`, a seed law `D`, and a monitored
predicate `bad`, inspect the current declaration:

```lean
theorem maxAdvantage_filterQueries_seededConditionCGame_le
    {A I O : Type*} [Nonempty I]
    (D : Dist A) (F : A → I → O) (bad : A → List I → Prop)
    [∀ a l, Decidable (bad a l)]
    (hmono : ∀ a, ∀ {l₁ l₂ : List I}, l₁ <+: l₂ → bad a l₁ → bad a l₂)
    (q : ℕ) (T : PFunPDS I O) (ε : NNReal)
    (hCE : seededConditionCGame D F bad |≡ T)
    (hD : D.isProbDist) (hT : T.isProbDist)
    (hTtot : CondEquiv.TotalOnNonempty T)
    (hleaf : ∀ w : PFunDDS.Winner I O, IsBlind w →
      D.mass (fun a => bad a (blindQueryList w q)) ≤ ε) :
    Δ(⌈q⌉ PFunPDS.ignoreMBO (seededConditionCGame D F bad), ⌈q⌉ T)
      ≤ (ε : ℝ)
```

Search by declaration name rather than relying on a line number. The theorem
currently lives in `RandomSystems/SwitchingLemma.lean`.

Use this wrapper only when its seeded deterministic model matches the
construction. For a monitor depending on generated history or state, inspect
the history-aware endpoints in `RandomSystems/HistoryConditionC.lean`. If no
packaged wrapper matches, inspect the generic Theorem 4.17 bridge in
`RandomSystems/GameOf.lean`; do not silently force a different model into the
seeded interface.

## Blindness and fixed query lists

The blind-game reduction absorbs the original adaptive distinguisher together
with the target-side response process into a winner that is blind to the live
game's responses. Consequently, the packaged leaf is uniform over every blind
winner `w`, and each such winner supplies a fixed list
`blindQueryList w q` of length at most `q`.

This does not mean there is one universal schedule independent of `w`, and it
does not leave an “adaptive blind winner.” State a counting lemma uniformly in
the list, or prove it for arbitrary `w` after introducing the blindness
hypothesis.

## Proof obligations

A typical application should name, rather than hide, these obligations:

```text
monitor definition
├── decidability
├── prefix monotonicity
├── strip/ignore-MBO identity for the construction
├── probability and totality hypotheses
├── strict conditioned-law equality
└── uniform blind-list seed-mass bound
```

The exact list is determined by the selected theorem signature. Monotonicity
and totality can be mathematically substantive; do not label them routine
before inspecting the construction.

Search for a generic or instance-specific `ignoreMBO` theorem before proving a
strip identity. The seeded wrapper and several existing games provide such
lemmas, but a new construction may require its own proof.

## Current library map

- `RandomSystems/CondEquiv.lean`: `CondEquiv`, normalizer lemmas, and filter
  preservation results.
- `RandomSystems/GameOf.lean`: `gameOf` and generic CR18 Theorem 4.17 bridges.
- `RandomSystems/BlindConverter.lean`: blindness and blind winning probability.
- `RandomSystems/BlindAbsorption.lean`: absorption of the adaptive
  distinguisher into the blind game.
- `RandomSystems/SwitchingLemma.lean`: seeded monitored games and the packaged
  endpoint above.
- `RandomSystems/HistoryConditionC.lean`: history-aware monitored-game
  wrappers.
- `RandomSystems/CBCMAC.lean`: a completed construction-specific CE
  application in the current tree.

For the optional CBC structure-graph counting route, see
[counting.md](counting.md) and recheck its current build and axiom status.

## Review checklist

- Is the relation one enhanced source versus one ordinary target?
- Is the monitor prefix-monotone?
- Does the exact chosen monitor occur in both the CE and probability proofs?
- Does the simulator implement the intended ideal resource?
- Are probability, totality, normalization, and decidability hypotheses
  visible?
- Is the blind-list bound uniform in every blind winner?
- Does the claimed numerical rate come from a proved probability lemma?
- Does `#print axioms` show no unintended admission in the final theorem?
