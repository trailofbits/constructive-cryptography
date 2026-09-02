# Strict conditional equivalence

Use this route when a probabilistic discrete game `game : PDG X Y`, conditioned
on not winning, has the same visible behavior as a target `target : PDS X Y`.
This is the current fixed-interface CR18 certificate, not a generic name for
conditioning on a bad event.

## Live certificate and endpoint

`RandomSystems.Technique.ConditionalEquivalence` defines:

```lean
structure ConditionallyEquivalent (game : PDG X Y) (target : PDS X Y) : Prop where
  initiallyFalse : game.InitiallyFalse
  mass_eq : ∀ transcript, transcript ≠ [] →
    massAfalse game (transcript.map Prod.fst) ≠ 0 →
    massDom target (transcript.map Prod.fst) ≠ 0 →
      massYAfalse game transcript *
          massDom target (transcript.map Prod.fst) =
        PDS.transcriptSystemFactor target transcript *
          massAfalse game (transcript.map Prod.fst)
```

The notation is `game |≡ target`. The main numerical endpoint in
`RandomSystems.Technique.ConditionalEquivalence.Advantage` is:

```lean
PDS.advantage_le_of_conditionallyEquivalent_of_supWinProb_blind_le
```

It concludes `Adv(game.underlying, target) ≤ epsilon` from probability laws,
one common domain, `game |≡ target`, and
`Γ(PDG.blind game) ≤ epsilon`.

The proof tactic is deliberately narrow:

```lean
rs_conditional_equivalence domain using equivalent, winning
```

It discharges registered probability and domain side conditions but never
invents the domain, CE witness, game, or winning bound.

## Principal obligations

```text
game and target
├── probability laws
├── one explicit common domain
├── initially-false game condition
├── conditioned transcript-factor identity
└── supremum winning bound for the blind game
```

The game's monotone condition is already part of `System.MC`; do not add a
second unrelated monotonicity predicate. The numerical rate comes entirely
from the blind winning bound, not from conditional equivalence itself.

## Live module map

- `RandomSystems/Technique/ConditionalEquivalence.lean`: certificate,
  pre-winning factors, game equivalence, and MBO enhancement.
- `.../InitiallyFalse.lean`: the initial-false property.
- `.../Indistinguishability.lean`: transcript-distance bounds from equal
  pre-winning masses and `EquivalentAsGames`.
- `.../Absorption.lean`: absorbed blind winners and winning comparison.
- `.../Advantage.lean`: the ordinary RS advantage endpoints.
- `.../Blind.lean`: generic blind-game bounds for filtered function systems.
- `.../Filter.lean`: domain-filter preservation.
- `.../FunctionEvaluator.lean`: function-evaluator CE leaves.
- `RandomSystems/Tactics/ProofAutomation.lean`: the explicit CE tactic.

## Boundary checks

- `EquivalentAsGames` is a pre-winning game relation, not `game |≡ target`.
- An H bad cell is not an MBO and does not supply the CE identity.
- `PDG.supWinProb` is not abstract representative-level winnability.
- Changing the game condition or target requires a new CE proof and winning
  bound.
- Check the exact common-domain and probability hypotheses; do not recover an
  old seeded `PFunPDS` wrapper by compatibility aliases.
