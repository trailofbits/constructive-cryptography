# Games, blindness, and winning probability

Use this route when the certificate is a probabilistic discrete game rather
than only a pair of ordinary systems.

## Live game objects

`RandomSystems.Game` defines:

- `System.MC`, a monotone Boolean condition on query histories;
- `System.DDG`, a deterministic system paired with that condition;
- `PDG`, a distribution over deterministic games;
- `System.Winner`, an ordinary deterministic environment;
- `PDG.underlying`, which forgets the condition; and
- `PDG.gameTrLaw` for the observed transcript and final condition.

`RandomSystems.Game.Winning` defines `PDG.winProb`, `PDG.supWinProb`, and the
notation `ν(game)`. Use `winProb_le_supWinProb` for one winner and
`supWinProb_le` to prove a common upper bound for all winners.

`RandomSystems.Game.Blind` defines `System.DDE.IsBlind`, the blocked-answer
game `PDG.blind`, and the blind-winner comparison.

## Relations are not interchangeable

- Ordinary system equality concerns `PDG.underlying` after forgetting the
  condition.
- `EquivalentAsGames` concerns equal pre-winning behavior.
- `game |≡ target` is strict conditional equivalence between one PDG and one
  PDS.
- `ν(game)` is a supremum winning probability, not an abstract winnability
  functional and not a distance without a theorem connecting it.

Conditional equivalence uses game enhancement, game equivalence, absorption,
and blindness internally. Read [conditional-equivalence.md](conditional-equivalence.md)
for that complete route instead of applying these pieces by analogy.

MPR07's converse direction constructs two new games whose common pre-winning
part realizes the exact transcript distance. Read
[mpr07-symmetric-common-part.md](mpr07-symmetric-common-part.md); the current
generic game API does not itself construct that pair.
