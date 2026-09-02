# Direct calculations and lower bounds

Use this route when the transcript laws can be computed exactly or an explicit
environment witnesses a nontrivial distinguishing advantage.

## Direct upper bound

To prove an upper bound on `PDS.advantage`, show the desired transcript-distance
bound for every DDE in its pair-admissible subtype, then close the supremum with
the live order lemmas used by `RandomSystems.Distance`. This is appropriate
when the transcript law has a short exact calculation and no H, CE, or coupling
object improves the proof.

For a named common domain, first choose whether the natural root is
`advantageOnDomain` or `Adv`; use the exact restriction bridges rather than
silently changing observer classes.

## Explicit lower bound

A lower bound needs a concrete admissible deterministic environment:

1. define the DDE and prove compatibility and stopping for both systems;
2. calculate or lower-bound the statistical distance between its two
   transcript laws;
3. insert that value into the supremum defining `PDS.advantage`; and
4. transport to `Adv` only through the common-domain equality theorem.

At the distribution layer,
`Probability.mass_sub_mass_le_statDist` turns an explicit transcript event into
a one-sided statistical-distance lower bound. An exact accepting test can be
handled similarly through the expectation/statistical-distance theorems.

Do not call a guessed attack an RS lower bound until it is a well-typed DDE in
the exact observation family. Finite enumeration may test a conjecture, but it
does not replace a symbolic environment theorem.
