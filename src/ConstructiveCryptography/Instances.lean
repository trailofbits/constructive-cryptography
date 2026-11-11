module

public import ConstructiveCryptography.Instances.Category
public import ConstructiveCryptography.Instances.Monoidal
public import ConstructiveCryptography.Instances.Algebra
public import ConstructiveCryptography.Instances.FiniteParallel
public import ConstructiveCryptography.Instances.Game
public import ConstructiveCryptography.Instances.Substitution

/-!
# Interface instances of the abstract theory

The abstract classes instantiated on interfaces. The concrete objects and their laws live in
`RandomSystems`; these modules select those objects as fields and discharge the abstract axioms
with their laws, defining no new carrier.

* `Category`, `Monoidal`: typed converters with their serial and ordered parallel laws.
* `Algebra`: attachment, parallel composition, the canonical transcript metric over all
  compatible stopping distinguishers, decision evaluation and absorption of typed
  distinguishers, and domination of their advantage by that metric. No admitted test set is
  installed; a statement selects one locally.
* `FiniteParallel`: finite interface, converter and resource families, with explicit reindexing,
  head/tail and empty-unit isomorphisms satisfying the abstract coherence contract.
* `Game`: real-valued winners and the joint solver views of typed games, with their converter
  actions and the conditional-equivalence distance bounds.
* `Substitution`: a single-substitution relaxation is parallel-compatible, given explicit
  closure of its transformations under both ordered contexts.

The instances import `RandomSystems` and the abstract classes; `Game` adds only the abstract
`Notation.Basic`. The full `Notation`, the proof commands and the DSL are above this layer.
The field-by-field correspondence is the interface instance table of `THEORY.md`.
-/
