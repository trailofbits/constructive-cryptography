import ConstructiveCryptography.CryptographicAlgebra.Game
import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction

/-!
# Abstract CC notation

Scoped notation, in the `SystemAlgebra` scope, for any instances of the abstract classes:

```text
Δ R S         distance R S                      selected compatible pseudo-metric
R ∥ S         parallel R S                      selected ordered parallel operation
R ≃[ε] S      ∀ d ∈ admissible A,               decision advantage against the
                advantage(d, R, S) ≤ ε(d)         selected admitted tests
𝓡 —[π]→ 𝒮     Constructs π 𝓡 𝒮                  π𝓡 ⊆ 𝒮
𝓡 —[π; ε]→ 𝒮  ConstructsWithin π 𝓡 𝒮 ε          ∀ R ∈ 𝓡, ∃ S ∈ 𝒮, d(πR, S) ≤ ε
G |≡ T        ConditionallyEquivalent G T       selected `DistinctionGames` field
```

The notation reads the instances in scope and selects none: the metric, the parallel
operation, the attachment, the decision evaluation, the admitted tests and conditional
equivalence are all fixed by the statement using it. `Δ` and `∥` are syntaxes with their own
generic elaborators, `elabCCDistance` and `elabCCParallel`, so that a concrete layer can add
carrier hints; every handler produces the same `distance R S` or `parallel R S` of the selected
instance. Unexpanders print both back in this notation.

This module imports only abstract classes, so instance modules such as
`ConstructiveCryptography.Instances.Game` use it without loading the frontend.
`ConstructiveCryptography.Notation`, above the instances and the proof commands, defines no
further notation: it adds the typed carrier hints for `Δ` and `∥` and registers the
normalization rules for interfaces.
-/

namespace SystemAlgebra

/-- Distance in the selected compatible pseudo-metric. -/
scoped syntax (name := ccDistance) "Δ " term:max term:max : term

open Lean Elab Term in
/-- The generic handler: `Δ R S` elaborates to `distance R S`, the carrier and its metric being
inferred from the operands. Later handlers that fail fall back to this one. -/
@[term_elab ccDistance]
def elabCCDistance : TermElab
  | `(Δ $R $S), expectedType? => do
    elabTerm (← `(ConstructiveCryptography.CryptographicAlgebra.distance $R $S)) expectedType?
  | _, _ => throwUnsupportedSyntax

/-- The selected ordered parallel operation, with its explicit interface tensor. -/
scoped syntax:70 (name := ccParallel) term:70 " ∥ " term:71 : term

open Lean Elab Term in
/-- The generic handler: `R ∥ S` elaborates to `parallel R S`, the carrier and its parallel
operation being inferred from the operands. Later handlers that fail fall back to this one. -/
@[term_elab ccParallel]
def elabCCParallel : TermElab
  | `($R ∥ $S), expectedType? => do
    elabTerm (← `(ConstructiveCryptography.CryptographicAlgebra.parallel $R $S)) expectedType?
  | _, _ => throwUnsupportedSyntax

open Lean PrettyPrinter in
/-- Display the selected distance with the same notation used in its statement. -/
@[app_unexpander ConstructiveCryptography.CryptographicAlgebra.distance]
def unexpandCCDistance : Unexpander
  | `($_ $R $S) => `(Δ $R $S)
  | _ => throw ()

open Lean PrettyPrinter in
/-- Display the selected parallel operation without exposing its class projection. -/
@[app_unexpander ConstructiveCryptography.CryptographicAlgebra.parallel]
def unexpandCCParallel : Unexpander
  | `($_ $R $S) => `($R ∥ $S)
  | _ => throw ()

/-- Substitution within `ε`: every admitted `d` has decision advantage at most `ε(d)`, for the
`Distinguishers` and `AdmissibleDistinguishers` instances in scope. -/
scoped notation:50 R:51 " ≃[" error "] " S:51 =>
  ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin
    (ConstructiveCryptography.Distinguishers.distinguisherAdvantage
      ConstructiveCryptography.AdmissibleDistinguishers.admissible) error R S

/-- Exact construction `𝓡 —[π]→ 𝒮`: attaching the converter `π` maps every resource of the
specification `𝓡` into `𝒮`, `π𝓡 ⊆ 𝒮` (MR16 §§2–4). -/
scoped notation:50 source " —[" converter "]→ " target:51 =>
  ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
    converter source target

/-- Construction within `ε`, `𝓡 —[π; ε]→ 𝒮`: every `R ∈ 𝓡` has some `S ∈ 𝒮` with
`d(πR, S) ≤ ε` in the selected metric (MR16 §§2–4). -/
scoped notation:50 source " —[" converter "; " error "]→ " target:51 =>
  ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
    converter source target error

/-- Conditional equivalence `G |≡ T` of a game `G` to a resource `T` (CR18, Definition 4.19):
the `ConditionallyEquivalent` field of the selected `DistinctionGames` instance. -/
scoped notation:50 G:51 " |≡ " T:51 =>
  ConstructiveCryptography.DistinctionGames.ConditionallyEquivalent G T

end SystemAlgebra
