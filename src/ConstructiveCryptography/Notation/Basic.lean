import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction

/-!
# Abstract CC notation

Scoped notation, in the `SystemAlgebra` scope, for any cryptographic algebra:

```text
Δ R S       distance R S                         selected compatible pseudo-metric
R ∥ S       parallel R S                         selected ordered parallel operation
R ≃[ε] S    ∀ d ∈ admissible A, advantage(d, R, S) ≤ ε(d)    decision advantage
```

The notation reads the instances in scope and selects none: the metric, the parallel
operation, the decision evaluation and the admitted tests are all fixed by the statement
using it. `Δ` and `∥` are syntaxes with their own generic elaborators, `elabCCDistance` and
`elabCCParallel`, so that a concrete layer can add carrier hints; every handler produces the
same `distance R S` or `parallel R S` of the selected instance. Unexpanders print both back in
this notation. This module imports only the abstract layer; `ConstructiveCryptography.Notation`
adds the typed-system handlers, the interface notation and the normalization rules.
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

end SystemAlgebra
