import Informalization.Semantics.CanonicalRandomSystems
import Informalization.Semantics.RandomSystems
import RandomSystems.Converter.CommonDomain

/-!
# Live common-domain data-processing seam

This fixture checks the current generic carrier boundary independently of the
migration-blocked CBC application. It prevents the semantic catalog from
retaining the removed ambient-advantage bridge by name or by operand shape.
-/

open Lean Meta Elab Command
open Informalization.Semantics
open Informalization.Semantics.Registry
open RandomSystems

namespace VerboseTests.CommonDomain

run_cmd liftTermElabM do
  let environment ← getEnv
  let declaration :=
    ``RandomSystems.CommonDomain.ProbabilityRandomSystem.edist_apply_le
  let some entry := Informalization.Semantics.RandomSystems.catalog.find?
      (·.declaration == declaration)
    | throwError "the live common-domain data-processing theorem is not registered"
  unless entry.role == .proofRule .commonDomainDataProcessing do
    throwError "the live common-domain theorem has the wrong semantic role"
  unless entry.arguments.filterMap (·.slot?) ==
      #[`converter, `leftSystem, `rightSystem, `result] do
    throwError "the live common-domain theorem has stale semantic operands"
  let expectedBindings := #[
    (`converter, .binder `converter, .converter),
    (`leftSystem, .binder `left, .sourceSystem),
    (`rightSystem, .binder `right, .targetSystem),
    (`result, .result, .conclusion)]
  unless entry.arguments.map (fun binding =>
      (binding.slot?.getD .anonymous, binding.selector, binding.role)) ==
      expectedBindings do
    throwError "the common-domain semantic roles or selectors drifted"
  let some canonicalRule :=
      Informalization.Semantics.Canonical.RandomSystemsProfile.profile.rules.find?
        (·.declaration == declaration)
    | throwError "the canonical common-domain rule is absent"
  unless canonicalRule.operands.map (fun operand => (operand.slot, operand.selector)) == #[
      (`converter, .binder `converter),
      (`leftSystem, .binder `left),
      (`rightSystem, .binder `right)] do
    throwError "the registry and canonical common-domain schemas disagree"
  let issues := validateCatalog environment #[entry]
  unless issues.isEmpty do
    throwError "the common-domain catalog entry does not match the live theorem: {repr issues}"

universe u v

example {X U : Type u} {Y V : Type v}
    (converter : CommonDomain.DDC U V X Y)
    (left right : CommonDomain.ProbabilityRandomSystem X Y) :
    edist (CommonDomain.ProbabilityRandomSystem.apply converter left)
        (CommonDomain.ProbabilityRandomSystem.apply converter right) ≤
      edist left right :=
  CommonDomain.ProbabilityRandomSystem.edist_apply_le converter left right

run_cmd liftTermElabM do
  let environment ← getEnv
  let declaration :=
    ``RandomSystems.CommonDomain.ProbabilityRandomSystem.edist_apply_le
  let information ← getConstInfo declaration
  forallTelescope information.type fun arguments conclusion => do
    let some claim ←
        Informalization.Semantics.Canonical.RandomSystemsProfile.decodeClaim?
          conclusion
      | throwError "the live common-domain distance conclusion was not decoded"
    match claim with
    | .distanceBound _ (.converterApplication _ _ _) (.converterApplication _ _ _) _ =>
        pure ()
    | _ => throwError "common-domain converter applications were decoded opaquely"

end VerboseTests.CommonDomain
