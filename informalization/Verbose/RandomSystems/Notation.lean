import RandomSystems.Technique.Switching

/-!
# Random Systems mathematical notation

These are standalone scoped terms.  Each expands to one exact Random Systems
constructor; none is recovered from a local declaration name or from theorem-
specific syntax.
-/

namespace CryptoVerbose

open Lean Parser Term

scoped syntax:max (name := uniformRandomFunctionNotation)
  "URF(" term "," term ")" : term

scoped syntax:max (name := homogeneousUniformRandomFunctionNotation)
  "URF(" term ")" : term

scoped syntax:max (name := uniformRandomPermutationNotation)
  "URP(" term ")" : term

/-- Query restriction binds less tightly than the standard RS atoms. Nested
restrictions therefore require parentheses. -/
scoped syntax:65 (name := queryRestrictionNotation)
  "[" term "]" term:66 : term

scoped syntax:max (name := fullyDefinedAdvantageNotation)
  "Adv⊥(" term "," term ")" : term

scoped syntax:max (name := forgetGameNotation)
  "forget(" term ")" : term

scoped syntax:max (name := blindWinningENNRealNotation)
  "νᴺᴬ[" term "]" : term

scoped macro_rules
  | `(term| URF($inputAlphabet, $outputAlphabet)) =>
      `(term| RandomSystems.PDS.urf $inputAlphabet $outputAlphabet)
  | `(term| URF($alphabet)) =>
      `(term| RandomSystems.PDS.urf $alphabet $alphabet)
  | `(term| URP($alphabet)) =>
      `(term| RandomSystems.PDS.urp $alphabet)
  | `(term| [$budget] $system) =>
      `(term| RandomSystems.Switching.limit $budget $system)
  | `(term| Adv⊥($left, $right)) =>
      `(term| RandomSystems.PDS.advFullyDefined $left $right)
  | `(term| forget($game)) => `(term| RandomSystems.PDG.forget $game)
  | `(term| νᴺᴬ[$game]) =>
      `(term| ENNReal.ofReal (RandomSystems.PDG.blindSupWinProb $game))

end CryptoVerbose
