import Verbose

namespace CryptoLanguage.Verbose.Tests.Grammar

universe u v w

variable {I : Type u} {Gamma : I → Type v} {Phi : Type w}
variable [∀ i, Monoid (Gamma i)] [MulAction (∀ i, Gamma i) Phi]

open scoped CryptoVerbose

/- Compound references remain ordinary Lean terms, explicitly parenthesized
at a prose boundary. -/
omit [MulAction (∀ i, Gamma i) Phi] in
example (P : Prop) (proof : P) : P := by
  exact id proof

/- Reader notes have no effect on proof checking. -/
omit [MulAction (∀ i, Gamma i) Phi] in
example (P : Prop) (proof : P) : P ∧ P := by
  constructor
  · exact proof
  · exact proof

/- Assistance does not invent an ideal system, simulator, restriction, or
other explicit mathematical operand. -/
/-- info: Dry-elaborated suggestions (nothing was inserted):

exact _example -/
#guard_msgs (substring := true) in
set_option linter.unusedTactic false in
example : True := by
  crypto_suggest
  trivial

/- Hypothesis help is based on checked definitional equality and shows a
sentence which the frontend has dry-elaborated successfully. -/
/-- info: proof exactly proves the current goal.

Checked proof step: exact proof -/
#guard_msgs (substring := true) in
example (P : Prop) (proof : P) : P := by
  crypto_help proof
  exact proof

/-- info: validated -/
#guard_msgs (substring := true) in
#crypto_verbose_validate

end CryptoLanguage.Verbose.Tests.Grammar
