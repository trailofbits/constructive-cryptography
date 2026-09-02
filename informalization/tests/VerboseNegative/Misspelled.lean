import Verbose

open scoped CryptoVerbose

/- This file must fail: misspelled fixed words do not select a proof rule. -/
example (P : Prop) (proof : P) : P := by
  Usign proof, we conclude the goal
