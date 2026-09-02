import Verbose

open scoped CryptoVerbose

example (P : Prop) (proof : P) : True := by
  Fact invalid: exact proof
