import Verbose

open scoped CryptoVerbose

example (a b : Nat) (equation : b = a) : a = b := by
  Replacing a by b using equation yields b = b
